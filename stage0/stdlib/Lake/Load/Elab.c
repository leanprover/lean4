// Lean compiler output
// Module: Lake.Load.Elab
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
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__19;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__40;
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t, lean_object*);
lean_object* lean_read_module_data(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_unlock(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lake_dirExt;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__6;
static lean_object* l_Lake_instHashableImport__lake___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonHash___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__1;
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lake_importModulesUsingCache___spec__5(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Elab___hyg_123____spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqImport__lake;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__49;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedEnvExtensionState;
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lake_importModulesUsingCache___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__1;
lean_object* l_Lean_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__3;
static lean_object* l_Lake_importConfigFile___closed__10;
lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__11;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__39;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkExtNameMap(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonHash___closed__3;
static lean_object* l_Lake_importConfigFile___closed__9;
lean_object* l___private_Init_GetElem_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lake_instToJsonConfigTrace___closed__1;
static lean_object* l_Lake_configModuleName___closed__2;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__4;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_elabConfigFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__11;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__12;
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__9;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__14;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_loop___at_Lake_elabConfigFile___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__6;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(lean_object*);
lean_object* l_Lean_Elab_headerToImports(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__22;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__29;
LEAN_EXPORT uint64_t l___private_Lake_Load_Elab_0__Lake_hashImport____x40_Lake_Load_Elab___hyg_82_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__17;
extern lean_object* l_Lake_optsExt;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Elab___hyg_123____spec__1___boxed(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__19;
lean_object* l_Lean_PersistentArray_toList___rarg(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__21;
static lean_object* l_Lake_importConfigFileCore___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__15;
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__12;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__10;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__24;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lake_importModulesUsingCache___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__51;
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_beqImport____x40_Lake_Load_Elab___hyg_5____boxed(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__13;
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_elabConfigFile___closed__2;
static lean_object* l_Lake_instBEqImport__lake___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__5;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__43;
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__3;
LEAN_EXPORT uint8_t l___private_Lake_Load_Elab_0__Lake_beqImport____x40_Lake_Load_Elab___hyg_5_(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__2___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_Handle_readToEnd_loop(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__21;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__32;
static lean_object* l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__4;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonHash___closed__2;
lean_object* l_System_FilePath_fileName(lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__34;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__23;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__18;
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_addToEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__7___at_Lake_importModulesUsingCache___spec__8(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__5;
static lean_object* l_Lake_processHeader___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__38;
lean_object* lean_environment_set_main_module(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonConfigTrace___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_hashImport____x40_Lake_Load_Elab___hyg_82____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__27;
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__16;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__31;
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonConfigTrace;
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__8;
lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
static lean_object* l_Lake_configModuleName___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__35;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__41;
extern lean_object* l_Lake_defaultLakeDir;
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__15;
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__3;
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__22;
lean_object* lean_environment_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__50;
uint8_t l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonConfigTrace;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12___boxed(lean_object*, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__47;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__25;
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_Load_Elab___hyg_123_(lean_object*);
static lean_object* l_Lake_elabConfigFile___closed__1;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__2(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importModulesUsingCache___lambda__1___closed__1;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__2;
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToJsonHash(uint64_t);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__37;
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__18;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__14;
lean_object* l_Lean_EnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__8;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__45;
lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133_(lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__3;
static lean_object* l_Lake_importConfigFile___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__33;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importEnvCache;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__44;
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lake_importModulesUsingCache___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__20;
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__17;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__7;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__30;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6(lean_object*, size_t, size_t, uint64_t);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__4;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__48;
lean_object* l_Lean_RBNode_foldM___at_Lake_Env_compute_computePkgUrlMap___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__8;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__42;
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lake_importModulesUsingCache___spec__4(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__46;
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__7;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__9;
static lean_object* l_Lake_elabConfigFile___closed__3;
size_t lean_usize_add(size_t, size_t);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__16;
lean_object* l_List_bindTR_go___at___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonHash(lean_object*);
static lean_object* l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore_lakeExts;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__20;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__10;
lean_object* lean_write_module(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonHash___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__2;
LEAN_EXPORT lean_object* l_Lake_instHashableImport__lake;
static lean_object* l_Lake_importConfigFile___closed__2;
lean_object* l_Lean_HashMapImp_find_x3f___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonHash___closed__1;
lean_object* lean_io_prim_handle_truncate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configModuleName;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__26;
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____boxed(lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__36;
lean_object* l_Lean_Json_parse(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_import_modules(lean_object*, lean_object*, uint32_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lake_importModulesUsingCache___spec__9(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__11;
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__6;
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__5;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__28;
static lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__13;
static lean_object* l_Lake_importConfigFile___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Elab_0__Lake_beqImport____x40_Lake_Load_Elab___hyg_5_(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_beqImport____x40_Lake_Load_Elab___hyg_5____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Load_Elab_0__Lake_beqImport____x40_Lake_Load_Elab___hyg_5_(x_1, x_2);
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
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Elab_0__Lake_beqImport____x40_Lake_Load_Elab___hyg_5____boxed), 2, 0);
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
LEAN_EXPORT uint64_t l___private_Lake_Load_Elab_0__Lake_hashImport____x40_Lake_Load_Elab___hyg_82_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_hashImport____x40_Lake_Load_Elab___hyg_82____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Elab_0__Lake_hashImport____x40_Lake_Load_Elab___hyg_82_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instHashableImport__lake___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Elab_0__Lake_hashImport____x40_Lake_Load_Elab___hyg_82____boxed), 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Elab___hyg_123____spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_Load_Elab___hyg_123_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Elab___hyg_123____spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lake_initFn____x40_Lake_Load_Elab___hyg_123____spec__1(x_1);
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
x_12 = l___private_Lake_Load_Elab_0__Lake_beqImport____x40_Lake_Load_Elab___hyg_5_(x_10, x_11);
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
x_7 = l___private_Lake_Load_Elab_0__Lake_hashImport____x40_Lake_Load_Elab___hyg_82_(x_6);
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
x_12 = l___private_Lake_Load_Elab_0__Lake_beqImport____x40_Lake_Load_Elab___hyg_5_(x_10, x_11);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
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
x_24 = 7;
x_25 = lean_array_get_size(x_2);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_lt(x_26, x_25);
if (x_27 == 0)
{
lean_dec(x_25);
x_8 = x_24;
goto block_23;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_25, x_25);
if (x_28 == 0)
{
lean_dec(x_25);
x_8 = x_24;
goto block_23;
}
else
{
size_t x_29; size_t x_30; uint64_t x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__6(x_2, x_29, x_30, x_24);
x_8 = x_31;
goto block_23;
}
}
block_23:
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_7);
x_20 = l_Lean_AssocList_replace___at_Lake_importModulesUsingCache___spec__9(x_2, x_3, x_10);
x_21 = lean_array_uset(x_5, x_9, x_20);
if (lean_is_scalar(x_6)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_6;
}
lean_ctor_set(x_22, 0, x_4);
lean_ctor_set(x_22, 1, x_21);
return x_22;
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
x_12 = l___private_Lake_Load_Elab_0__Lake_beqImport____x40_Lake_Load_Elab___hyg_5_(x_10, x_11);
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
lean_inc(x_3);
lean_dec(x_1);
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
lean_dec(x_3);
x_11 = l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(x_2, x_10);
lean_dec(x_10);
lean_dec(x_2);
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
lean_dec(x_3);
x_15 = l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(x_2, x_14);
lean_dec(x_14);
lean_dec(x_2);
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
lean_dec(x_3);
x_21 = l_Lean_AssocList_find_x3f___at_Lake_importModulesUsingCache___spec__12(x_2, x_20);
lean_dec(x_20);
lean_dec(x_2);
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
lean_inc(x_1);
x_10 = l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11(x_8, x_1);
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
lean_inc(x_1);
x_16 = l_Lean_HashMapImp_find_x3f___at_Lake_importModulesUsingCache___spec__11(x_14, x_1);
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
x_19 = 0;
x_20 = l_Lean_Syntax_getPos_x3f(x_1, x_19);
x_21 = lean_ctor_get(x_3, 1);
x_22 = lean_box(0);
x_23 = lean_io_error_to_string(x_16);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
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
lean_inc(x_21);
x_34 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_22);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_25);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_34, sizeof(void*)*5 + 1, x_32);
x_35 = l_Lean_PersistentArray_push___rarg(x_4, x_34);
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
lean_inc(x_21);
x_43 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_22);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_25);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_41);
x_44 = l_Lean_PersistentArray_push___rarg(x_4, x_43);
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
lean_inc(x_21);
x_57 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_22);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set(x_57, 4, x_25);
lean_ctor_set_uint8(x_57, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_57, sizeof(void*)*5 + 1, x_55);
x_58 = l_Lean_PersistentArray_push___rarg(x_4, x_57);
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
lean_inc(x_21);
x_65 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_65, 0, x_21);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_22);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_65, 4, x_25);
lean_ctor_set_uint8(x_65, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_65, sizeof(void*)*5 + 1, x_63);
x_66 = l_Lean_PersistentArray_push___rarg(x_4, x_65);
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
lean_dec(x_20);
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
lean_dec(x_3);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_30; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_30 = lean_ctor_get_uint8(x_7, sizeof(void*)*5 + 1);
switch (x_30) {
case 0:
{
uint8_t x_31; lean_object* x_32; 
x_31 = 0;
x_32 = l_Lean_Message_toString(x_7, x_31, x_4);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = 1;
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_35);
x_37 = lean_array_push(x_3, x_36);
x_38 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_9 = x_39;
x_10 = x_34;
goto block_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_io_error_to_string(x_40);
x_43 = 3;
x_44 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
x_45 = lean_array_get_size(x_3);
x_46 = lean_array_push(x_3, x_44);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_9 = x_47;
x_10 = x_41;
goto block_29;
}
}
case 1:
{
uint8_t x_48; lean_object* x_49; 
x_48 = 0;
x_49 = l_Lean_Message_toString(x_7, x_48, x_4);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = 2;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_push(x_3, x_53);
x_55 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_9 = x_56;
x_10 = x_51;
goto block_29;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_dec(x_49);
x_59 = lean_io_error_to_string(x_57);
x_60 = 3;
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_60);
x_62 = lean_array_get_size(x_3);
x_63 = lean_array_push(x_3, x_61);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_9 = x_64;
x_10 = x_58;
goto block_29;
}
}
default: 
{
uint8_t x_65; lean_object* x_66; 
x_65 = 0;
x_66 = l_Lean_Message_toString(x_7, x_65, x_4);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = 3;
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_69);
x_71 = lean_array_push(x_3, x_70);
x_72 = l_List_forIn_loop___at_Lake_elabConfigFile___spec__1___closed__1;
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_9 = x_73;
x_10 = x_68;
goto block_29;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_66, 1);
lean_inc(x_75);
lean_dec(x_66);
x_76 = lean_io_error_to_string(x_74);
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_array_get_size(x_3);
x_80 = lean_array_push(x_3, x_78);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_9 = x_81;
x_10 = x_75;
goto block_29;
}
}
}
block_29:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_8);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_9, 1);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_1 = x_8;
x_2 = x_21;
x_3 = x_20;
x_4 = x_10;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_10);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_9, 0);
x_26 = lean_ctor_get(x_9, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_9);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
return x_28;
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
lean_object* x_7; lean_object* x_8; lean_object* x_79; lean_object* x_80; lean_object* x_313; 
x_313 = l_IO_FS_readFile(x_4, x_6);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_5);
x_79 = x_316;
x_80 = x_315;
goto block_312;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_317 = lean_ctor_get(x_313, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_313, 1);
lean_inc(x_318);
lean_dec(x_313);
x_319 = lean_io_error_to_string(x_317);
x_320 = 3;
x_321 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set_uint8(x_321, sizeof(void*)*1, x_320);
x_322 = lean_array_get_size(x_5);
x_323 = lean_array_push(x_5, x_321);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_79 = x_324;
x_80 = x_318;
goto block_312;
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
lean_inc(x_13);
x_14 = l_Lean_PersistentArray_toList___rarg(x_13);
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
x_23 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_13);
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
x_33 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_13);
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
x_47 = l_Lean_PersistentArray_anyM___at_Lean_MessageLog_hasErrors___spec__1(x_13);
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
block_312:
{
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_220; 
x_82 = lean_ctor_get(x_79, 0);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_4);
x_84 = l_Lean_Parser_mkInputContext(x_82, x_4);
lean_inc(x_84);
x_220 = l_Lean_Parser_parseHeader(x_84, x_80);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
lean_ctor_set(x_79, 0, x_221);
x_85 = x_79;
x_86 = x_222;
goto block_219;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_223 = lean_ctor_get(x_220, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_220, 1);
lean_inc(x_224);
lean_dec(x_220);
x_225 = lean_io_error_to_string(x_223);
x_226 = 3;
x_227 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set_uint8(x_227, sizeof(void*)*1, x_226);
x_228 = lean_array_get_size(x_83);
x_229 = lean_array_push(x_83, x_227);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 1, x_229);
lean_ctor_set(x_79, 0, x_228);
x_85 = x_79;
x_86 = x_224;
goto block_219;
}
block_219:
{
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
x_89 = !lean_is_exclusive(x_85);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_153; 
x_90 = lean_ctor_get(x_85, 1);
x_91 = lean_ctor_get(x_85, 0);
lean_dec(x_91);
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
lean_dec(x_87);
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_dec(x_88);
lean_inc(x_3);
x_153 = l_Lake_processHeader(x_92, x_3, x_84, x_94, x_86);
lean_dec(x_92);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_ctor_set(x_85, 0, x_154);
x_95 = x_85;
x_96 = x_155;
goto block_152;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_dec(x_153);
x_158 = lean_io_error_to_string(x_156);
x_159 = 3;
x_160 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set_uint8(x_160, sizeof(void*)*1, x_159);
x_161 = lean_array_get_size(x_90);
x_162 = lean_array_push(x_90, x_160);
lean_ctor_set_tag(x_85, 1);
lean_ctor_set(x_85, 1, x_162);
lean_ctor_set(x_85, 0, x_161);
x_95 = x_85;
x_96 = x_157;
goto block_152;
}
block_152:
{
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_ctor_get(x_95, 1);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec(x_98);
x_102 = l_Lake_configModuleName;
x_103 = lean_environment_set_main_module(x_100, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_1);
x_105 = l_Lake_elabConfigFile___closed__2;
x_106 = l_Lean_EnvExtension_setState___rarg(x_105, x_103, x_104);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_2);
x_108 = l_Lake_elabConfigFile___closed__3;
x_109 = l_Lean_EnvExtension_setState___rarg(x_108, x_106, x_107);
x_110 = l_Lean_Elab_Command_mkState(x_109, x_101, x_3);
x_111 = l_Lean_Elab_IO_processCommands(x_84, x_93, x_110, x_96);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
lean_ctor_set(x_95, 0, x_112);
x_7 = x_95;
x_8 = x_113;
goto block_78;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_116 = lean_io_error_to_string(x_114);
x_117 = 3;
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_117);
x_119 = lean_array_get_size(x_99);
x_120 = lean_array_push(x_99, x_118);
lean_ctor_set_tag(x_95, 1);
lean_ctor_set(x_95, 1, x_120);
lean_ctor_set(x_95, 0, x_119);
x_7 = x_95;
x_8 = x_115;
goto block_78;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_121 = lean_ctor_get(x_95, 0);
x_122 = lean_ctor_get(x_95, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_95);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = l_Lake_configModuleName;
x_126 = lean_environment_set_main_module(x_123, x_125);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_1);
x_128 = l_Lake_elabConfigFile___closed__2;
x_129 = l_Lean_EnvExtension_setState___rarg(x_128, x_126, x_127);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_2);
x_131 = l_Lake_elabConfigFile___closed__3;
x_132 = l_Lean_EnvExtension_setState___rarg(x_131, x_129, x_130);
x_133 = l_Lean_Elab_Command_mkState(x_132, x_124, x_3);
x_134 = l_Lean_Elab_IO_processCommands(x_84, x_93, x_133, x_96);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_122);
x_7 = x_137;
x_8 = x_136;
goto block_78;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_134, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_dec(x_134);
x_140 = lean_io_error_to_string(x_138);
x_141 = 3;
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_141);
x_143 = lean_array_get_size(x_122);
x_144 = lean_array_push(x_122, x_142);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_7 = x_145;
x_8 = x_139;
goto block_78;
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_93);
lean_dec(x_84);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_95);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_95);
lean_ctor_set(x_147, 1, x_96);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_95, 0);
x_149 = lean_ctor_get(x_95, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_95);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_96);
return x_151;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_201; 
x_163 = lean_ctor_get(x_85, 1);
lean_inc(x_163);
lean_dec(x_85);
x_164 = lean_ctor_get(x_87, 0);
lean_inc(x_164);
lean_dec(x_87);
x_165 = lean_ctor_get(x_88, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_88, 1);
lean_inc(x_166);
lean_dec(x_88);
lean_inc(x_3);
x_201 = l_Lake_processHeader(x_164, x_3, x_84, x_166, x_86);
lean_dec(x_164);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_163);
x_167 = x_204;
x_168 = x_203;
goto block_200;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_205 = lean_ctor_get(x_201, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
lean_dec(x_201);
x_207 = lean_io_error_to_string(x_205);
x_208 = 3;
x_209 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set_uint8(x_209, sizeof(void*)*1, x_208);
x_210 = lean_array_get_size(x_163);
x_211 = lean_array_push(x_163, x_209);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_167 = x_212;
x_168 = x_206;
goto block_200;
}
block_200:
{
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_171 = x_167;
} else {
 lean_dec_ref(x_167);
 x_171 = lean_box(0);
}
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
lean_dec(x_169);
x_174 = l_Lake_configModuleName;
x_175 = lean_environment_set_main_module(x_172, x_174);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_1);
x_177 = l_Lake_elabConfigFile___closed__2;
x_178 = l_Lean_EnvExtension_setState___rarg(x_177, x_175, x_176);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_2);
x_180 = l_Lake_elabConfigFile___closed__3;
x_181 = l_Lean_EnvExtension_setState___rarg(x_180, x_178, x_179);
x_182 = l_Lean_Elab_Command_mkState(x_181, x_173, x_3);
x_183 = l_Lean_Elab_IO_processCommands(x_84, x_165, x_182, x_168);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
if (lean_is_scalar(x_171)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_171;
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_170);
x_7 = x_186;
x_8 = x_185;
goto block_78;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 1);
lean_inc(x_188);
lean_dec(x_183);
x_189 = lean_io_error_to_string(x_187);
x_190 = 3;
x_191 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*1, x_190);
x_192 = lean_array_get_size(x_170);
x_193 = lean_array_push(x_170, x_191);
if (lean_is_scalar(x_171)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_171;
 lean_ctor_set_tag(x_194, 1);
}
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_7 = x_194;
x_8 = x_188;
goto block_78;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_165);
lean_dec(x_84);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = lean_ctor_get(x_167, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_167, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_197 = x_167;
} else {
 lean_dec_ref(x_167);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_168);
return x_199;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_84);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = !lean_is_exclusive(x_85);
if (x_213 == 0)
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_85);
lean_ctor_set(x_214, 1, x_86);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_215 = lean_ctor_get(x_85, 0);
x_216 = lean_ctor_get(x_85, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_85);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_86);
return x_218;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_294; 
x_230 = lean_ctor_get(x_79, 0);
x_231 = lean_ctor_get(x_79, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_79);
lean_inc(x_4);
x_232 = l_Lean_Parser_mkInputContext(x_230, x_4);
lean_inc(x_232);
x_294 = l_Lean_Parser_parseHeader(x_232, x_80);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set(x_297, 1, x_231);
x_233 = x_297;
x_234 = x_296;
goto block_293;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_298 = lean_ctor_get(x_294, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_294, 1);
lean_inc(x_299);
lean_dec(x_294);
x_300 = lean_io_error_to_string(x_298);
x_301 = 3;
x_302 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*1, x_301);
x_303 = lean_array_get_size(x_231);
x_304 = lean_array_push(x_231, x_302);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
x_233 = x_305;
x_234 = x_299;
goto block_293;
}
block_293:
{
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_276; 
x_235 = lean_ctor_get(x_233, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_238 = x_233;
} else {
 lean_dec_ref(x_233);
 x_238 = lean_box(0);
}
x_239 = lean_ctor_get(x_235, 0);
lean_inc(x_239);
lean_dec(x_235);
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_236, 1);
lean_inc(x_241);
lean_dec(x_236);
lean_inc(x_3);
x_276 = l_Lake_processHeader(x_239, x_3, x_232, x_241, x_234);
lean_dec(x_239);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
if (lean_is_scalar(x_238)) {
 x_279 = lean_alloc_ctor(0, 2, 0);
} else {
 x_279 = x_238;
}
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_237);
x_242 = x_279;
x_243 = x_278;
goto block_275;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_280 = lean_ctor_get(x_276, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_276, 1);
lean_inc(x_281);
lean_dec(x_276);
x_282 = lean_io_error_to_string(x_280);
x_283 = 3;
x_284 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_283);
x_285 = lean_array_get_size(x_237);
x_286 = lean_array_push(x_237, x_284);
if (lean_is_scalar(x_238)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_238;
 lean_ctor_set_tag(x_287, 1);
}
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_242 = x_287;
x_243 = x_281;
goto block_275;
}
block_275:
{
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_244 = lean_ctor_get(x_242, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_242, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_246 = x_242;
} else {
 lean_dec_ref(x_242);
 x_246 = lean_box(0);
}
x_247 = lean_ctor_get(x_244, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_244, 1);
lean_inc(x_248);
lean_dec(x_244);
x_249 = l_Lake_configModuleName;
x_250 = lean_environment_set_main_module(x_247, x_249);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_1);
x_252 = l_Lake_elabConfigFile___closed__2;
x_253 = l_Lean_EnvExtension_setState___rarg(x_252, x_250, x_251);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_2);
x_255 = l_Lake_elabConfigFile___closed__3;
x_256 = l_Lean_EnvExtension_setState___rarg(x_255, x_253, x_254);
x_257 = l_Lean_Elab_Command_mkState(x_256, x_248, x_3);
x_258 = l_Lean_Elab_IO_processCommands(x_232, x_240, x_257, x_243);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
if (lean_is_scalar(x_246)) {
 x_261 = lean_alloc_ctor(0, 2, 0);
} else {
 x_261 = x_246;
}
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_245);
x_7 = x_261;
x_8 = x_260;
goto block_78;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_262 = lean_ctor_get(x_258, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_258, 1);
lean_inc(x_263);
lean_dec(x_258);
x_264 = lean_io_error_to_string(x_262);
x_265 = 3;
x_266 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set_uint8(x_266, sizeof(void*)*1, x_265);
x_267 = lean_array_get_size(x_245);
x_268 = lean_array_push(x_245, x_266);
if (lean_is_scalar(x_246)) {
 x_269 = lean_alloc_ctor(1, 2, 0);
} else {
 x_269 = x_246;
 lean_ctor_set_tag(x_269, 1);
}
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_7 = x_269;
x_8 = x_263;
goto block_78;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_240);
lean_dec(x_232);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = lean_ctor_get(x_242, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_242, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_272 = x_242;
} else {
 lean_dec_ref(x_242);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_243);
return x_274;
}
}
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_232);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_288 = lean_ctor_get(x_233, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_233, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_290 = x_233;
} else {
 lean_dec_ref(x_233);
 x_290 = lean_box(0);
}
if (lean_is_scalar(x_290)) {
 x_291 = lean_alloc_ctor(1, 2, 0);
} else {
 x_291 = x_290;
}
lean_ctor_set(x_291, 0, x_288);
lean_ctor_set(x_291, 1, x_289);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_234);
return x_292;
}
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_79);
if (x_306 == 0)
{
lean_object* x_307; 
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_79);
lean_ctor_set(x_307, 1, x_80);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_79, 0);
x_309 = lean_ctor_get(x_79, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_79);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_80);
return x_311;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_addToEnv___boxed(lean_object* x_1, lean_object* x_2) {
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
x_1 = lean_mk_string_from_bytes("testRunnerAttr", 14);
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
x_1 = lean_mk_string_from_bytes("moduleFacetAttr", 15);
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
x_1 = lean_mk_string_from_bytes("packageFacetAttr", 16);
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
x_1 = lean_mk_string_from_bytes("libraryFacetAttr", 16);
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
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__45() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("docStringExt", 12);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__46() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__44;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__45;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__43;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__46;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("IR", 2);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__49() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("declMapExt", 10);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__50() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__44;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__48;
x_3 = l_Lake_importConfigFileCore_lakeExts___closed__49;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__47;
x_2 = l_Lake_importConfigFileCore_lakeExts___closed__50;
x_3 = lean_box(0);
x_4 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__51;
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
lean_inc(x_2);
x_16 = l_Lean_HashMapImp_find_x3f___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(x_2, x_11);
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
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Lake_instToJsonHash(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Lean_bignumToJson(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instToJsonHash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_instToJsonHash(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonHash___lambda__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lake_instFromJsonHash___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonHash___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("value '{j}' is too large for `UInt64`", 37);
return x_1;
}
}
static lean_object* _init_l_Lake_instFromJsonHash___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instFromJsonHash___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonHash(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_bignumFromJson_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lake_instFromJsonHash___closed__1;
x_8 = lean_nat_dec_le(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_box(0);
x_10 = l_Lake_instFromJsonHash___lambda__1(x_6, x_9);
lean_dec(x_6);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_6);
x_14 = l_Lake_instFromJsonHash___closed__3;
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instFromJsonHash___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instFromJsonHash___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("platform", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("leanHash", 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("configHash", 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("options", 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(lean_object* x_1) {
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
x_7 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__2;
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
x_18 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__3;
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
x_24 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__5;
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
x_31 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__4;
x_32 = l_List_bindTR_go___at___private_Lake_Util_Log_0__Lake_toJsonLogEntry____x40_Lake_Util_Log___hyg_1054____spec__1(x_30, x_31);
x_33 = l_Lean_Json_mkObj(x_32);
return x_33;
}
}
static lean_object* _init_l_Lake_instToJsonConfigTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_), 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lake_instFromJsonHash___closed__1;
x_10 = lean_nat_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(0);
x_12 = l_Lake_instFromJsonHash___lambda__1(x_8, x_11);
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
x_16 = l_Lake_instFromJsonHash___closed__3;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Json_getObjValD(x_1, x_2);
x_4 = l_Lean_Json_getObj_x3f(x_3);
lean_dec(x_3);
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
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ConfigTrace", 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__2;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(".", 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__3;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__4;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__6;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__5;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(": ", 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__8;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__11;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__5;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__12;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__13;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__15;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__5;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__16;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__17;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__19;
x_2 = 1;
x_3 = l_Lean_Name_toString(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__5;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__20;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__21;
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__9;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__1;
x_3 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__10;
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
x_9 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__10;
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
x_13 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__2;
x_14 = l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__14;
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
x_20 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__14;
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
x_24 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__3;
x_25 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__1(x_1, x_24);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
lean_dec(x_12);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__18;
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
x_31 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__18;
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
x_35 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__5;
x_36 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__2(x_1, x_35);
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
x_39 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__22;
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
x_42 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__22;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133_(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instFromJsonConfigTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____boxed), 1, 0);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_2031; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = l_Lake_defaultLakeDir;
lean_inc(x_6);
x_17 = l_System_FilePath_join(x_6, x_16);
x_18 = l_Lake_importConfigFile___closed__3;
lean_inc(x_15);
x_19 = l_System_FilePath_withExtension(x_15, x_18);
lean_inc(x_17);
x_20 = l_System_FilePath_join(x_17, x_19);
x_21 = l_Lake_importConfigFile___closed__4;
lean_inc(x_15);
x_22 = l_System_FilePath_withExtension(x_15, x_21);
lean_inc(x_17);
x_23 = l_System_FilePath_join(x_17, x_22);
x_24 = l_Lake_importConfigFile___closed__5;
x_25 = l_System_FilePath_withExtension(x_15, x_24);
lean_inc(x_17);
x_26 = l_System_FilePath_join(x_17, x_25);
x_2031 = l_Lake_computeTextFileHash(x_8, x_3);
if (lean_obj_tag(x_2031) == 0)
{
lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; 
x_2032 = lean_ctor_get(x_2031, 0);
lean_inc(x_2032);
x_2033 = lean_ctor_get(x_2031, 1);
lean_inc(x_2033);
lean_dec(x_2031);
x_2034 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2034, 0, x_2032);
lean_ctor_set(x_2034, 1, x_2);
x_27 = x_2034;
x_28 = x_2033;
goto block_2030;
}
else
{
lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; uint8_t x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; 
x_2035 = lean_ctor_get(x_2031, 0);
lean_inc(x_2035);
x_2036 = lean_ctor_get(x_2031, 1);
lean_inc(x_2036);
lean_dec(x_2031);
x_2037 = lean_io_error_to_string(x_2035);
x_2038 = 3;
x_2039 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2039, 0, x_2037);
lean_ctor_set_uint8(x_2039, sizeof(void*)*1, x_2038);
x_2040 = lean_array_get_size(x_2);
x_2041 = lean_array_push(x_2, x_2039);
x_2042 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2042, 0, x_2040);
lean_ctor_set(x_2042, 1, x_2041);
x_27 = x_2042;
x_28 = x_2036;
goto block_2030;
}
block_2030:
{
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_518; lean_object* x_519; lean_object* x_1239; lean_object* x_1240; lean_object* x_1977; lean_object* x_1978; uint8_t x_1979; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_1977 = l_System_FilePath_pathExists(x_23, x_28);
x_1978 = lean_ctor_get(x_1977, 0);
lean_inc(x_1978);
x_1979 = lean_unbox(x_1978);
lean_dec(x_1978);
if (x_1979 == 0)
{
lean_object* x_1980; lean_object* x_1981; 
x_1980 = lean_ctor_get(x_1977, 1);
lean_inc(x_1980);
lean_dec(x_1977);
x_1981 = l_IO_FS_createDirAll(x_17, x_1980);
if (lean_obj_tag(x_1981) == 0)
{
lean_object* x_1982; uint8_t x_1983; lean_object* x_1984; 
x_1982 = lean_ctor_get(x_1981, 1);
lean_inc(x_1982);
lean_dec(x_1981);
x_1983 = 2;
x_1984 = lean_io_prim_handle_mk(x_23, x_1983, x_1982);
if (lean_obj_tag(x_1984) == 0)
{
lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; 
x_1985 = lean_ctor_get(x_1984, 0);
lean_inc(x_1985);
x_1986 = lean_ctor_get(x_1984, 1);
lean_inc(x_1986);
lean_dec(x_1984);
x_1987 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1987, 0, x_1985);
x_1988 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1988, 0, x_1987);
lean_ctor_set(x_1988, 1, x_30);
x_1239 = x_1988;
x_1240 = x_1986;
goto block_1976;
}
else
{
lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; 
x_1989 = lean_ctor_get(x_1984, 0);
lean_inc(x_1989);
x_1990 = lean_ctor_get(x_1984, 1);
lean_inc(x_1990);
lean_dec(x_1984);
x_1991 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1991, 0, x_1989);
x_1992 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1992, 0, x_1991);
lean_ctor_set(x_1992, 1, x_30);
x_1239 = x_1992;
x_1240 = x_1990;
goto block_1976;
}
}
else
{
uint8_t x_1993; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1993 = !lean_is_exclusive(x_1981);
if (x_1993 == 0)
{
lean_object* x_1994; lean_object* x_1995; uint8_t x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; 
x_1994 = lean_ctor_get(x_1981, 0);
x_1995 = lean_io_error_to_string(x_1994);
x_1996 = 3;
x_1997 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1997, 0, x_1995);
lean_ctor_set_uint8(x_1997, sizeof(void*)*1, x_1996);
x_1998 = lean_array_get_size(x_30);
x_1999 = lean_array_push(x_30, x_1997);
x_2000 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2000, 0, x_1998);
lean_ctor_set(x_2000, 1, x_1999);
lean_ctor_set_tag(x_1981, 0);
lean_ctor_set(x_1981, 0, x_2000);
return x_1981;
}
else
{
lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; uint8_t x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; 
x_2001 = lean_ctor_get(x_1981, 0);
x_2002 = lean_ctor_get(x_1981, 1);
lean_inc(x_2002);
lean_inc(x_2001);
lean_dec(x_1981);
x_2003 = lean_io_error_to_string(x_2001);
x_2004 = 3;
x_2005 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2005, 0, x_2003);
lean_ctor_set_uint8(x_2005, sizeof(void*)*1, x_2004);
x_2006 = lean_array_get_size(x_30);
x_2007 = lean_array_push(x_30, x_2005);
x_2008 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2008, 0, x_2006);
lean_ctor_set(x_2008, 1, x_2007);
x_2009 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2009, 0, x_2008);
lean_ctor_set(x_2009, 1, x_2002);
return x_2009;
}
}
}
else
{
lean_object* x_2010; uint8_t x_2011; lean_object* x_2012; 
lean_dec(x_17);
x_2010 = lean_ctor_get(x_1977, 1);
lean_inc(x_2010);
lean_dec(x_1977);
x_2011 = 0;
x_2012 = lean_io_prim_handle_mk(x_23, x_2011, x_2010);
if (lean_obj_tag(x_2012) == 0)
{
lean_object* x_2013; lean_object* x_2014; lean_object* x_2015; 
x_2013 = lean_ctor_get(x_2012, 0);
lean_inc(x_2013);
x_2014 = lean_ctor_get(x_2012, 1);
lean_inc(x_2014);
lean_dec(x_2012);
x_2015 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2015, 0, x_2013);
lean_ctor_set(x_2015, 1, x_30);
x_518 = x_2015;
x_519 = x_2014;
goto block_1238;
}
else
{
lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; uint8_t x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; 
x_2016 = lean_ctor_get(x_2012, 0);
lean_inc(x_2016);
x_2017 = lean_ctor_get(x_2012, 1);
lean_inc(x_2017);
lean_dec(x_2012);
x_2018 = lean_io_error_to_string(x_2016);
x_2019 = 3;
x_2020 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2020, 0, x_2018);
lean_ctor_set_uint8(x_2020, sizeof(void*)*1, x_2019);
x_2021 = lean_array_get_size(x_30);
x_2022 = lean_array_push(x_30, x_2020);
x_2023 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2023, 0, x_2021);
lean_ctor_set(x_2023, 1, x_2022);
x_518 = x_2023;
x_519 = x_2017;
goto block_1238;
}
}
block_517:
{
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_132; lean_object* x_133; lean_object* x_341; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_1, 4);
lean_inc(x_36);
x_341 = lean_io_remove_file(x_20, x_33);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_32, 0, x_344);
x_132 = x_32;
x_133 = x_343;
goto block_340;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_341, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_341, 1);
lean_inc(x_346);
lean_dec(x_341);
x_347 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_32, 0, x_347);
x_132 = x_32;
x_133 = x_346;
goto block_340;
}
block_131:
{
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_1, 5);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l_Lake_elabConfigFile(x_6, x_36, x_40, x_8, x_39, x_38);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = !lean_is_exclusive(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_47 = lean_write_module(x_45, x_20, x_43);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_io_prim_handle_unlock(x_35, x_48);
lean_dec(x_35);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_42);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_45);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_io_error_to_string(x_55);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_array_get_size(x_46);
x_60 = lean_array_push(x_46, x_58);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_60);
lean_ctor_set(x_42, 0, x_59);
lean_ctor_set_tag(x_49, 0);
lean_ctor_set(x_49, 0, x_42);
return x_49;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_49, 0);
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_49);
x_63 = lean_io_error_to_string(x_61);
x_64 = 3;
x_65 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*1, x_64);
x_66 = lean_array_get_size(x_46);
x_67 = lean_array_push(x_46, x_65);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_67);
lean_ctor_set(x_42, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_42);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_45);
lean_dec(x_35);
x_69 = !lean_is_exclusive(x_47);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_47, 0);
x_71 = lean_io_error_to_string(x_70);
x_72 = 3;
x_73 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_72);
x_74 = lean_array_get_size(x_46);
x_75 = lean_array_push(x_46, x_73);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_75);
lean_ctor_set(x_42, 0, x_74);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_42);
return x_47;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_76 = lean_ctor_get(x_47, 0);
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_47);
x_78 = lean_io_error_to_string(x_76);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_array_get_size(x_46);
x_82 = lean_array_push(x_46, x_80);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_82);
lean_ctor_set(x_42, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_42);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_42, 0);
x_85 = lean_ctor_get(x_42, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_42);
lean_inc(x_84);
x_86 = lean_write_module(x_84, x_20, x_43);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_io_prim_handle_unlock(x_35, x_87);
lean_dec(x_35);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_84);
lean_ctor_set(x_91, 1, x_85);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_84);
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_95 = x_88;
} else {
 lean_dec_ref(x_88);
 x_95 = lean_box(0);
}
x_96 = lean_io_error_to_string(x_93);
x_97 = 3;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_array_get_size(x_85);
x_100 = lean_array_push(x_85, x_98);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
if (lean_is_scalar(x_95)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_95;
 lean_ctor_set_tag(x_102, 0);
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_94);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_84);
lean_dec(x_35);
x_103 = lean_ctor_get(x_86, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_86, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_105 = x_86;
} else {
 lean_dec_ref(x_86);
 x_105 = lean_box(0);
}
x_106 = lean_io_error_to_string(x_103);
x_107 = 3;
x_108 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set_uint8(x_108, sizeof(void*)*1, x_107);
x_109 = lean_array_get_size(x_85);
x_110 = lean_array_push(x_85, x_108);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
if (lean_is_scalar(x_105)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_105;
 lean_ctor_set_tag(x_112, 0);
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_104);
return x_112;
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_35);
lean_dec(x_20);
x_113 = !lean_is_exclusive(x_41);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_41, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_42);
if (x_115 == 0)
{
return x_41;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_42, 0);
x_117 = lean_ctor_get(x_42, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_42);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_41, 0, x_118);
return x_41;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_41, 1);
lean_inc(x_119);
lean_dec(x_41);
x_120 = lean_ctor_get(x_42, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_42, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_122 = x_42;
} else {
 lean_dec_ref(x_42);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_119);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_37);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_37);
lean_ctor_set(x_126, 1, x_38);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_37, 0);
x_128 = lean_ctor_get(x_37, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_37);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_38);
return x_130;
}
}
}
block_340:
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_132, 0);
lean_inc(x_134);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec(x_134);
if (lean_obj_tag(x_135) == 11)
{
uint8_t x_136; 
lean_dec(x_135);
lean_dec(x_23);
x_136 = !lean_is_exclusive(x_132);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_137 = lean_ctor_get(x_132, 1);
x_138 = lean_ctor_get(x_132, 0);
lean_dec(x_138);
x_139 = lean_ctor_get(x_1, 0);
lean_inc(x_139);
x_140 = l_Lake_Env_leanGithash(x_139);
lean_dec(x_139);
x_141 = l_System_Platform_target;
lean_inc(x_36);
x_142 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
lean_ctor_set(x_142, 2, x_29);
lean_ctor_set(x_142, 3, x_36);
x_143 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_142);
x_144 = lean_unsigned_to_nat(80u);
x_145 = l_Lean_Json_pretty(x_143, x_144);
x_146 = l_IO_FS_Handle_putStrLn(x_35, x_145, x_133);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = lean_io_prim_handle_truncate(x_35, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
lean_ctor_set(x_132, 0, x_149);
x_37 = x_132;
x_38 = x_150;
goto block_131;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_148, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_148, 1);
lean_inc(x_152);
lean_dec(x_148);
x_153 = lean_io_error_to_string(x_151);
x_154 = 3;
x_155 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set_uint8(x_155, sizeof(void*)*1, x_154);
x_156 = lean_array_get_size(x_137);
x_157 = lean_array_push(x_137, x_155);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_157);
lean_ctor_set(x_132, 0, x_156);
x_37 = x_132;
x_38 = x_152;
goto block_131;
}
}
else
{
uint8_t x_158; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_146);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_146, 0);
x_160 = lean_io_error_to_string(x_159);
x_161 = 3;
x_162 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set_uint8(x_162, sizeof(void*)*1, x_161);
x_163 = lean_array_get_size(x_137);
x_164 = lean_array_push(x_137, x_162);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_164);
lean_ctor_set(x_132, 0, x_163);
lean_ctor_set_tag(x_146, 0);
lean_ctor_set(x_146, 0, x_132);
return x_146;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_146, 0);
x_166 = lean_ctor_get(x_146, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_146);
x_167 = lean_io_error_to_string(x_165);
x_168 = 3;
x_169 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_168);
x_170 = lean_array_get_size(x_137);
x_171 = lean_array_push(x_137, x_169);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_171);
lean_ctor_set(x_132, 0, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_132);
lean_ctor_set(x_172, 1, x_166);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_173 = lean_ctor_get(x_132, 1);
lean_inc(x_173);
lean_dec(x_132);
x_174 = lean_ctor_get(x_1, 0);
lean_inc(x_174);
x_175 = l_Lake_Env_leanGithash(x_174);
lean_dec(x_174);
x_176 = l_System_Platform_target;
lean_inc(x_36);
x_177 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_177, 2, x_29);
lean_ctor_set(x_177, 3, x_36);
x_178 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_177);
x_179 = lean_unsigned_to_nat(80u);
x_180 = l_Lean_Json_pretty(x_178, x_179);
x_181 = l_IO_FS_Handle_putStrLn(x_35, x_180, x_133);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_io_prim_handle_truncate(x_35, x_182);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_173);
x_37 = x_186;
x_38 = x_185;
goto block_131;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_187 = lean_ctor_get(x_183, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_183, 1);
lean_inc(x_188);
lean_dec(x_183);
x_189 = lean_io_error_to_string(x_187);
x_190 = 3;
x_191 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set_uint8(x_191, sizeof(void*)*1, x_190);
x_192 = lean_array_get_size(x_173);
x_193 = lean_array_push(x_173, x_191);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_37 = x_194;
x_38 = x_188;
goto block_131;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_195 = lean_ctor_get(x_181, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_181, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_197 = x_181;
} else {
 lean_dec_ref(x_181);
 x_197 = lean_box(0);
}
x_198 = lean_io_error_to_string(x_195);
x_199 = 3;
x_200 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set_uint8(x_200, sizeof(void*)*1, x_199);
x_201 = lean_array_get_size(x_173);
x_202 = lean_array_push(x_173, x_200);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
if (lean_is_scalar(x_197)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_197;
 lean_ctor_set_tag(x_204, 0);
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_196);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_36);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_132);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_206 = lean_ctor_get(x_132, 1);
x_207 = lean_ctor_get(x_132, 0);
lean_dec(x_207);
x_208 = lean_io_error_to_string(x_135);
x_209 = 3;
x_210 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set_uint8(x_210, sizeof(void*)*1, x_209);
x_211 = lean_array_get_size(x_206);
x_212 = lean_array_push(x_206, x_210);
x_213 = lean_io_prim_handle_unlock(x_35, x_133);
lean_dec(x_35);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_io_remove_file(x_23, x_214);
lean_dec(x_23);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_215, 0);
lean_dec(x_217);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_212);
lean_ctor_set(x_132, 0, x_211);
lean_ctor_set(x_215, 0, x_132);
return x_215;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_215, 1);
lean_inc(x_218);
lean_dec(x_215);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_212);
lean_ctor_set(x_132, 0, x_211);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_132);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
else
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_215);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_221 = lean_ctor_get(x_215, 0);
x_222 = lean_io_error_to_string(x_221);
x_223 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_209);
x_224 = lean_array_push(x_212, x_223);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_224);
lean_ctor_set(x_132, 0, x_211);
lean_ctor_set_tag(x_215, 0);
lean_ctor_set(x_215, 0, x_132);
return x_215;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_225 = lean_ctor_get(x_215, 0);
x_226 = lean_ctor_get(x_215, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_215);
x_227 = lean_io_error_to_string(x_225);
x_228 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_209);
x_229 = lean_array_push(x_212, x_228);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_229);
lean_ctor_set(x_132, 0, x_211);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_132);
lean_ctor_set(x_230, 1, x_226);
return x_230;
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_23);
x_231 = !lean_is_exclusive(x_213);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_213, 0);
x_233 = lean_io_error_to_string(x_232);
x_234 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set_uint8(x_234, sizeof(void*)*1, x_209);
x_235 = lean_array_push(x_212, x_234);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_235);
lean_ctor_set(x_132, 0, x_211);
lean_ctor_set_tag(x_213, 0);
lean_ctor_set(x_213, 0, x_132);
return x_213;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_236 = lean_ctor_get(x_213, 0);
x_237 = lean_ctor_get(x_213, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_213);
x_238 = lean_io_error_to_string(x_236);
x_239 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set_uint8(x_239, sizeof(void*)*1, x_209);
x_240 = lean_array_push(x_212, x_239);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_240);
lean_ctor_set(x_132, 0, x_211);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_132);
lean_ctor_set(x_241, 1, x_237);
return x_241;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_242 = lean_ctor_get(x_132, 1);
lean_inc(x_242);
lean_dec(x_132);
x_243 = lean_io_error_to_string(x_135);
x_244 = 3;
x_245 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set_uint8(x_245, sizeof(void*)*1, x_244);
x_246 = lean_array_get_size(x_242);
x_247 = lean_array_push(x_242, x_245);
x_248 = lean_io_prim_handle_unlock(x_35, x_133);
lean_dec(x_35);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = lean_io_remove_file(x_23, x_249);
lean_dec(x_23);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_246);
lean_ctor_set(x_253, 1, x_247);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_255 = lean_ctor_get(x_250, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_250, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_257 = x_250;
} else {
 lean_dec_ref(x_250);
 x_257 = lean_box(0);
}
x_258 = lean_io_error_to_string(x_255);
x_259 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_244);
x_260 = lean_array_push(x_247, x_259);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_246);
lean_ctor_set(x_261, 1, x_260);
if (lean_is_scalar(x_257)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_257;
 lean_ctor_set_tag(x_262, 0);
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_256);
return x_262;
}
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_23);
x_263 = lean_ctor_get(x_248, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_248, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_265 = x_248;
} else {
 lean_dec_ref(x_248);
 x_265 = lean_box(0);
}
x_266 = lean_io_error_to_string(x_263);
x_267 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set_uint8(x_267, sizeof(void*)*1, x_244);
x_268 = lean_array_push(x_247, x_267);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_246);
lean_ctor_set(x_269, 1, x_268);
if (lean_is_scalar(x_265)) {
 x_270 = lean_alloc_ctor(0, 2, 0);
} else {
 x_270 = x_265;
 lean_ctor_set_tag(x_270, 0);
}
lean_ctor_set(x_270, 0, x_269);
lean_ctor_set(x_270, 1, x_264);
return x_270;
}
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_134);
lean_dec(x_23);
x_271 = !lean_is_exclusive(x_132);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_272 = lean_ctor_get(x_132, 1);
x_273 = lean_ctor_get(x_132, 0);
lean_dec(x_273);
x_274 = lean_ctor_get(x_1, 0);
lean_inc(x_274);
x_275 = l_Lake_Env_leanGithash(x_274);
lean_dec(x_274);
x_276 = l_System_Platform_target;
lean_inc(x_36);
x_277 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
lean_ctor_set(x_277, 2, x_29);
lean_ctor_set(x_277, 3, x_36);
x_278 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_277);
x_279 = lean_unsigned_to_nat(80u);
x_280 = l_Lean_Json_pretty(x_278, x_279);
x_281 = l_IO_FS_Handle_putStrLn(x_35, x_280, x_133);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
x_283 = lean_io_prim_handle_truncate(x_35, x_282);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
lean_ctor_set(x_132, 0, x_284);
x_37 = x_132;
x_38 = x_285;
goto block_131;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_286 = lean_ctor_get(x_283, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
lean_dec(x_283);
x_288 = lean_io_error_to_string(x_286);
x_289 = 3;
x_290 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set_uint8(x_290, sizeof(void*)*1, x_289);
x_291 = lean_array_get_size(x_272);
x_292 = lean_array_push(x_272, x_290);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_292);
lean_ctor_set(x_132, 0, x_291);
x_37 = x_132;
x_38 = x_287;
goto block_131;
}
}
else
{
uint8_t x_293; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_293 = !lean_is_exclusive(x_281);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_294 = lean_ctor_get(x_281, 0);
x_295 = lean_io_error_to_string(x_294);
x_296 = 3;
x_297 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set_uint8(x_297, sizeof(void*)*1, x_296);
x_298 = lean_array_get_size(x_272);
x_299 = lean_array_push(x_272, x_297);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_299);
lean_ctor_set(x_132, 0, x_298);
lean_ctor_set_tag(x_281, 0);
lean_ctor_set(x_281, 0, x_132);
return x_281;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_300 = lean_ctor_get(x_281, 0);
x_301 = lean_ctor_get(x_281, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_281);
x_302 = lean_io_error_to_string(x_300);
x_303 = 3;
x_304 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set_uint8(x_304, sizeof(void*)*1, x_303);
x_305 = lean_array_get_size(x_272);
x_306 = lean_array_push(x_272, x_304);
lean_ctor_set_tag(x_132, 1);
lean_ctor_set(x_132, 1, x_306);
lean_ctor_set(x_132, 0, x_305);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_132);
lean_ctor_set(x_307, 1, x_301);
return x_307;
}
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_308 = lean_ctor_get(x_132, 1);
lean_inc(x_308);
lean_dec(x_132);
x_309 = lean_ctor_get(x_1, 0);
lean_inc(x_309);
x_310 = l_Lake_Env_leanGithash(x_309);
lean_dec(x_309);
x_311 = l_System_Platform_target;
lean_inc(x_36);
x_312 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_310);
lean_ctor_set(x_312, 2, x_29);
lean_ctor_set(x_312, 3, x_36);
x_313 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_312);
x_314 = lean_unsigned_to_nat(80u);
x_315 = l_Lean_Json_pretty(x_313, x_314);
x_316 = l_IO_FS_Handle_putStrLn(x_35, x_315, x_133);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
x_318 = lean_io_prim_handle_truncate(x_35, x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_308);
x_37 = x_321;
x_38 = x_320;
goto block_131;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_322 = lean_ctor_get(x_318, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_318, 1);
lean_inc(x_323);
lean_dec(x_318);
x_324 = lean_io_error_to_string(x_322);
x_325 = 3;
x_326 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set_uint8(x_326, sizeof(void*)*1, x_325);
x_327 = lean_array_get_size(x_308);
x_328 = lean_array_push(x_308, x_326);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
x_37 = x_329;
x_38 = x_323;
goto block_131;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_330 = lean_ctor_get(x_316, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_316, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_332 = x_316;
} else {
 lean_dec_ref(x_316);
 x_332 = lean_box(0);
}
x_333 = lean_io_error_to_string(x_330);
x_334 = 3;
x_335 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set_uint8(x_335, sizeof(void*)*1, x_334);
x_336 = lean_array_get_size(x_308);
x_337 = lean_array_push(x_308, x_335);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
if (lean_is_scalar(x_332)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_332;
 lean_ctor_set_tag(x_339, 0);
}
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_331);
return x_339;
}
}
}
}
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_401; lean_object* x_402; lean_object* x_502; 
x_348 = lean_ctor_get(x_32, 0);
x_349 = lean_ctor_get(x_32, 1);
lean_inc(x_349);
lean_inc(x_348);
lean_dec(x_32);
x_350 = lean_ctor_get(x_1, 4);
lean_inc(x_350);
x_502 = lean_io_remove_file(x_20, x_33);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_503);
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_349);
x_401 = x_506;
x_402 = x_504;
goto block_501;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_ctor_get(x_502, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_502, 1);
lean_inc(x_508);
lean_dec(x_502);
x_509 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_509, 0, x_507);
x_510 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_349);
x_401 = x_510;
x_402 = x_508;
goto block_501;
}
block_400:
{
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_ctor_get(x_1, 5);
lean_inc(x_354);
lean_dec(x_1);
x_355 = l_Lake_elabConfigFile(x_6, x_350, x_354, x_8, x_353, x_352);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = lean_ctor_get(x_356, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_356, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_360 = x_356;
} else {
 lean_dec_ref(x_356);
 x_360 = lean_box(0);
}
lean_inc(x_358);
x_361 = lean_write_module(x_358, x_20, x_357);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
x_363 = lean_io_prim_handle_unlock(x_348, x_362);
lean_dec(x_348);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_365 = x_363;
} else {
 lean_dec_ref(x_363);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_366 = lean_alloc_ctor(0, 2, 0);
} else {
 x_366 = x_360;
}
lean_ctor_set(x_366, 0, x_358);
lean_ctor_set(x_366, 1, x_359);
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_364);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_358);
x_368 = lean_ctor_get(x_363, 0);
lean_inc(x_368);
x_369 = lean_ctor_get(x_363, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_370 = x_363;
} else {
 lean_dec_ref(x_363);
 x_370 = lean_box(0);
}
x_371 = lean_io_error_to_string(x_368);
x_372 = 3;
x_373 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set_uint8(x_373, sizeof(void*)*1, x_372);
x_374 = lean_array_get_size(x_359);
x_375 = lean_array_push(x_359, x_373);
if (lean_is_scalar(x_360)) {
 x_376 = lean_alloc_ctor(1, 2, 0);
} else {
 x_376 = x_360;
 lean_ctor_set_tag(x_376, 1);
}
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
if (lean_is_scalar(x_370)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_370;
 lean_ctor_set_tag(x_377, 0);
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_369);
return x_377;
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; uint8_t x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_358);
lean_dec(x_348);
x_378 = lean_ctor_get(x_361, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_361, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_380 = x_361;
} else {
 lean_dec_ref(x_361);
 x_380 = lean_box(0);
}
x_381 = lean_io_error_to_string(x_378);
x_382 = 3;
x_383 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set_uint8(x_383, sizeof(void*)*1, x_382);
x_384 = lean_array_get_size(x_359);
x_385 = lean_array_push(x_359, x_383);
if (lean_is_scalar(x_360)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_360;
 lean_ctor_set_tag(x_386, 1);
}
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
if (lean_is_scalar(x_380)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_380;
 lean_ctor_set_tag(x_387, 0);
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_379);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_348);
lean_dec(x_20);
x_388 = lean_ctor_get(x_355, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_389 = x_355;
} else {
 lean_dec_ref(x_355);
 x_389 = lean_box(0);
}
x_390 = lean_ctor_get(x_356, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_356, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_392 = x_356;
} else {
 lean_dec_ref(x_356);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_391);
if (lean_is_scalar(x_389)) {
 x_394 = lean_alloc_ctor(0, 2, 0);
} else {
 x_394 = x_389;
}
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_388);
return x_394;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_395 = lean_ctor_get(x_351, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_351, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_397 = x_351;
} else {
 lean_dec_ref(x_351);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_352);
return x_399;
}
}
block_501:
{
lean_object* x_403; 
x_403 = lean_ctor_get(x_401, 0);
lean_inc(x_403);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
lean_dec(x_403);
if (lean_obj_tag(x_404) == 11)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_404);
lean_dec(x_23);
x_405 = lean_ctor_get(x_401, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_406 = x_401;
} else {
 lean_dec_ref(x_401);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_1, 0);
lean_inc(x_407);
x_408 = l_Lake_Env_leanGithash(x_407);
lean_dec(x_407);
x_409 = l_System_Platform_target;
lean_inc(x_350);
x_410 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_408);
lean_ctor_set(x_410, 2, x_29);
lean_ctor_set(x_410, 3, x_350);
x_411 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_410);
x_412 = lean_unsigned_to_nat(80u);
x_413 = l_Lean_Json_pretty(x_411, x_412);
x_414 = l_IO_FS_Handle_putStrLn(x_348, x_413, x_402);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
x_416 = lean_io_prim_handle_truncate(x_348, x_415);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_418);
lean_dec(x_416);
if (lean_is_scalar(x_406)) {
 x_419 = lean_alloc_ctor(0, 2, 0);
} else {
 x_419 = x_406;
}
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_405);
x_351 = x_419;
x_352 = x_418;
goto block_400;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_420 = lean_ctor_get(x_416, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_416, 1);
lean_inc(x_421);
lean_dec(x_416);
x_422 = lean_io_error_to_string(x_420);
x_423 = 3;
x_424 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set_uint8(x_424, sizeof(void*)*1, x_423);
x_425 = lean_array_get_size(x_405);
x_426 = lean_array_push(x_405, x_424);
if (lean_is_scalar(x_406)) {
 x_427 = lean_alloc_ctor(1, 2, 0);
} else {
 x_427 = x_406;
 lean_ctor_set_tag(x_427, 1);
}
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
x_351 = x_427;
x_352 = x_421;
goto block_400;
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_428 = lean_ctor_get(x_414, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_414, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_430 = x_414;
} else {
 lean_dec_ref(x_414);
 x_430 = lean_box(0);
}
x_431 = lean_io_error_to_string(x_428);
x_432 = 3;
x_433 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*1, x_432);
x_434 = lean_array_get_size(x_405);
x_435 = lean_array_push(x_405, x_433);
if (lean_is_scalar(x_406)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_406;
 lean_ctor_set_tag(x_436, 1);
}
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
if (lean_is_scalar(x_430)) {
 x_437 = lean_alloc_ctor(0, 2, 0);
} else {
 x_437 = x_430;
 lean_ctor_set_tag(x_437, 0);
}
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_429);
return x_437;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_350);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_438 = lean_ctor_get(x_401, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_439 = x_401;
} else {
 lean_dec_ref(x_401);
 x_439 = lean_box(0);
}
x_440 = lean_io_error_to_string(x_404);
x_441 = 3;
x_442 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set_uint8(x_442, sizeof(void*)*1, x_441);
x_443 = lean_array_get_size(x_438);
x_444 = lean_array_push(x_438, x_442);
x_445 = lean_io_prim_handle_unlock(x_348, x_402);
lean_dec(x_348);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
lean_dec(x_445);
x_447 = lean_io_remove_file(x_23, x_446);
lean_dec(x_23);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_448 = lean_ctor_get(x_447, 1);
lean_inc(x_448);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_449 = x_447;
} else {
 lean_dec_ref(x_447);
 x_449 = lean_box(0);
}
if (lean_is_scalar(x_439)) {
 x_450 = lean_alloc_ctor(1, 2, 0);
} else {
 x_450 = x_439;
 lean_ctor_set_tag(x_450, 1);
}
lean_ctor_set(x_450, 0, x_443);
lean_ctor_set(x_450, 1, x_444);
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_450);
lean_ctor_set(x_451, 1, x_448);
return x_451;
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_452 = lean_ctor_get(x_447, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_447, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_454 = x_447;
} else {
 lean_dec_ref(x_447);
 x_454 = lean_box(0);
}
x_455 = lean_io_error_to_string(x_452);
x_456 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set_uint8(x_456, sizeof(void*)*1, x_441);
x_457 = lean_array_push(x_444, x_456);
if (lean_is_scalar(x_439)) {
 x_458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_458 = x_439;
 lean_ctor_set_tag(x_458, 1);
}
lean_ctor_set(x_458, 0, x_443);
lean_ctor_set(x_458, 1, x_457);
if (lean_is_scalar(x_454)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_454;
 lean_ctor_set_tag(x_459, 0);
}
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_453);
return x_459;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_23);
x_460 = lean_ctor_get(x_445, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_445, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_462 = x_445;
} else {
 lean_dec_ref(x_445);
 x_462 = lean_box(0);
}
x_463 = lean_io_error_to_string(x_460);
x_464 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set_uint8(x_464, sizeof(void*)*1, x_441);
x_465 = lean_array_push(x_444, x_464);
if (lean_is_scalar(x_439)) {
 x_466 = lean_alloc_ctor(1, 2, 0);
} else {
 x_466 = x_439;
 lean_ctor_set_tag(x_466, 1);
}
lean_ctor_set(x_466, 0, x_443);
lean_ctor_set(x_466, 1, x_465);
if (lean_is_scalar(x_462)) {
 x_467 = lean_alloc_ctor(0, 2, 0);
} else {
 x_467 = x_462;
 lean_ctor_set_tag(x_467, 0);
}
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_461);
return x_467;
}
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_403);
lean_dec(x_23);
x_468 = lean_ctor_get(x_401, 1);
lean_inc(x_468);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_469 = x_401;
} else {
 lean_dec_ref(x_401);
 x_469 = lean_box(0);
}
x_470 = lean_ctor_get(x_1, 0);
lean_inc(x_470);
x_471 = l_Lake_Env_leanGithash(x_470);
lean_dec(x_470);
x_472 = l_System_Platform_target;
lean_inc(x_350);
x_473 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_471);
lean_ctor_set(x_473, 2, x_29);
lean_ctor_set(x_473, 3, x_350);
x_474 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_473);
x_475 = lean_unsigned_to_nat(80u);
x_476 = l_Lean_Json_pretty(x_474, x_475);
x_477 = l_IO_FS_Handle_putStrLn(x_348, x_476, x_402);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; 
x_478 = lean_ctor_get(x_477, 1);
lean_inc(x_478);
lean_dec(x_477);
x_479 = lean_io_prim_handle_truncate(x_348, x_478);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
if (lean_is_scalar(x_469)) {
 x_482 = lean_alloc_ctor(0, 2, 0);
} else {
 x_482 = x_469;
}
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_468);
x_351 = x_482;
x_352 = x_481;
goto block_400;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_483 = lean_ctor_get(x_479, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_479, 1);
lean_inc(x_484);
lean_dec(x_479);
x_485 = lean_io_error_to_string(x_483);
x_486 = 3;
x_487 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set_uint8(x_487, sizeof(void*)*1, x_486);
x_488 = lean_array_get_size(x_468);
x_489 = lean_array_push(x_468, x_487);
if (lean_is_scalar(x_469)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_469;
 lean_ctor_set_tag(x_490, 1);
}
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_351 = x_490;
x_352 = x_484;
goto block_400;
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_491 = lean_ctor_get(x_477, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_477, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_493 = x_477;
} else {
 lean_dec_ref(x_477);
 x_493 = lean_box(0);
}
x_494 = lean_io_error_to_string(x_491);
x_495 = 3;
x_496 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*1, x_495);
x_497 = lean_array_get_size(x_468);
x_498 = lean_array_push(x_468, x_496);
if (lean_is_scalar(x_469)) {
 x_499 = lean_alloc_ctor(1, 2, 0);
} else {
 x_499 = x_469;
 lean_ctor_set_tag(x_499, 1);
}
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
if (lean_is_scalar(x_493)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_493;
 lean_ctor_set_tag(x_500, 0);
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_492);
return x_500;
}
}
}
}
}
else
{
uint8_t x_511; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_511 = !lean_is_exclusive(x_32);
if (x_511 == 0)
{
lean_object* x_512; 
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_32);
lean_ctor_set(x_512, 1, x_33);
return x_512;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_513 = lean_ctor_get(x_32, 0);
x_514 = lean_ctor_get(x_32, 1);
lean_inc(x_514);
lean_inc(x_513);
lean_dec(x_32);
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_513);
lean_ctor_set(x_515, 1, x_514);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_33);
return x_516;
}
}
}
block_1238:
{
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; uint8_t x_1151; 
x_520 = lean_ctor_get(x_518, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_518, 1);
lean_inc(x_521);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 lean_ctor_release(x_518, 1);
 x_522 = x_518;
} else {
 lean_dec_ref(x_518);
 x_522 = lean_box(0);
}
x_1151 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
if (x_1151 == 0)
{
uint8_t x_1152; lean_object* x_1153; 
x_1152 = 0;
x_1153 = lean_io_prim_handle_lock(x_520, x_1152, x_519);
if (lean_obj_tag(x_1153) == 0)
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; 
x_1154 = lean_ctor_get(x_1153, 1);
lean_inc(x_1154);
lean_dec(x_1153);
x_1155 = l_Lake_processHeader___closed__1;
x_1156 = l_IO_FS_Handle_readToEnd_loop(x_520, x_1155, x_1154);
if (lean_obj_tag(x_1156) == 0)
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1157 = lean_ctor_get(x_1156, 0);
lean_inc(x_1157);
x_1158 = lean_ctor_get(x_1156, 1);
lean_inc(x_1158);
lean_dec(x_1156);
x_1159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1159, 0, x_1157);
lean_ctor_set(x_1159, 1, x_521);
x_523 = x_1159;
x_524 = x_1158;
goto block_1150;
}
else
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; uint8_t x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1160 = lean_ctor_get(x_1156, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_1156, 1);
lean_inc(x_1161);
lean_dec(x_1156);
x_1162 = lean_io_error_to_string(x_1160);
x_1163 = 3;
x_1164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1164, 0, x_1162);
lean_ctor_set_uint8(x_1164, sizeof(void*)*1, x_1163);
x_1165 = lean_array_get_size(x_521);
x_1166 = lean_array_push(x_521, x_1164);
x_1167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1167, 0, x_1165);
lean_ctor_set(x_1167, 1, x_1166);
x_523 = x_1167;
x_524 = x_1161;
goto block_1150;
}
}
else
{
uint8_t x_1168; 
lean_dec(x_522);
lean_dec(x_520);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1168 = !lean_is_exclusive(x_1153);
if (x_1168 == 0)
{
lean_object* x_1169; lean_object* x_1170; uint8_t x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1169 = lean_ctor_get(x_1153, 0);
x_1170 = lean_io_error_to_string(x_1169);
x_1171 = 3;
x_1172 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1172, 0, x_1170);
lean_ctor_set_uint8(x_1172, sizeof(void*)*1, x_1171);
x_1173 = lean_array_get_size(x_521);
x_1174 = lean_array_push(x_521, x_1172);
x_1175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1175, 0, x_1173);
lean_ctor_set(x_1175, 1, x_1174);
lean_ctor_set_tag(x_1153, 0);
lean_ctor_set(x_1153, 0, x_1175);
return x_1153;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; uint8_t x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; 
x_1176 = lean_ctor_get(x_1153, 0);
x_1177 = lean_ctor_get(x_1153, 1);
lean_inc(x_1177);
lean_inc(x_1176);
lean_dec(x_1153);
x_1178 = lean_io_error_to_string(x_1176);
x_1179 = 3;
x_1180 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1180, 0, x_1178);
lean_ctor_set_uint8(x_1180, sizeof(void*)*1, x_1179);
x_1181 = lean_array_get_size(x_521);
x_1182 = lean_array_push(x_521, x_1180);
x_1183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1183, 0, x_1181);
lean_ctor_set(x_1183, 1, x_1182);
x_1184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1184, 0, x_1183);
lean_ctor_set(x_1184, 1, x_1177);
return x_1184;
}
}
}
else
{
lean_object* x_1185; lean_object* x_1186; uint8_t x_1194; lean_object* x_1195; 
lean_dec(x_522);
lean_dec(x_31);
x_1194 = 1;
x_1195 = lean_io_prim_handle_mk(x_26, x_1194, x_519);
lean_dec(x_26);
if (lean_obj_tag(x_1195) == 0)
{
lean_object* x_1196; lean_object* x_1197; uint8_t x_1198; lean_object* x_1199; 
x_1196 = lean_ctor_get(x_1195, 0);
lean_inc(x_1196);
x_1197 = lean_ctor_get(x_1195, 1);
lean_inc(x_1197);
lean_dec(x_1195);
x_1198 = 1;
x_1199 = lean_io_prim_handle_try_lock(x_1196, x_1198, x_1197);
if (lean_obj_tag(x_1199) == 0)
{
lean_object* x_1200; uint8_t x_1201; 
x_1200 = lean_ctor_get(x_1199, 0);
lean_inc(x_1200);
x_1201 = lean_unbox(x_1200);
lean_dec(x_1200);
if (x_1201 == 0)
{
lean_object* x_1202; lean_object* x_1203; 
lean_dec(x_1196);
x_1202 = lean_ctor_get(x_1199, 1);
lean_inc(x_1202);
lean_dec(x_1199);
x_1203 = lean_io_prim_handle_unlock(x_520, x_1202);
lean_dec(x_520);
if (lean_obj_tag(x_1203) == 0)
{
lean_object* x_1204; lean_object* x_1205; 
x_1204 = lean_ctor_get(x_1203, 1);
lean_inc(x_1204);
lean_dec(x_1203);
x_1205 = l_Lake_importConfigFile___closed__11;
x_1185 = x_1205;
x_1186 = x_1204;
goto block_1193;
}
else
{
lean_object* x_1206; lean_object* x_1207; 
x_1206 = lean_ctor_get(x_1203, 0);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_1203, 1);
lean_inc(x_1207);
lean_dec(x_1203);
x_1185 = x_1206;
x_1186 = x_1207;
goto block_1193;
}
}
else
{
lean_object* x_1208; lean_object* x_1209; 
x_1208 = lean_ctor_get(x_1199, 1);
lean_inc(x_1208);
lean_dec(x_1199);
x_1209 = lean_io_prim_handle_unlock(x_520, x_1208);
lean_dec(x_520);
if (lean_obj_tag(x_1209) == 0)
{
lean_object* x_1210; uint8_t x_1211; lean_object* x_1212; 
x_1210 = lean_ctor_get(x_1209, 1);
lean_inc(x_1210);
lean_dec(x_1209);
x_1211 = 3;
x_1212 = lean_io_prim_handle_mk(x_23, x_1211, x_1210);
if (lean_obj_tag(x_1212) == 0)
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1213 = lean_ctor_get(x_1212, 0);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1212, 1);
lean_inc(x_1214);
lean_dec(x_1212);
x_1215 = lean_io_prim_handle_lock(x_1213, x_1198, x_1214);
if (lean_obj_tag(x_1215) == 0)
{
lean_object* x_1216; lean_object* x_1217; 
x_1216 = lean_ctor_get(x_1215, 1);
lean_inc(x_1216);
lean_dec(x_1215);
x_1217 = lean_io_prim_handle_unlock(x_1196, x_1216);
lean_dec(x_1196);
if (lean_obj_tag(x_1217) == 0)
{
lean_object* x_1218; lean_object* x_1219; 
x_1218 = lean_ctor_get(x_1217, 1);
lean_inc(x_1218);
lean_dec(x_1217);
x_1219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1219, 0, x_1213);
lean_ctor_set(x_1219, 1, x_521);
x_32 = x_1219;
x_33 = x_1218;
goto block_517;
}
else
{
lean_object* x_1220; lean_object* x_1221; 
lean_dec(x_1213);
x_1220 = lean_ctor_get(x_1217, 0);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1217, 1);
lean_inc(x_1221);
lean_dec(x_1217);
x_1185 = x_1220;
x_1186 = x_1221;
goto block_1193;
}
}
else
{
lean_object* x_1222; lean_object* x_1223; 
lean_dec(x_1213);
lean_dec(x_1196);
x_1222 = lean_ctor_get(x_1215, 0);
lean_inc(x_1222);
x_1223 = lean_ctor_get(x_1215, 1);
lean_inc(x_1223);
lean_dec(x_1215);
x_1185 = x_1222;
x_1186 = x_1223;
goto block_1193;
}
}
else
{
lean_object* x_1224; lean_object* x_1225; 
lean_dec(x_1196);
x_1224 = lean_ctor_get(x_1212, 0);
lean_inc(x_1224);
x_1225 = lean_ctor_get(x_1212, 1);
lean_inc(x_1225);
lean_dec(x_1212);
x_1185 = x_1224;
x_1186 = x_1225;
goto block_1193;
}
}
else
{
lean_object* x_1226; lean_object* x_1227; 
lean_dec(x_1196);
x_1226 = lean_ctor_get(x_1209, 0);
lean_inc(x_1226);
x_1227 = lean_ctor_get(x_1209, 1);
lean_inc(x_1227);
lean_dec(x_1209);
x_1185 = x_1226;
x_1186 = x_1227;
goto block_1193;
}
}
}
else
{
lean_object* x_1228; lean_object* x_1229; 
lean_dec(x_1196);
lean_dec(x_520);
x_1228 = lean_ctor_get(x_1199, 0);
lean_inc(x_1228);
x_1229 = lean_ctor_get(x_1199, 1);
lean_inc(x_1229);
lean_dec(x_1199);
x_1185 = x_1228;
x_1186 = x_1229;
goto block_1193;
}
}
else
{
lean_object* x_1230; lean_object* x_1231; 
lean_dec(x_520);
x_1230 = lean_ctor_get(x_1195, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1195, 1);
lean_inc(x_1231);
lean_dec(x_1195);
x_1185 = x_1230;
x_1186 = x_1231;
goto block_1193;
}
block_1193:
{
lean_object* x_1187; uint8_t x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1187 = lean_io_error_to_string(x_1185);
x_1188 = 3;
x_1189 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1189, 0, x_1187);
lean_ctor_set_uint8(x_1189, sizeof(void*)*1, x_1188);
x_1190 = lean_array_get_size(x_521);
x_1191 = lean_array_push(x_521, x_1189);
x_1192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1192, 0, x_1190);
lean_ctor_set(x_1192, 1, x_1191);
x_32 = x_1192;
x_33 = x_1186;
goto block_517;
}
}
block_1150:
{
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_525 = lean_ctor_get(x_523, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_523, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_523)) {
 lean_ctor_release(x_523, 0);
 lean_ctor_release(x_523, 1);
 x_527 = x_523;
} else {
 lean_dec_ref(x_523);
 x_527 = lean_box(0);
}
x_528 = l_Lean_Json_parse(x_525);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec(x_528);
lean_dec(x_522);
lean_dec(x_520);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_529 = lean_array_get_size(x_526);
x_530 = l_Lake_importConfigFile___closed__7;
x_531 = lean_array_push(x_526, x_530);
if (lean_is_scalar(x_527)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_527;
 lean_ctor_set_tag(x_532, 1);
}
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_531);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_533, 1, x_524);
return x_533;
}
else
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_ctor_get(x_528, 0);
lean_inc(x_534);
lean_dec(x_528);
x_535 = l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133_(x_534);
lean_dec(x_534);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_535);
lean_dec(x_522);
lean_dec(x_520);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_536 = lean_array_get_size(x_526);
x_537 = l_Lake_importConfigFile___closed__7;
x_538 = lean_array_push(x_526, x_537);
if (lean_is_scalar(x_527)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_527;
 lean_ctor_set_tag(x_539, 1);
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_538);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_524);
return x_540;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; uint8_t x_1083; 
x_541 = lean_ctor_get(x_535, 0);
lean_inc(x_541);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 x_542 = x_535;
} else {
 lean_dec_ref(x_535);
 x_542 = lean_box(0);
}
x_1031 = l_System_FilePath_pathExists(x_20, x_524);
x_1032 = lean_ctor_get(x_1031, 0);
lean_inc(x_1032);
x_1033 = lean_ctor_get(x_1031, 1);
lean_inc(x_1033);
lean_dec(x_1031);
x_1083 = lean_unbox(x_1032);
lean_dec(x_1032);
if (x_1083 == 0)
{
lean_object* x_1084; 
lean_dec(x_31);
x_1084 = lean_box(0);
x_1034 = x_1084;
goto block_1082;
}
else
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; uint8_t x_1089; 
x_1085 = lean_ctor_get(x_541, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_541, 1);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_541, 2);
lean_inc(x_1087);
x_1088 = l_System_Platform_target;
x_1089 = lean_string_dec_eq(x_1085, x_1088);
lean_dec(x_1085);
if (x_1089 == 0)
{
lean_object* x_1090; 
lean_dec(x_1087);
lean_dec(x_1086);
lean_dec(x_31);
x_1090 = lean_box(0);
x_1034 = x_1090;
goto block_1082;
}
else
{
lean_object* x_1091; lean_object* x_1092; uint8_t x_1093; 
x_1091 = lean_ctor_get(x_1, 0);
lean_inc(x_1091);
x_1092 = l_Lake_Env_leanGithash(x_1091);
lean_dec(x_1091);
x_1093 = lean_string_dec_eq(x_1086, x_1092);
lean_dec(x_1092);
lean_dec(x_1086);
if (x_1093 == 0)
{
lean_object* x_1094; 
lean_dec(x_1087);
lean_dec(x_31);
x_1094 = lean_box(0);
x_1034 = x_1094;
goto block_1082;
}
else
{
uint64_t x_1095; uint64_t x_1096; uint8_t x_1097; 
x_1095 = lean_unbox_uint64(x_1087);
lean_dec(x_1087);
x_1096 = lean_unbox_uint64(x_29);
x_1097 = lean_uint64_dec_eq(x_1095, x_1096);
if (x_1097 == 0)
{
lean_object* x_1098; 
lean_dec(x_31);
x_1098 = lean_box(0);
x_1034 = x_1098;
goto block_1082;
}
else
{
lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_527);
lean_dec(x_522);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_8);
lean_dec(x_6);
x_1099 = lean_ctor_get(x_1, 5);
lean_inc(x_1099);
lean_dec(x_1);
x_1100 = l_Lake_importConfigFileCore(x_20, x_1099, x_1033);
lean_dec(x_20);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
x_1101 = lean_ctor_get(x_1100, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1100, 1);
lean_inc(x_1102);
lean_dec(x_1100);
x_1103 = lean_io_prim_handle_unlock(x_520, x_1102);
lean_dec(x_520);
if (lean_obj_tag(x_1103) == 0)
{
uint8_t x_1104; 
x_1104 = !lean_is_exclusive(x_1103);
if (x_1104 == 0)
{
lean_object* x_1105; lean_object* x_1106; 
x_1105 = lean_ctor_get(x_1103, 0);
lean_dec(x_1105);
if (lean_is_scalar(x_31)) {
 x_1106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1106 = x_31;
}
lean_ctor_set(x_1106, 0, x_1101);
lean_ctor_set(x_1106, 1, x_526);
lean_ctor_set(x_1103, 0, x_1106);
return x_1103;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1107 = lean_ctor_get(x_1103, 1);
lean_inc(x_1107);
lean_dec(x_1103);
if (lean_is_scalar(x_31)) {
 x_1108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1108 = x_31;
}
lean_ctor_set(x_1108, 0, x_1101);
lean_ctor_set(x_1108, 1, x_526);
x_1109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1109, 0, x_1108);
lean_ctor_set(x_1109, 1, x_1107);
return x_1109;
}
}
else
{
uint8_t x_1110; 
lean_dec(x_1101);
x_1110 = !lean_is_exclusive(x_1103);
if (x_1110 == 0)
{
lean_object* x_1111; lean_object* x_1112; uint8_t x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; 
x_1111 = lean_ctor_get(x_1103, 0);
x_1112 = lean_io_error_to_string(x_1111);
x_1113 = 3;
x_1114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1114, 0, x_1112);
lean_ctor_set_uint8(x_1114, sizeof(void*)*1, x_1113);
x_1115 = lean_array_get_size(x_526);
x_1116 = lean_array_push(x_526, x_1114);
if (lean_is_scalar(x_31)) {
 x_1117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1117 = x_31;
 lean_ctor_set_tag(x_1117, 1);
}
lean_ctor_set(x_1117, 0, x_1115);
lean_ctor_set(x_1117, 1, x_1116);
lean_ctor_set_tag(x_1103, 0);
lean_ctor_set(x_1103, 0, x_1117);
return x_1103;
}
else
{
lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; uint8_t x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1118 = lean_ctor_get(x_1103, 0);
x_1119 = lean_ctor_get(x_1103, 1);
lean_inc(x_1119);
lean_inc(x_1118);
lean_dec(x_1103);
x_1120 = lean_io_error_to_string(x_1118);
x_1121 = 3;
x_1122 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1122, 0, x_1120);
lean_ctor_set_uint8(x_1122, sizeof(void*)*1, x_1121);
x_1123 = lean_array_get_size(x_526);
x_1124 = lean_array_push(x_526, x_1122);
if (lean_is_scalar(x_31)) {
 x_1125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1125 = x_31;
 lean_ctor_set_tag(x_1125, 1);
}
lean_ctor_set(x_1125, 0, x_1123);
lean_ctor_set(x_1125, 1, x_1124);
x_1126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1126, 0, x_1125);
lean_ctor_set(x_1126, 1, x_1119);
return x_1126;
}
}
}
else
{
uint8_t x_1127; 
lean_dec(x_520);
x_1127 = !lean_is_exclusive(x_1100);
if (x_1127 == 0)
{
lean_object* x_1128; lean_object* x_1129; uint8_t x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
x_1128 = lean_ctor_get(x_1100, 0);
x_1129 = lean_io_error_to_string(x_1128);
x_1130 = 3;
x_1131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1131, 0, x_1129);
lean_ctor_set_uint8(x_1131, sizeof(void*)*1, x_1130);
x_1132 = lean_array_get_size(x_526);
x_1133 = lean_array_push(x_526, x_1131);
if (lean_is_scalar(x_31)) {
 x_1134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1134 = x_31;
 lean_ctor_set_tag(x_1134, 1);
}
lean_ctor_set(x_1134, 0, x_1132);
lean_ctor_set(x_1134, 1, x_1133);
lean_ctor_set_tag(x_1100, 0);
lean_ctor_set(x_1100, 0, x_1134);
return x_1100;
}
else
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; uint8_t x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1135 = lean_ctor_get(x_1100, 0);
x_1136 = lean_ctor_get(x_1100, 1);
lean_inc(x_1136);
lean_inc(x_1135);
lean_dec(x_1100);
x_1137 = lean_io_error_to_string(x_1135);
x_1138 = 3;
x_1139 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1139, 0, x_1137);
lean_ctor_set_uint8(x_1139, sizeof(void*)*1, x_1138);
x_1140 = lean_array_get_size(x_526);
x_1141 = lean_array_push(x_526, x_1139);
if (lean_is_scalar(x_31)) {
 x_1142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1142 = x_31;
 lean_ctor_set_tag(x_1142, 1);
}
lean_ctor_set(x_1142, 0, x_1140);
lean_ctor_set(x_1142, 1, x_1141);
x_1143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1143, 0, x_1142);
lean_ctor_set(x_1143, 1, x_1136);
return x_1143;
}
}
}
}
}
}
block_1030:
{
if (lean_obj_tag(x_543) == 0)
{
uint8_t x_545; 
x_545 = !lean_is_exclusive(x_543);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_644; lean_object* x_645; lean_object* x_853; 
x_546 = lean_ctor_get(x_543, 0);
x_547 = lean_ctor_get(x_541, 3);
lean_inc(x_547);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 lean_ctor_release(x_541, 2);
 lean_ctor_release(x_541, 3);
 x_548 = x_541;
} else {
 lean_dec_ref(x_541);
 x_548 = lean_box(0);
}
x_853 = lean_io_remove_file(x_20, x_544);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
lean_dec(x_853);
if (lean_is_scalar(x_542)) {
 x_856 = lean_alloc_ctor(1, 1, 0);
} else {
 x_856 = x_542;
}
lean_ctor_set(x_856, 0, x_854);
lean_ctor_set(x_543, 0, x_856);
x_644 = x_543;
x_645 = x_855;
goto block_852;
}
else
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; 
x_857 = lean_ctor_get(x_853, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_853, 1);
lean_inc(x_858);
lean_dec(x_853);
if (lean_is_scalar(x_542)) {
 x_859 = lean_alloc_ctor(0, 1, 0);
} else {
 x_859 = x_542;
 lean_ctor_set_tag(x_859, 0);
}
lean_ctor_set(x_859, 0, x_857);
lean_ctor_set(x_543, 0, x_859);
x_644 = x_543;
x_645 = x_858;
goto block_852;
}
block_643:
{
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_551 = lean_ctor_get(x_549, 1);
lean_inc(x_551);
lean_dec(x_549);
x_552 = lean_ctor_get(x_1, 5);
lean_inc(x_552);
lean_dec(x_1);
x_553 = l_Lake_elabConfigFile(x_6, x_547, x_552, x_8, x_551, x_550);
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
if (lean_obj_tag(x_554) == 0)
{
lean_object* x_555; uint8_t x_556; 
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
x_556 = !lean_is_exclusive(x_554);
if (x_556 == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_554, 0);
x_558 = lean_ctor_get(x_554, 1);
lean_inc(x_557);
x_559 = lean_write_module(x_557, x_20, x_555);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_559, 1);
lean_inc(x_560);
lean_dec(x_559);
x_561 = lean_io_prim_handle_unlock(x_546, x_560);
lean_dec(x_546);
if (lean_obj_tag(x_561) == 0)
{
uint8_t x_562; 
x_562 = !lean_is_exclusive(x_561);
if (x_562 == 0)
{
lean_object* x_563; 
x_563 = lean_ctor_get(x_561, 0);
lean_dec(x_563);
lean_ctor_set(x_561, 0, x_554);
return x_561;
}
else
{
lean_object* x_564; lean_object* x_565; 
x_564 = lean_ctor_get(x_561, 1);
lean_inc(x_564);
lean_dec(x_561);
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_554);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
else
{
uint8_t x_566; 
lean_dec(x_557);
x_566 = !lean_is_exclusive(x_561);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_567 = lean_ctor_get(x_561, 0);
x_568 = lean_io_error_to_string(x_567);
x_569 = 3;
x_570 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set_uint8(x_570, sizeof(void*)*1, x_569);
x_571 = lean_array_get_size(x_558);
x_572 = lean_array_push(x_558, x_570);
lean_ctor_set_tag(x_554, 1);
lean_ctor_set(x_554, 1, x_572);
lean_ctor_set(x_554, 0, x_571);
lean_ctor_set_tag(x_561, 0);
lean_ctor_set(x_561, 0, x_554);
return x_561;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_573 = lean_ctor_get(x_561, 0);
x_574 = lean_ctor_get(x_561, 1);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_561);
x_575 = lean_io_error_to_string(x_573);
x_576 = 3;
x_577 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_577, 0, x_575);
lean_ctor_set_uint8(x_577, sizeof(void*)*1, x_576);
x_578 = lean_array_get_size(x_558);
x_579 = lean_array_push(x_558, x_577);
lean_ctor_set_tag(x_554, 1);
lean_ctor_set(x_554, 1, x_579);
lean_ctor_set(x_554, 0, x_578);
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_554);
lean_ctor_set(x_580, 1, x_574);
return x_580;
}
}
}
else
{
uint8_t x_581; 
lean_dec(x_557);
lean_dec(x_546);
x_581 = !lean_is_exclusive(x_559);
if (x_581 == 0)
{
lean_object* x_582; lean_object* x_583; uint8_t x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_582 = lean_ctor_get(x_559, 0);
x_583 = lean_io_error_to_string(x_582);
x_584 = 3;
x_585 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set_uint8(x_585, sizeof(void*)*1, x_584);
x_586 = lean_array_get_size(x_558);
x_587 = lean_array_push(x_558, x_585);
lean_ctor_set_tag(x_554, 1);
lean_ctor_set(x_554, 1, x_587);
lean_ctor_set(x_554, 0, x_586);
lean_ctor_set_tag(x_559, 0);
lean_ctor_set(x_559, 0, x_554);
return x_559;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_588 = lean_ctor_get(x_559, 0);
x_589 = lean_ctor_get(x_559, 1);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_559);
x_590 = lean_io_error_to_string(x_588);
x_591 = 3;
x_592 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set_uint8(x_592, sizeof(void*)*1, x_591);
x_593 = lean_array_get_size(x_558);
x_594 = lean_array_push(x_558, x_592);
lean_ctor_set_tag(x_554, 1);
lean_ctor_set(x_554, 1, x_594);
lean_ctor_set(x_554, 0, x_593);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_554);
lean_ctor_set(x_595, 1, x_589);
return x_595;
}
}
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_554, 0);
x_597 = lean_ctor_get(x_554, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_554);
lean_inc(x_596);
x_598 = lean_write_module(x_596, x_20, x_555);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; 
x_599 = lean_ctor_get(x_598, 1);
lean_inc(x_599);
lean_dec(x_598);
x_600 = lean_io_prim_handle_unlock(x_546, x_599);
lean_dec(x_546);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_601 = lean_ctor_get(x_600, 1);
lean_inc(x_601);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_602 = x_600;
} else {
 lean_dec_ref(x_600);
 x_602 = lean_box(0);
}
x_603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_603, 0, x_596);
lean_ctor_set(x_603, 1, x_597);
if (lean_is_scalar(x_602)) {
 x_604 = lean_alloc_ctor(0, 2, 0);
} else {
 x_604 = x_602;
}
lean_ctor_set(x_604, 0, x_603);
lean_ctor_set(x_604, 1, x_601);
return x_604;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; uint8_t x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_dec(x_596);
x_605 = lean_ctor_get(x_600, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_600, 1);
lean_inc(x_606);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 x_607 = x_600;
} else {
 lean_dec_ref(x_600);
 x_607 = lean_box(0);
}
x_608 = lean_io_error_to_string(x_605);
x_609 = 3;
x_610 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_610, 0, x_608);
lean_ctor_set_uint8(x_610, sizeof(void*)*1, x_609);
x_611 = lean_array_get_size(x_597);
x_612 = lean_array_push(x_597, x_610);
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_611);
lean_ctor_set(x_613, 1, x_612);
if (lean_is_scalar(x_607)) {
 x_614 = lean_alloc_ctor(0, 2, 0);
} else {
 x_614 = x_607;
 lean_ctor_set_tag(x_614, 0);
}
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_606);
return x_614;
}
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_596);
lean_dec(x_546);
x_615 = lean_ctor_get(x_598, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_598, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 x_617 = x_598;
} else {
 lean_dec_ref(x_598);
 x_617 = lean_box(0);
}
x_618 = lean_io_error_to_string(x_615);
x_619 = 3;
x_620 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set_uint8(x_620, sizeof(void*)*1, x_619);
x_621 = lean_array_get_size(x_597);
x_622 = lean_array_push(x_597, x_620);
x_623 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_623, 0, x_621);
lean_ctor_set(x_623, 1, x_622);
if (lean_is_scalar(x_617)) {
 x_624 = lean_alloc_ctor(0, 2, 0);
} else {
 x_624 = x_617;
 lean_ctor_set_tag(x_624, 0);
}
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_616);
return x_624;
}
}
}
else
{
uint8_t x_625; 
lean_dec(x_546);
lean_dec(x_20);
x_625 = !lean_is_exclusive(x_553);
if (x_625 == 0)
{
lean_object* x_626; uint8_t x_627; 
x_626 = lean_ctor_get(x_553, 0);
lean_dec(x_626);
x_627 = !lean_is_exclusive(x_554);
if (x_627 == 0)
{
return x_553;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_554, 0);
x_629 = lean_ctor_get(x_554, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_554);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
lean_ctor_set(x_553, 0, x_630);
return x_553;
}
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_631 = lean_ctor_get(x_553, 1);
lean_inc(x_631);
lean_dec(x_553);
x_632 = lean_ctor_get(x_554, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_554, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 x_634 = x_554;
} else {
 lean_dec_ref(x_554);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_634)) {
 x_635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_635 = x_634;
}
lean_ctor_set(x_635, 0, x_632);
lean_ctor_set(x_635, 1, x_633);
x_636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_631);
return x_636;
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_637 = !lean_is_exclusive(x_549);
if (x_637 == 0)
{
lean_object* x_638; 
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_549);
lean_ctor_set(x_638, 1, x_550);
return x_638;
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_639 = lean_ctor_get(x_549, 0);
x_640 = lean_ctor_get(x_549, 1);
lean_inc(x_640);
lean_inc(x_639);
lean_dec(x_549);
x_641 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_641, 0, x_639);
lean_ctor_set(x_641, 1, x_640);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_550);
return x_642;
}
}
}
block_852:
{
lean_object* x_646; 
x_646 = lean_ctor_get(x_644, 0);
lean_inc(x_646);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; 
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
lean_dec(x_646);
if (lean_obj_tag(x_647) == 11)
{
uint8_t x_648; 
lean_dec(x_647);
lean_dec(x_23);
x_648 = !lean_is_exclusive(x_644);
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_649 = lean_ctor_get(x_644, 1);
x_650 = lean_ctor_get(x_644, 0);
lean_dec(x_650);
x_651 = lean_ctor_get(x_1, 0);
lean_inc(x_651);
x_652 = l_Lake_Env_leanGithash(x_651);
lean_dec(x_651);
x_653 = l_System_Platform_target;
lean_inc(x_547);
if (lean_is_scalar(x_548)) {
 x_654 = lean_alloc_ctor(0, 4, 0);
} else {
 x_654 = x_548;
}
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_652);
lean_ctor_set(x_654, 2, x_29);
lean_ctor_set(x_654, 3, x_547);
x_655 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_654);
x_656 = lean_unsigned_to_nat(80u);
x_657 = l_Lean_Json_pretty(x_655, x_656);
x_658 = l_IO_FS_Handle_putStrLn(x_546, x_657, x_645);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; 
x_659 = lean_ctor_get(x_658, 1);
lean_inc(x_659);
lean_dec(x_658);
x_660 = lean_io_prim_handle_truncate(x_546, x_659);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
lean_dec(x_660);
lean_ctor_set(x_644, 0, x_661);
x_549 = x_644;
x_550 = x_662;
goto block_643;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; uint8_t x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_663 = lean_ctor_get(x_660, 0);
lean_inc(x_663);
x_664 = lean_ctor_get(x_660, 1);
lean_inc(x_664);
lean_dec(x_660);
x_665 = lean_io_error_to_string(x_663);
x_666 = 3;
x_667 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_667, 0, x_665);
lean_ctor_set_uint8(x_667, sizeof(void*)*1, x_666);
x_668 = lean_array_get_size(x_649);
x_669 = lean_array_push(x_649, x_667);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_669);
lean_ctor_set(x_644, 0, x_668);
x_549 = x_644;
x_550 = x_664;
goto block_643;
}
}
else
{
uint8_t x_670; 
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_670 = !lean_is_exclusive(x_658);
if (x_670 == 0)
{
lean_object* x_671; lean_object* x_672; uint8_t x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_671 = lean_ctor_get(x_658, 0);
x_672 = lean_io_error_to_string(x_671);
x_673 = 3;
x_674 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_674, 0, x_672);
lean_ctor_set_uint8(x_674, sizeof(void*)*1, x_673);
x_675 = lean_array_get_size(x_649);
x_676 = lean_array_push(x_649, x_674);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_676);
lean_ctor_set(x_644, 0, x_675);
lean_ctor_set_tag(x_658, 0);
lean_ctor_set(x_658, 0, x_644);
return x_658;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_677 = lean_ctor_get(x_658, 0);
x_678 = lean_ctor_get(x_658, 1);
lean_inc(x_678);
lean_inc(x_677);
lean_dec(x_658);
x_679 = lean_io_error_to_string(x_677);
x_680 = 3;
x_681 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_681, 0, x_679);
lean_ctor_set_uint8(x_681, sizeof(void*)*1, x_680);
x_682 = lean_array_get_size(x_649);
x_683 = lean_array_push(x_649, x_681);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_683);
lean_ctor_set(x_644, 0, x_682);
x_684 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_684, 0, x_644);
lean_ctor_set(x_684, 1, x_678);
return x_684;
}
}
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_685 = lean_ctor_get(x_644, 1);
lean_inc(x_685);
lean_dec(x_644);
x_686 = lean_ctor_get(x_1, 0);
lean_inc(x_686);
x_687 = l_Lake_Env_leanGithash(x_686);
lean_dec(x_686);
x_688 = l_System_Platform_target;
lean_inc(x_547);
if (lean_is_scalar(x_548)) {
 x_689 = lean_alloc_ctor(0, 4, 0);
} else {
 x_689 = x_548;
}
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_687);
lean_ctor_set(x_689, 2, x_29);
lean_ctor_set(x_689, 3, x_547);
x_690 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_689);
x_691 = lean_unsigned_to_nat(80u);
x_692 = l_Lean_Json_pretty(x_690, x_691);
x_693 = l_IO_FS_Handle_putStrLn(x_546, x_692, x_645);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; 
x_694 = lean_ctor_get(x_693, 1);
lean_inc(x_694);
lean_dec(x_693);
x_695 = lean_io_prim_handle_truncate(x_546, x_694);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_685);
x_549 = x_698;
x_550 = x_697;
goto block_643;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_699 = lean_ctor_get(x_695, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_695, 1);
lean_inc(x_700);
lean_dec(x_695);
x_701 = lean_io_error_to_string(x_699);
x_702 = 3;
x_703 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set_uint8(x_703, sizeof(void*)*1, x_702);
x_704 = lean_array_get_size(x_685);
x_705 = lean_array_push(x_685, x_703);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
x_549 = x_706;
x_550 = x_700;
goto block_643;
}
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; uint8_t x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_707 = lean_ctor_get(x_693, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_693, 1);
lean_inc(x_708);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_709 = x_693;
} else {
 lean_dec_ref(x_693);
 x_709 = lean_box(0);
}
x_710 = lean_io_error_to_string(x_707);
x_711 = 3;
x_712 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_712, 0, x_710);
lean_ctor_set_uint8(x_712, sizeof(void*)*1, x_711);
x_713 = lean_array_get_size(x_685);
x_714 = lean_array_push(x_685, x_712);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
if (lean_is_scalar(x_709)) {
 x_716 = lean_alloc_ctor(0, 2, 0);
} else {
 x_716 = x_709;
 lean_ctor_set_tag(x_716, 0);
}
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_708);
return x_716;
}
}
}
else
{
uint8_t x_717; 
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_717 = !lean_is_exclusive(x_644);
if (x_717 == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_718 = lean_ctor_get(x_644, 1);
x_719 = lean_ctor_get(x_644, 0);
lean_dec(x_719);
x_720 = lean_io_error_to_string(x_647);
x_721 = 3;
x_722 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_722, 0, x_720);
lean_ctor_set_uint8(x_722, sizeof(void*)*1, x_721);
x_723 = lean_array_get_size(x_718);
x_724 = lean_array_push(x_718, x_722);
x_725 = lean_io_prim_handle_unlock(x_546, x_645);
lean_dec(x_546);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; 
x_726 = lean_ctor_get(x_725, 1);
lean_inc(x_726);
lean_dec(x_725);
x_727 = lean_io_remove_file(x_23, x_726);
lean_dec(x_23);
if (lean_obj_tag(x_727) == 0)
{
uint8_t x_728; 
x_728 = !lean_is_exclusive(x_727);
if (x_728 == 0)
{
lean_object* x_729; 
x_729 = lean_ctor_get(x_727, 0);
lean_dec(x_729);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_724);
lean_ctor_set(x_644, 0, x_723);
lean_ctor_set(x_727, 0, x_644);
return x_727;
}
else
{
lean_object* x_730; lean_object* x_731; 
x_730 = lean_ctor_get(x_727, 1);
lean_inc(x_730);
lean_dec(x_727);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_724);
lean_ctor_set(x_644, 0, x_723);
x_731 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_731, 0, x_644);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
else
{
uint8_t x_732; 
x_732 = !lean_is_exclusive(x_727);
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_733 = lean_ctor_get(x_727, 0);
x_734 = lean_io_error_to_string(x_733);
x_735 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_735, 0, x_734);
lean_ctor_set_uint8(x_735, sizeof(void*)*1, x_721);
x_736 = lean_array_push(x_724, x_735);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_736);
lean_ctor_set(x_644, 0, x_723);
lean_ctor_set_tag(x_727, 0);
lean_ctor_set(x_727, 0, x_644);
return x_727;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_737 = lean_ctor_get(x_727, 0);
x_738 = lean_ctor_get(x_727, 1);
lean_inc(x_738);
lean_inc(x_737);
lean_dec(x_727);
x_739 = lean_io_error_to_string(x_737);
x_740 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set_uint8(x_740, sizeof(void*)*1, x_721);
x_741 = lean_array_push(x_724, x_740);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_741);
lean_ctor_set(x_644, 0, x_723);
x_742 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_742, 0, x_644);
lean_ctor_set(x_742, 1, x_738);
return x_742;
}
}
}
else
{
uint8_t x_743; 
lean_dec(x_23);
x_743 = !lean_is_exclusive(x_725);
if (x_743 == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_744 = lean_ctor_get(x_725, 0);
x_745 = lean_io_error_to_string(x_744);
x_746 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set_uint8(x_746, sizeof(void*)*1, x_721);
x_747 = lean_array_push(x_724, x_746);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_747);
lean_ctor_set(x_644, 0, x_723);
lean_ctor_set_tag(x_725, 0);
lean_ctor_set(x_725, 0, x_644);
return x_725;
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_748 = lean_ctor_get(x_725, 0);
x_749 = lean_ctor_get(x_725, 1);
lean_inc(x_749);
lean_inc(x_748);
lean_dec(x_725);
x_750 = lean_io_error_to_string(x_748);
x_751 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_751, 0, x_750);
lean_ctor_set_uint8(x_751, sizeof(void*)*1, x_721);
x_752 = lean_array_push(x_724, x_751);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_752);
lean_ctor_set(x_644, 0, x_723);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_644);
lean_ctor_set(x_753, 1, x_749);
return x_753;
}
}
}
else
{
lean_object* x_754; lean_object* x_755; uint8_t x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_754 = lean_ctor_get(x_644, 1);
lean_inc(x_754);
lean_dec(x_644);
x_755 = lean_io_error_to_string(x_647);
x_756 = 3;
x_757 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set_uint8(x_757, sizeof(void*)*1, x_756);
x_758 = lean_array_get_size(x_754);
x_759 = lean_array_push(x_754, x_757);
x_760 = lean_io_prim_handle_unlock(x_546, x_645);
lean_dec(x_546);
if (lean_obj_tag(x_760) == 0)
{
lean_object* x_761; lean_object* x_762; 
x_761 = lean_ctor_get(x_760, 1);
lean_inc(x_761);
lean_dec(x_760);
x_762 = lean_io_remove_file(x_23, x_761);
lean_dec(x_23);
if (lean_obj_tag(x_762) == 0)
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_763 = lean_ctor_get(x_762, 1);
lean_inc(x_763);
if (lean_is_exclusive(x_762)) {
 lean_ctor_release(x_762, 0);
 lean_ctor_release(x_762, 1);
 x_764 = x_762;
} else {
 lean_dec_ref(x_762);
 x_764 = lean_box(0);
}
x_765 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_765, 0, x_758);
lean_ctor_set(x_765, 1, x_759);
if (lean_is_scalar(x_764)) {
 x_766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_766 = x_764;
}
lean_ctor_set(x_766, 0, x_765);
lean_ctor_set(x_766, 1, x_763);
return x_766;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_767 = lean_ctor_get(x_762, 0);
lean_inc(x_767);
x_768 = lean_ctor_get(x_762, 1);
lean_inc(x_768);
if (lean_is_exclusive(x_762)) {
 lean_ctor_release(x_762, 0);
 lean_ctor_release(x_762, 1);
 x_769 = x_762;
} else {
 lean_dec_ref(x_762);
 x_769 = lean_box(0);
}
x_770 = lean_io_error_to_string(x_767);
x_771 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_771, 0, x_770);
lean_ctor_set_uint8(x_771, sizeof(void*)*1, x_756);
x_772 = lean_array_push(x_759, x_771);
x_773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_773, 0, x_758);
lean_ctor_set(x_773, 1, x_772);
if (lean_is_scalar(x_769)) {
 x_774 = lean_alloc_ctor(0, 2, 0);
} else {
 x_774 = x_769;
 lean_ctor_set_tag(x_774, 0);
}
lean_ctor_set(x_774, 0, x_773);
lean_ctor_set(x_774, 1, x_768);
return x_774;
}
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
lean_dec(x_23);
x_775 = lean_ctor_get(x_760, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_760, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 lean_ctor_release(x_760, 1);
 x_777 = x_760;
} else {
 lean_dec_ref(x_760);
 x_777 = lean_box(0);
}
x_778 = lean_io_error_to_string(x_775);
x_779 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_779, 0, x_778);
lean_ctor_set_uint8(x_779, sizeof(void*)*1, x_756);
x_780 = lean_array_push(x_759, x_779);
x_781 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_781, 0, x_758);
lean_ctor_set(x_781, 1, x_780);
if (lean_is_scalar(x_777)) {
 x_782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_782 = x_777;
 lean_ctor_set_tag(x_782, 0);
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_776);
return x_782;
}
}
}
}
else
{
uint8_t x_783; 
lean_dec(x_646);
lean_dec(x_23);
x_783 = !lean_is_exclusive(x_644);
if (x_783 == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_784 = lean_ctor_get(x_644, 1);
x_785 = lean_ctor_get(x_644, 0);
lean_dec(x_785);
x_786 = lean_ctor_get(x_1, 0);
lean_inc(x_786);
x_787 = l_Lake_Env_leanGithash(x_786);
lean_dec(x_786);
x_788 = l_System_Platform_target;
lean_inc(x_547);
if (lean_is_scalar(x_548)) {
 x_789 = lean_alloc_ctor(0, 4, 0);
} else {
 x_789 = x_548;
}
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_789, 1, x_787);
lean_ctor_set(x_789, 2, x_29);
lean_ctor_set(x_789, 3, x_547);
x_790 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_789);
x_791 = lean_unsigned_to_nat(80u);
x_792 = l_Lean_Json_pretty(x_790, x_791);
x_793 = l_IO_FS_Handle_putStrLn(x_546, x_792, x_645);
if (lean_obj_tag(x_793) == 0)
{
lean_object* x_794; lean_object* x_795; 
x_794 = lean_ctor_get(x_793, 1);
lean_inc(x_794);
lean_dec(x_793);
x_795 = lean_io_prim_handle_truncate(x_546, x_794);
if (lean_obj_tag(x_795) == 0)
{
lean_object* x_796; lean_object* x_797; 
x_796 = lean_ctor_get(x_795, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_795, 1);
lean_inc(x_797);
lean_dec(x_795);
lean_ctor_set(x_644, 0, x_796);
x_549 = x_644;
x_550 = x_797;
goto block_643;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; uint8_t x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_798 = lean_ctor_get(x_795, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_795, 1);
lean_inc(x_799);
lean_dec(x_795);
x_800 = lean_io_error_to_string(x_798);
x_801 = 3;
x_802 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_802, 0, x_800);
lean_ctor_set_uint8(x_802, sizeof(void*)*1, x_801);
x_803 = lean_array_get_size(x_784);
x_804 = lean_array_push(x_784, x_802);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_804);
lean_ctor_set(x_644, 0, x_803);
x_549 = x_644;
x_550 = x_799;
goto block_643;
}
}
else
{
uint8_t x_805; 
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_805 = !lean_is_exclusive(x_793);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; uint8_t x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_806 = lean_ctor_get(x_793, 0);
x_807 = lean_io_error_to_string(x_806);
x_808 = 3;
x_809 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_809, 0, x_807);
lean_ctor_set_uint8(x_809, sizeof(void*)*1, x_808);
x_810 = lean_array_get_size(x_784);
x_811 = lean_array_push(x_784, x_809);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_811);
lean_ctor_set(x_644, 0, x_810);
lean_ctor_set_tag(x_793, 0);
lean_ctor_set(x_793, 0, x_644);
return x_793;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_812 = lean_ctor_get(x_793, 0);
x_813 = lean_ctor_get(x_793, 1);
lean_inc(x_813);
lean_inc(x_812);
lean_dec(x_793);
x_814 = lean_io_error_to_string(x_812);
x_815 = 3;
x_816 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_816, 0, x_814);
lean_ctor_set_uint8(x_816, sizeof(void*)*1, x_815);
x_817 = lean_array_get_size(x_784);
x_818 = lean_array_push(x_784, x_816);
lean_ctor_set_tag(x_644, 1);
lean_ctor_set(x_644, 1, x_818);
lean_ctor_set(x_644, 0, x_817);
x_819 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_819, 0, x_644);
lean_ctor_set(x_819, 1, x_813);
return x_819;
}
}
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_820 = lean_ctor_get(x_644, 1);
lean_inc(x_820);
lean_dec(x_644);
x_821 = lean_ctor_get(x_1, 0);
lean_inc(x_821);
x_822 = l_Lake_Env_leanGithash(x_821);
lean_dec(x_821);
x_823 = l_System_Platform_target;
lean_inc(x_547);
if (lean_is_scalar(x_548)) {
 x_824 = lean_alloc_ctor(0, 4, 0);
} else {
 x_824 = x_548;
}
lean_ctor_set(x_824, 0, x_823);
lean_ctor_set(x_824, 1, x_822);
lean_ctor_set(x_824, 2, x_29);
lean_ctor_set(x_824, 3, x_547);
x_825 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_824);
x_826 = lean_unsigned_to_nat(80u);
x_827 = l_Lean_Json_pretty(x_825, x_826);
x_828 = l_IO_FS_Handle_putStrLn(x_546, x_827, x_645);
if (lean_obj_tag(x_828) == 0)
{
lean_object* x_829; lean_object* x_830; 
x_829 = lean_ctor_get(x_828, 1);
lean_inc(x_829);
lean_dec(x_828);
x_830 = lean_io_prim_handle_truncate(x_546, x_829);
if (lean_obj_tag(x_830) == 0)
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_831 = lean_ctor_get(x_830, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_830, 1);
lean_inc(x_832);
lean_dec(x_830);
x_833 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_833, 0, x_831);
lean_ctor_set(x_833, 1, x_820);
x_549 = x_833;
x_550 = x_832;
goto block_643;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; uint8_t x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_834 = lean_ctor_get(x_830, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_830, 1);
lean_inc(x_835);
lean_dec(x_830);
x_836 = lean_io_error_to_string(x_834);
x_837 = 3;
x_838 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_838, 0, x_836);
lean_ctor_set_uint8(x_838, sizeof(void*)*1, x_837);
x_839 = lean_array_get_size(x_820);
x_840 = lean_array_push(x_820, x_838);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
x_549 = x_841;
x_550 = x_835;
goto block_643;
}
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; uint8_t x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_842 = lean_ctor_get(x_828, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_828, 1);
lean_inc(x_843);
if (lean_is_exclusive(x_828)) {
 lean_ctor_release(x_828, 0);
 lean_ctor_release(x_828, 1);
 x_844 = x_828;
} else {
 lean_dec_ref(x_828);
 x_844 = lean_box(0);
}
x_845 = lean_io_error_to_string(x_842);
x_846 = 3;
x_847 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set_uint8(x_847, sizeof(void*)*1, x_846);
x_848 = lean_array_get_size(x_820);
x_849 = lean_array_push(x_820, x_847);
x_850 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_849);
if (lean_is_scalar(x_844)) {
 x_851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_851 = x_844;
 lean_ctor_set_tag(x_851, 0);
}
lean_ctor_set(x_851, 0, x_850);
lean_ctor_set(x_851, 1, x_843);
return x_851;
}
}
}
}
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_914; lean_object* x_915; lean_object* x_1015; 
x_860 = lean_ctor_get(x_543, 0);
x_861 = lean_ctor_get(x_543, 1);
lean_inc(x_861);
lean_inc(x_860);
lean_dec(x_543);
x_862 = lean_ctor_get(x_541, 3);
lean_inc(x_862);
if (lean_is_exclusive(x_541)) {
 lean_ctor_release(x_541, 0);
 lean_ctor_release(x_541, 1);
 lean_ctor_release(x_541, 2);
 lean_ctor_release(x_541, 3);
 x_863 = x_541;
} else {
 lean_dec_ref(x_541);
 x_863 = lean_box(0);
}
x_1015 = lean_io_remove_file(x_20, x_544);
if (lean_obj_tag(x_1015) == 0)
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1015, 1);
lean_inc(x_1017);
lean_dec(x_1015);
if (lean_is_scalar(x_542)) {
 x_1018 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1018 = x_542;
}
lean_ctor_set(x_1018, 0, x_1016);
x_1019 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1019, 0, x_1018);
lean_ctor_set(x_1019, 1, x_861);
x_914 = x_1019;
x_915 = x_1017;
goto block_1014;
}
else
{
lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1020 = lean_ctor_get(x_1015, 0);
lean_inc(x_1020);
x_1021 = lean_ctor_get(x_1015, 1);
lean_inc(x_1021);
lean_dec(x_1015);
if (lean_is_scalar(x_542)) {
 x_1022 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1022 = x_542;
 lean_ctor_set_tag(x_1022, 0);
}
lean_ctor_set(x_1022, 0, x_1020);
x_1023 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_861);
x_914 = x_1023;
x_915 = x_1021;
goto block_1014;
}
block_913:
{
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
x_867 = lean_ctor_get(x_1, 5);
lean_inc(x_867);
lean_dec(x_1);
x_868 = l_Lake_elabConfigFile(x_6, x_862, x_867, x_8, x_866, x_865);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; 
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = lean_ctor_get(x_869, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_869, 1);
lean_inc(x_872);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 x_873 = x_869;
} else {
 lean_dec_ref(x_869);
 x_873 = lean_box(0);
}
lean_inc(x_871);
x_874 = lean_write_module(x_871, x_20, x_870);
if (lean_obj_tag(x_874) == 0)
{
lean_object* x_875; lean_object* x_876; 
x_875 = lean_ctor_get(x_874, 1);
lean_inc(x_875);
lean_dec(x_874);
x_876 = lean_io_prim_handle_unlock(x_860, x_875);
lean_dec(x_860);
if (lean_obj_tag(x_876) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_877 = lean_ctor_get(x_876, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_878 = x_876;
} else {
 lean_dec_ref(x_876);
 x_878 = lean_box(0);
}
if (lean_is_scalar(x_873)) {
 x_879 = lean_alloc_ctor(0, 2, 0);
} else {
 x_879 = x_873;
}
lean_ctor_set(x_879, 0, x_871);
lean_ctor_set(x_879, 1, x_872);
if (lean_is_scalar(x_878)) {
 x_880 = lean_alloc_ctor(0, 2, 0);
} else {
 x_880 = x_878;
}
lean_ctor_set(x_880, 0, x_879);
lean_ctor_set(x_880, 1, x_877);
return x_880;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
lean_dec(x_871);
x_881 = lean_ctor_get(x_876, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_876, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_876)) {
 lean_ctor_release(x_876, 0);
 lean_ctor_release(x_876, 1);
 x_883 = x_876;
} else {
 lean_dec_ref(x_876);
 x_883 = lean_box(0);
}
x_884 = lean_io_error_to_string(x_881);
x_885 = 3;
x_886 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_886, 0, x_884);
lean_ctor_set_uint8(x_886, sizeof(void*)*1, x_885);
x_887 = lean_array_get_size(x_872);
x_888 = lean_array_push(x_872, x_886);
if (lean_is_scalar(x_873)) {
 x_889 = lean_alloc_ctor(1, 2, 0);
} else {
 x_889 = x_873;
 lean_ctor_set_tag(x_889, 1);
}
lean_ctor_set(x_889, 0, x_887);
lean_ctor_set(x_889, 1, x_888);
if (lean_is_scalar(x_883)) {
 x_890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_890 = x_883;
 lean_ctor_set_tag(x_890, 0);
}
lean_ctor_set(x_890, 0, x_889);
lean_ctor_set(x_890, 1, x_882);
return x_890;
}
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; uint8_t x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
lean_dec(x_871);
lean_dec(x_860);
x_891 = lean_ctor_get(x_874, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_874, 1);
lean_inc(x_892);
if (lean_is_exclusive(x_874)) {
 lean_ctor_release(x_874, 0);
 lean_ctor_release(x_874, 1);
 x_893 = x_874;
} else {
 lean_dec_ref(x_874);
 x_893 = lean_box(0);
}
x_894 = lean_io_error_to_string(x_891);
x_895 = 3;
x_896 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_896, 0, x_894);
lean_ctor_set_uint8(x_896, sizeof(void*)*1, x_895);
x_897 = lean_array_get_size(x_872);
x_898 = lean_array_push(x_872, x_896);
if (lean_is_scalar(x_873)) {
 x_899 = lean_alloc_ctor(1, 2, 0);
} else {
 x_899 = x_873;
 lean_ctor_set_tag(x_899, 1);
}
lean_ctor_set(x_899, 0, x_897);
lean_ctor_set(x_899, 1, x_898);
if (lean_is_scalar(x_893)) {
 x_900 = lean_alloc_ctor(0, 2, 0);
} else {
 x_900 = x_893;
 lean_ctor_set_tag(x_900, 0);
}
lean_ctor_set(x_900, 0, x_899);
lean_ctor_set(x_900, 1, x_892);
return x_900;
}
}
else
{
lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_860);
lean_dec(x_20);
x_901 = lean_ctor_get(x_868, 1);
lean_inc(x_901);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_902 = x_868;
} else {
 lean_dec_ref(x_868);
 x_902 = lean_box(0);
}
x_903 = lean_ctor_get(x_869, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_869, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 x_905 = x_869;
} else {
 lean_dec_ref(x_869);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_905)) {
 x_906 = lean_alloc_ctor(1, 2, 0);
} else {
 x_906 = x_905;
}
lean_ctor_set(x_906, 0, x_903);
lean_ctor_set(x_906, 1, x_904);
if (lean_is_scalar(x_902)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_902;
}
lean_ctor_set(x_907, 0, x_906);
lean_ctor_set(x_907, 1, x_901);
return x_907;
}
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; 
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_908 = lean_ctor_get(x_864, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_864, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_864)) {
 lean_ctor_release(x_864, 0);
 lean_ctor_release(x_864, 1);
 x_910 = x_864;
} else {
 lean_dec_ref(x_864);
 x_910 = lean_box(0);
}
if (lean_is_scalar(x_910)) {
 x_911 = lean_alloc_ctor(1, 2, 0);
} else {
 x_911 = x_910;
}
lean_ctor_set(x_911, 0, x_908);
lean_ctor_set(x_911, 1, x_909);
x_912 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_912, 0, x_911);
lean_ctor_set(x_912, 1, x_865);
return x_912;
}
}
block_1014:
{
lean_object* x_916; 
x_916 = lean_ctor_get(x_914, 0);
lean_inc(x_916);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; 
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
lean_dec(x_916);
if (lean_obj_tag(x_917) == 11)
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
lean_dec(x_917);
lean_dec(x_23);
x_918 = lean_ctor_get(x_914, 1);
lean_inc(x_918);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 x_919 = x_914;
} else {
 lean_dec_ref(x_914);
 x_919 = lean_box(0);
}
x_920 = lean_ctor_get(x_1, 0);
lean_inc(x_920);
x_921 = l_Lake_Env_leanGithash(x_920);
lean_dec(x_920);
x_922 = l_System_Platform_target;
lean_inc(x_862);
if (lean_is_scalar(x_863)) {
 x_923 = lean_alloc_ctor(0, 4, 0);
} else {
 x_923 = x_863;
}
lean_ctor_set(x_923, 0, x_922);
lean_ctor_set(x_923, 1, x_921);
lean_ctor_set(x_923, 2, x_29);
lean_ctor_set(x_923, 3, x_862);
x_924 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_923);
x_925 = lean_unsigned_to_nat(80u);
x_926 = l_Lean_Json_pretty(x_924, x_925);
x_927 = l_IO_FS_Handle_putStrLn(x_860, x_926, x_915);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; 
x_928 = lean_ctor_get(x_927, 1);
lean_inc(x_928);
lean_dec(x_927);
x_929 = lean_io_prim_handle_truncate(x_860, x_928);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_929, 1);
lean_inc(x_931);
lean_dec(x_929);
if (lean_is_scalar(x_919)) {
 x_932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_932 = x_919;
}
lean_ctor_set(x_932, 0, x_930);
lean_ctor_set(x_932, 1, x_918);
x_864 = x_932;
x_865 = x_931;
goto block_913;
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; uint8_t x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_933 = lean_ctor_get(x_929, 0);
lean_inc(x_933);
x_934 = lean_ctor_get(x_929, 1);
lean_inc(x_934);
lean_dec(x_929);
x_935 = lean_io_error_to_string(x_933);
x_936 = 3;
x_937 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_937, 0, x_935);
lean_ctor_set_uint8(x_937, sizeof(void*)*1, x_936);
x_938 = lean_array_get_size(x_918);
x_939 = lean_array_push(x_918, x_937);
if (lean_is_scalar(x_919)) {
 x_940 = lean_alloc_ctor(1, 2, 0);
} else {
 x_940 = x_919;
 lean_ctor_set_tag(x_940, 1);
}
lean_ctor_set(x_940, 0, x_938);
lean_ctor_set(x_940, 1, x_939);
x_864 = x_940;
x_865 = x_934;
goto block_913;
}
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; uint8_t x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; 
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_941 = lean_ctor_get(x_927, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_927, 1);
lean_inc(x_942);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 x_943 = x_927;
} else {
 lean_dec_ref(x_927);
 x_943 = lean_box(0);
}
x_944 = lean_io_error_to_string(x_941);
x_945 = 3;
x_946 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_946, 0, x_944);
lean_ctor_set_uint8(x_946, sizeof(void*)*1, x_945);
x_947 = lean_array_get_size(x_918);
x_948 = lean_array_push(x_918, x_946);
if (lean_is_scalar(x_919)) {
 x_949 = lean_alloc_ctor(1, 2, 0);
} else {
 x_949 = x_919;
 lean_ctor_set_tag(x_949, 1);
}
lean_ctor_set(x_949, 0, x_947);
lean_ctor_set(x_949, 1, x_948);
if (lean_is_scalar(x_943)) {
 x_950 = lean_alloc_ctor(0, 2, 0);
} else {
 x_950 = x_943;
 lean_ctor_set_tag(x_950, 0);
}
lean_ctor_set(x_950, 0, x_949);
lean_ctor_set(x_950, 1, x_942);
return x_950;
}
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; uint8_t x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
lean_dec(x_863);
lean_dec(x_862);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_951 = lean_ctor_get(x_914, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 x_952 = x_914;
} else {
 lean_dec_ref(x_914);
 x_952 = lean_box(0);
}
x_953 = lean_io_error_to_string(x_917);
x_954 = 3;
x_955 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_955, 0, x_953);
lean_ctor_set_uint8(x_955, sizeof(void*)*1, x_954);
x_956 = lean_array_get_size(x_951);
x_957 = lean_array_push(x_951, x_955);
x_958 = lean_io_prim_handle_unlock(x_860, x_915);
lean_dec(x_860);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; 
x_959 = lean_ctor_get(x_958, 1);
lean_inc(x_959);
lean_dec(x_958);
x_960 = lean_io_remove_file(x_23, x_959);
lean_dec(x_23);
if (lean_obj_tag(x_960) == 0)
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_961 = lean_ctor_get(x_960, 1);
lean_inc(x_961);
if (lean_is_exclusive(x_960)) {
 lean_ctor_release(x_960, 0);
 lean_ctor_release(x_960, 1);
 x_962 = x_960;
} else {
 lean_dec_ref(x_960);
 x_962 = lean_box(0);
}
if (lean_is_scalar(x_952)) {
 x_963 = lean_alloc_ctor(1, 2, 0);
} else {
 x_963 = x_952;
 lean_ctor_set_tag(x_963, 1);
}
lean_ctor_set(x_963, 0, x_956);
lean_ctor_set(x_963, 1, x_957);
if (lean_is_scalar(x_962)) {
 x_964 = lean_alloc_ctor(0, 2, 0);
} else {
 x_964 = x_962;
}
lean_ctor_set(x_964, 0, x_963);
lean_ctor_set(x_964, 1, x_961);
return x_964;
}
else
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; 
x_965 = lean_ctor_get(x_960, 0);
lean_inc(x_965);
x_966 = lean_ctor_get(x_960, 1);
lean_inc(x_966);
if (lean_is_exclusive(x_960)) {
 lean_ctor_release(x_960, 0);
 lean_ctor_release(x_960, 1);
 x_967 = x_960;
} else {
 lean_dec_ref(x_960);
 x_967 = lean_box(0);
}
x_968 = lean_io_error_to_string(x_965);
x_969 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_969, 0, x_968);
lean_ctor_set_uint8(x_969, sizeof(void*)*1, x_954);
x_970 = lean_array_push(x_957, x_969);
if (lean_is_scalar(x_952)) {
 x_971 = lean_alloc_ctor(1, 2, 0);
} else {
 x_971 = x_952;
 lean_ctor_set_tag(x_971, 1);
}
lean_ctor_set(x_971, 0, x_956);
lean_ctor_set(x_971, 1, x_970);
if (lean_is_scalar(x_967)) {
 x_972 = lean_alloc_ctor(0, 2, 0);
} else {
 x_972 = x_967;
 lean_ctor_set_tag(x_972, 0);
}
lean_ctor_set(x_972, 0, x_971);
lean_ctor_set(x_972, 1, x_966);
return x_972;
}
}
else
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
lean_dec(x_23);
x_973 = lean_ctor_get(x_958, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_958, 1);
lean_inc(x_974);
if (lean_is_exclusive(x_958)) {
 lean_ctor_release(x_958, 0);
 lean_ctor_release(x_958, 1);
 x_975 = x_958;
} else {
 lean_dec_ref(x_958);
 x_975 = lean_box(0);
}
x_976 = lean_io_error_to_string(x_973);
x_977 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_977, 0, x_976);
lean_ctor_set_uint8(x_977, sizeof(void*)*1, x_954);
x_978 = lean_array_push(x_957, x_977);
if (lean_is_scalar(x_952)) {
 x_979 = lean_alloc_ctor(1, 2, 0);
} else {
 x_979 = x_952;
 lean_ctor_set_tag(x_979, 1);
}
lean_ctor_set(x_979, 0, x_956);
lean_ctor_set(x_979, 1, x_978);
if (lean_is_scalar(x_975)) {
 x_980 = lean_alloc_ctor(0, 2, 0);
} else {
 x_980 = x_975;
 lean_ctor_set_tag(x_980, 0);
}
lean_ctor_set(x_980, 0, x_979);
lean_ctor_set(x_980, 1, x_974);
return x_980;
}
}
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; 
lean_dec(x_916);
lean_dec(x_23);
x_981 = lean_ctor_get(x_914, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_914)) {
 lean_ctor_release(x_914, 0);
 lean_ctor_release(x_914, 1);
 x_982 = x_914;
} else {
 lean_dec_ref(x_914);
 x_982 = lean_box(0);
}
x_983 = lean_ctor_get(x_1, 0);
lean_inc(x_983);
x_984 = l_Lake_Env_leanGithash(x_983);
lean_dec(x_983);
x_985 = l_System_Platform_target;
lean_inc(x_862);
if (lean_is_scalar(x_863)) {
 x_986 = lean_alloc_ctor(0, 4, 0);
} else {
 x_986 = x_863;
}
lean_ctor_set(x_986, 0, x_985);
lean_ctor_set(x_986, 1, x_984);
lean_ctor_set(x_986, 2, x_29);
lean_ctor_set(x_986, 3, x_862);
x_987 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_986);
x_988 = lean_unsigned_to_nat(80u);
x_989 = l_Lean_Json_pretty(x_987, x_988);
x_990 = l_IO_FS_Handle_putStrLn(x_860, x_989, x_915);
if (lean_obj_tag(x_990) == 0)
{
lean_object* x_991; lean_object* x_992; 
x_991 = lean_ctor_get(x_990, 1);
lean_inc(x_991);
lean_dec(x_990);
x_992 = lean_io_prim_handle_truncate(x_860, x_991);
if (lean_obj_tag(x_992) == 0)
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_993 = lean_ctor_get(x_992, 0);
lean_inc(x_993);
x_994 = lean_ctor_get(x_992, 1);
lean_inc(x_994);
lean_dec(x_992);
if (lean_is_scalar(x_982)) {
 x_995 = lean_alloc_ctor(0, 2, 0);
} else {
 x_995 = x_982;
}
lean_ctor_set(x_995, 0, x_993);
lean_ctor_set(x_995, 1, x_981);
x_864 = x_995;
x_865 = x_994;
goto block_913;
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; uint8_t x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; 
x_996 = lean_ctor_get(x_992, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_992, 1);
lean_inc(x_997);
lean_dec(x_992);
x_998 = lean_io_error_to_string(x_996);
x_999 = 3;
x_1000 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1000, 0, x_998);
lean_ctor_set_uint8(x_1000, sizeof(void*)*1, x_999);
x_1001 = lean_array_get_size(x_981);
x_1002 = lean_array_push(x_981, x_1000);
if (lean_is_scalar(x_982)) {
 x_1003 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1003 = x_982;
 lean_ctor_set_tag(x_1003, 1);
}
lean_ctor_set(x_1003, 0, x_1001);
lean_ctor_set(x_1003, 1, x_1002);
x_864 = x_1003;
x_865 = x_997;
goto block_913;
}
}
else
{
lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; uint8_t x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
lean_dec(x_862);
lean_dec(x_860);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1004 = lean_ctor_get(x_990, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_990, 1);
lean_inc(x_1005);
if (lean_is_exclusive(x_990)) {
 lean_ctor_release(x_990, 0);
 lean_ctor_release(x_990, 1);
 x_1006 = x_990;
} else {
 lean_dec_ref(x_990);
 x_1006 = lean_box(0);
}
x_1007 = lean_io_error_to_string(x_1004);
x_1008 = 3;
x_1009 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1009, 0, x_1007);
lean_ctor_set_uint8(x_1009, sizeof(void*)*1, x_1008);
x_1010 = lean_array_get_size(x_981);
x_1011 = lean_array_push(x_981, x_1009);
if (lean_is_scalar(x_982)) {
 x_1012 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1012 = x_982;
 lean_ctor_set_tag(x_1012, 1);
}
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
if (lean_is_scalar(x_1006)) {
 x_1013 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1013 = x_1006;
 lean_ctor_set_tag(x_1013, 0);
}
lean_ctor_set(x_1013, 0, x_1012);
lean_ctor_set(x_1013, 1, x_1005);
return x_1013;
}
}
}
}
}
else
{
uint8_t x_1024; 
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1024 = !lean_is_exclusive(x_543);
if (x_1024 == 0)
{
lean_object* x_1025; 
x_1025 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1025, 0, x_543);
lean_ctor_set(x_1025, 1, x_544);
return x_1025;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1026 = lean_ctor_get(x_543, 0);
x_1027 = lean_ctor_get(x_543, 1);
lean_inc(x_1027);
lean_inc(x_1026);
lean_dec(x_543);
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_1026);
lean_ctor_set(x_1028, 1, x_1027);
x_1029 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1029, 0, x_1028);
lean_ctor_set(x_1029, 1, x_544);
return x_1029;
}
}
}
block_1082:
{
lean_object* x_1035; lean_object* x_1036; uint8_t x_1044; lean_object* x_1045; 
lean_dec(x_1034);
x_1044 = 1;
x_1045 = lean_io_prim_handle_mk(x_26, x_1044, x_1033);
lean_dec(x_26);
if (lean_obj_tag(x_1045) == 0)
{
lean_object* x_1046; lean_object* x_1047; uint8_t x_1048; lean_object* x_1049; 
x_1046 = lean_ctor_get(x_1045, 0);
lean_inc(x_1046);
x_1047 = lean_ctor_get(x_1045, 1);
lean_inc(x_1047);
lean_dec(x_1045);
x_1048 = 1;
x_1049 = lean_io_prim_handle_try_lock(x_1046, x_1048, x_1047);
if (lean_obj_tag(x_1049) == 0)
{
lean_object* x_1050; uint8_t x_1051; 
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_unbox(x_1050);
lean_dec(x_1050);
if (x_1051 == 0)
{
lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_1046);
lean_dec(x_522);
x_1052 = lean_ctor_get(x_1049, 1);
lean_inc(x_1052);
lean_dec(x_1049);
x_1053 = lean_io_prim_handle_unlock(x_520, x_1052);
lean_dec(x_520);
if (lean_obj_tag(x_1053) == 0)
{
lean_object* x_1054; lean_object* x_1055; 
x_1054 = lean_ctor_get(x_1053, 1);
lean_inc(x_1054);
lean_dec(x_1053);
x_1055 = l_Lake_importConfigFile___closed__11;
x_1035 = x_1055;
x_1036 = x_1054;
goto block_1043;
}
else
{
lean_object* x_1056; lean_object* x_1057; 
x_1056 = lean_ctor_get(x_1053, 0);
lean_inc(x_1056);
x_1057 = lean_ctor_get(x_1053, 1);
lean_inc(x_1057);
lean_dec(x_1053);
x_1035 = x_1056;
x_1036 = x_1057;
goto block_1043;
}
}
else
{
lean_object* x_1058; lean_object* x_1059; 
x_1058 = lean_ctor_get(x_1049, 1);
lean_inc(x_1058);
lean_dec(x_1049);
x_1059 = lean_io_prim_handle_unlock(x_520, x_1058);
lean_dec(x_520);
if (lean_obj_tag(x_1059) == 0)
{
lean_object* x_1060; uint8_t x_1061; lean_object* x_1062; 
x_1060 = lean_ctor_get(x_1059, 1);
lean_inc(x_1060);
lean_dec(x_1059);
x_1061 = 3;
x_1062 = lean_io_prim_handle_mk(x_23, x_1061, x_1060);
if (lean_obj_tag(x_1062) == 0)
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; 
x_1063 = lean_ctor_get(x_1062, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1062, 1);
lean_inc(x_1064);
lean_dec(x_1062);
x_1065 = lean_io_prim_handle_lock(x_1063, x_1048, x_1064);
if (lean_obj_tag(x_1065) == 0)
{
lean_object* x_1066; lean_object* x_1067; 
x_1066 = lean_ctor_get(x_1065, 1);
lean_inc(x_1066);
lean_dec(x_1065);
x_1067 = lean_io_prim_handle_unlock(x_1046, x_1066);
lean_dec(x_1046);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; lean_object* x_1069; 
lean_dec(x_527);
x_1068 = lean_ctor_get(x_1067, 1);
lean_inc(x_1068);
lean_dec(x_1067);
if (lean_is_scalar(x_522)) {
 x_1069 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1069 = x_522;
}
lean_ctor_set(x_1069, 0, x_1063);
lean_ctor_set(x_1069, 1, x_526);
x_543 = x_1069;
x_544 = x_1068;
goto block_1030;
}
else
{
lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_1063);
lean_dec(x_522);
x_1070 = lean_ctor_get(x_1067, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1067, 1);
lean_inc(x_1071);
lean_dec(x_1067);
x_1035 = x_1070;
x_1036 = x_1071;
goto block_1043;
}
}
else
{
lean_object* x_1072; lean_object* x_1073; 
lean_dec(x_1063);
lean_dec(x_1046);
lean_dec(x_522);
x_1072 = lean_ctor_get(x_1065, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1065, 1);
lean_inc(x_1073);
lean_dec(x_1065);
x_1035 = x_1072;
x_1036 = x_1073;
goto block_1043;
}
}
else
{
lean_object* x_1074; lean_object* x_1075; 
lean_dec(x_1046);
lean_dec(x_522);
x_1074 = lean_ctor_get(x_1062, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1062, 1);
lean_inc(x_1075);
lean_dec(x_1062);
x_1035 = x_1074;
x_1036 = x_1075;
goto block_1043;
}
}
else
{
lean_object* x_1076; lean_object* x_1077; 
lean_dec(x_1046);
lean_dec(x_522);
x_1076 = lean_ctor_get(x_1059, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1059, 1);
lean_inc(x_1077);
lean_dec(x_1059);
x_1035 = x_1076;
x_1036 = x_1077;
goto block_1043;
}
}
}
else
{
lean_object* x_1078; lean_object* x_1079; 
lean_dec(x_1046);
lean_dec(x_522);
lean_dec(x_520);
x_1078 = lean_ctor_get(x_1049, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1049, 1);
lean_inc(x_1079);
lean_dec(x_1049);
x_1035 = x_1078;
x_1036 = x_1079;
goto block_1043;
}
}
else
{
lean_object* x_1080; lean_object* x_1081; 
lean_dec(x_522);
lean_dec(x_520);
x_1080 = lean_ctor_get(x_1045, 0);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_1045, 1);
lean_inc(x_1081);
lean_dec(x_1045);
x_1035 = x_1080;
x_1036 = x_1081;
goto block_1043;
}
block_1043:
{
lean_object* x_1037; uint8_t x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1037 = lean_io_error_to_string(x_1035);
x_1038 = 3;
x_1039 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1039, 0, x_1037);
lean_ctor_set_uint8(x_1039, sizeof(void*)*1, x_1038);
x_1040 = lean_array_get_size(x_526);
x_1041 = lean_array_push(x_526, x_1039);
if (lean_is_scalar(x_527)) {
 x_1042 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1042 = x_527;
 lean_ctor_set_tag(x_1042, 1);
}
lean_ctor_set(x_1042, 0, x_1040);
lean_ctor_set(x_1042, 1, x_1041);
x_543 = x_1042;
x_544 = x_1036;
goto block_1030;
}
}
}
}
}
else
{
uint8_t x_1144; 
lean_dec(x_522);
lean_dec(x_520);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1144 = !lean_is_exclusive(x_523);
if (x_1144 == 0)
{
lean_object* x_1145; 
x_1145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1145, 0, x_523);
lean_ctor_set(x_1145, 1, x_524);
return x_1145;
}
else
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; 
x_1146 = lean_ctor_get(x_523, 0);
x_1147 = lean_ctor_get(x_523, 1);
lean_inc(x_1147);
lean_inc(x_1146);
lean_dec(x_523);
x_1148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1148, 0, x_1146);
lean_ctor_set(x_1148, 1, x_1147);
x_1149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1149, 0, x_1148);
lean_ctor_set(x_1149, 1, x_524);
return x_1149;
}
}
}
}
else
{
uint8_t x_1232; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1232 = !lean_is_exclusive(x_518);
if (x_1232 == 0)
{
lean_object* x_1233; 
x_1233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1233, 0, x_518);
lean_ctor_set(x_1233, 1, x_519);
return x_1233;
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
x_1234 = lean_ctor_get(x_518, 0);
x_1235 = lean_ctor_get(x_518, 1);
lean_inc(x_1235);
lean_inc(x_1234);
lean_dec(x_518);
x_1236 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1236, 0, x_1234);
lean_ctor_set(x_1236, 1, x_1235);
x_1237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1237, 0, x_1236);
lean_ctor_set(x_1237, 1, x_519);
return x_1237;
}
}
}
block_1976:
{
lean_object* x_1241; 
x_1241 = lean_ctor_get(x_1239, 0);
lean_inc(x_1241);
if (lean_obj_tag(x_1241) == 0)
{
lean_object* x_1242; 
x_1242 = lean_ctor_get(x_1241, 0);
lean_inc(x_1242);
lean_dec(x_1241);
if (lean_obj_tag(x_1242) == 0)
{
uint8_t x_1243; 
lean_dec(x_1242);
x_1243 = !lean_is_exclusive(x_1239);
if (x_1243 == 0)
{
lean_object* x_1244; lean_object* x_1245; uint8_t x_1246; lean_object* x_1247; 
x_1244 = lean_ctor_get(x_1239, 1);
x_1245 = lean_ctor_get(x_1239, 0);
lean_dec(x_1245);
x_1246 = 0;
x_1247 = lean_io_prim_handle_mk(x_23, x_1246, x_1240);
if (lean_obj_tag(x_1247) == 0)
{
lean_object* x_1248; lean_object* x_1249; 
x_1248 = lean_ctor_get(x_1247, 0);
lean_inc(x_1248);
x_1249 = lean_ctor_get(x_1247, 1);
lean_inc(x_1249);
lean_dec(x_1247);
lean_ctor_set(x_1239, 0, x_1248);
x_518 = x_1239;
x_519 = x_1249;
goto block_1238;
}
else
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; uint8_t x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; 
x_1250 = lean_ctor_get(x_1247, 0);
lean_inc(x_1250);
x_1251 = lean_ctor_get(x_1247, 1);
lean_inc(x_1251);
lean_dec(x_1247);
x_1252 = lean_io_error_to_string(x_1250);
x_1253 = 3;
x_1254 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1254, 0, x_1252);
lean_ctor_set_uint8(x_1254, sizeof(void*)*1, x_1253);
x_1255 = lean_array_get_size(x_1244);
x_1256 = lean_array_push(x_1244, x_1254);
lean_ctor_set_tag(x_1239, 1);
lean_ctor_set(x_1239, 1, x_1256);
lean_ctor_set(x_1239, 0, x_1255);
x_518 = x_1239;
x_519 = x_1251;
goto block_1238;
}
}
else
{
lean_object* x_1257; uint8_t x_1258; lean_object* x_1259; 
x_1257 = lean_ctor_get(x_1239, 1);
lean_inc(x_1257);
lean_dec(x_1239);
x_1258 = 0;
x_1259 = lean_io_prim_handle_mk(x_23, x_1258, x_1240);
if (lean_obj_tag(x_1259) == 0)
{
lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1260 = lean_ctor_get(x_1259, 0);
lean_inc(x_1260);
x_1261 = lean_ctor_get(x_1259, 1);
lean_inc(x_1261);
lean_dec(x_1259);
x_1262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1262, 0, x_1260);
lean_ctor_set(x_1262, 1, x_1257);
x_518 = x_1262;
x_519 = x_1261;
goto block_1238;
}
else
{
lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; uint8_t x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
x_1263 = lean_ctor_get(x_1259, 0);
lean_inc(x_1263);
x_1264 = lean_ctor_get(x_1259, 1);
lean_inc(x_1264);
lean_dec(x_1259);
x_1265 = lean_io_error_to_string(x_1263);
x_1266 = 3;
x_1267 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1267, 0, x_1265);
lean_ctor_set_uint8(x_1267, sizeof(void*)*1, x_1266);
x_1268 = lean_array_get_size(x_1257);
x_1269 = lean_array_push(x_1257, x_1267);
x_1270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1270, 0, x_1268);
lean_ctor_set(x_1270, 1, x_1269);
x_518 = x_1270;
x_519 = x_1264;
goto block_1238;
}
}
}
else
{
uint8_t x_1271; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1271 = !lean_is_exclusive(x_1239);
if (x_1271 == 0)
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; uint8_t x_1275; lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; 
x_1272 = lean_ctor_get(x_1239, 1);
x_1273 = lean_ctor_get(x_1239, 0);
lean_dec(x_1273);
x_1274 = lean_io_error_to_string(x_1242);
x_1275 = 3;
x_1276 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1276, 0, x_1274);
lean_ctor_set_uint8(x_1276, sizeof(void*)*1, x_1275);
x_1277 = lean_array_get_size(x_1272);
x_1278 = lean_array_push(x_1272, x_1276);
lean_ctor_set_tag(x_1239, 1);
lean_ctor_set(x_1239, 1, x_1278);
lean_ctor_set(x_1239, 0, x_1277);
x_1279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1279, 0, x_1239);
lean_ctor_set(x_1279, 1, x_1240);
return x_1279;
}
else
{
lean_object* x_1280; lean_object* x_1281; uint8_t x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1280 = lean_ctor_get(x_1239, 1);
lean_inc(x_1280);
lean_dec(x_1239);
x_1281 = lean_io_error_to_string(x_1242);
x_1282 = 3;
x_1283 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1283, 0, x_1281);
lean_ctor_set_uint8(x_1283, sizeof(void*)*1, x_1282);
x_1284 = lean_array_get_size(x_1280);
x_1285 = lean_array_push(x_1280, x_1283);
x_1286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1286, 0, x_1284);
lean_ctor_set(x_1286, 1, x_1285);
x_1287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1287, 0, x_1286);
lean_ctor_set(x_1287, 1, x_1240);
return x_1287;
}
}
}
else
{
uint8_t x_1288; 
lean_dec(x_31);
lean_dec(x_26);
x_1288 = !lean_is_exclusive(x_1239);
if (x_1288 == 0)
{
lean_object* x_1289; lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; uint8_t x_1778; lean_object* x_1779; 
x_1289 = lean_ctor_get(x_1239, 1);
x_1290 = lean_ctor_get(x_1239, 0);
lean_dec(x_1290);
x_1291 = lean_ctor_get(x_1241, 0);
lean_inc(x_1291);
if (lean_is_exclusive(x_1241)) {
 lean_ctor_release(x_1241, 0);
 x_1292 = x_1241;
} else {
 lean_dec_ref(x_1241);
 x_1292 = lean_box(0);
}
x_1778 = 1;
x_1779 = lean_io_prim_handle_lock(x_1291, x_1778, x_1240);
if (lean_obj_tag(x_1779) == 0)
{
lean_object* x_1780; lean_object* x_1781; 
x_1780 = lean_ctor_get(x_1779, 0);
lean_inc(x_1780);
x_1781 = lean_ctor_get(x_1779, 1);
lean_inc(x_1781);
lean_dec(x_1779);
lean_ctor_set(x_1239, 0, x_1780);
x_1293 = x_1239;
x_1294 = x_1781;
goto block_1777;
}
else
{
lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; uint8_t x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; 
x_1782 = lean_ctor_get(x_1779, 0);
lean_inc(x_1782);
x_1783 = lean_ctor_get(x_1779, 1);
lean_inc(x_1783);
lean_dec(x_1779);
x_1784 = lean_io_error_to_string(x_1782);
x_1785 = 3;
x_1786 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1786, 0, x_1784);
lean_ctor_set_uint8(x_1786, sizeof(void*)*1, x_1785);
x_1787 = lean_array_get_size(x_1289);
x_1788 = lean_array_push(x_1289, x_1786);
lean_ctor_set_tag(x_1239, 1);
lean_ctor_set(x_1239, 1, x_1788);
lean_ctor_set(x_1239, 0, x_1787);
x_1293 = x_1239;
x_1294 = x_1783;
goto block_1777;
}
block_1777:
{
if (lean_obj_tag(x_1293) == 0)
{
uint8_t x_1295; 
x_1295 = !lean_is_exclusive(x_1293);
if (x_1295 == 0)
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1393; lean_object* x_1394; lean_object* x_1602; 
x_1296 = lean_ctor_get(x_1293, 0);
lean_dec(x_1296);
x_1297 = lean_ctor_get(x_1, 4);
lean_inc(x_1297);
x_1602 = lean_io_remove_file(x_20, x_1294);
if (lean_obj_tag(x_1602) == 0)
{
lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; 
x_1603 = lean_ctor_get(x_1602, 0);
lean_inc(x_1603);
x_1604 = lean_ctor_get(x_1602, 1);
lean_inc(x_1604);
lean_dec(x_1602);
if (lean_is_scalar(x_1292)) {
 x_1605 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1605 = x_1292;
}
lean_ctor_set(x_1605, 0, x_1603);
lean_ctor_set(x_1293, 0, x_1605);
x_1393 = x_1293;
x_1394 = x_1604;
goto block_1601;
}
else
{
lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; 
x_1606 = lean_ctor_get(x_1602, 0);
lean_inc(x_1606);
x_1607 = lean_ctor_get(x_1602, 1);
lean_inc(x_1607);
lean_dec(x_1602);
if (lean_is_scalar(x_1292)) {
 x_1608 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1608 = x_1292;
 lean_ctor_set_tag(x_1608, 0);
}
lean_ctor_set(x_1608, 0, x_1606);
lean_ctor_set(x_1293, 0, x_1608);
x_1393 = x_1293;
x_1394 = x_1607;
goto block_1601;
}
block_1392:
{
if (lean_obj_tag(x_1298) == 0)
{
lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1300 = lean_ctor_get(x_1298, 1);
lean_inc(x_1300);
lean_dec(x_1298);
x_1301 = lean_ctor_get(x_1, 5);
lean_inc(x_1301);
lean_dec(x_1);
x_1302 = l_Lake_elabConfigFile(x_6, x_1297, x_1301, x_8, x_1300, x_1299);
x_1303 = lean_ctor_get(x_1302, 0);
lean_inc(x_1303);
if (lean_obj_tag(x_1303) == 0)
{
lean_object* x_1304; uint8_t x_1305; 
x_1304 = lean_ctor_get(x_1302, 1);
lean_inc(x_1304);
lean_dec(x_1302);
x_1305 = !lean_is_exclusive(x_1303);
if (x_1305 == 0)
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; 
x_1306 = lean_ctor_get(x_1303, 0);
x_1307 = lean_ctor_get(x_1303, 1);
lean_inc(x_1306);
x_1308 = lean_write_module(x_1306, x_20, x_1304);
if (lean_obj_tag(x_1308) == 0)
{
lean_object* x_1309; lean_object* x_1310; 
x_1309 = lean_ctor_get(x_1308, 1);
lean_inc(x_1309);
lean_dec(x_1308);
x_1310 = lean_io_prim_handle_unlock(x_1291, x_1309);
lean_dec(x_1291);
if (lean_obj_tag(x_1310) == 0)
{
uint8_t x_1311; 
x_1311 = !lean_is_exclusive(x_1310);
if (x_1311 == 0)
{
lean_object* x_1312; 
x_1312 = lean_ctor_get(x_1310, 0);
lean_dec(x_1312);
lean_ctor_set(x_1310, 0, x_1303);
return x_1310;
}
else
{
lean_object* x_1313; lean_object* x_1314; 
x_1313 = lean_ctor_get(x_1310, 1);
lean_inc(x_1313);
lean_dec(x_1310);
x_1314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1314, 0, x_1303);
lean_ctor_set(x_1314, 1, x_1313);
return x_1314;
}
}
else
{
uint8_t x_1315; 
lean_dec(x_1306);
x_1315 = !lean_is_exclusive(x_1310);
if (x_1315 == 0)
{
lean_object* x_1316; lean_object* x_1317; uint8_t x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; 
x_1316 = lean_ctor_get(x_1310, 0);
x_1317 = lean_io_error_to_string(x_1316);
x_1318 = 3;
x_1319 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1319, 0, x_1317);
lean_ctor_set_uint8(x_1319, sizeof(void*)*1, x_1318);
x_1320 = lean_array_get_size(x_1307);
x_1321 = lean_array_push(x_1307, x_1319);
lean_ctor_set_tag(x_1303, 1);
lean_ctor_set(x_1303, 1, x_1321);
lean_ctor_set(x_1303, 0, x_1320);
lean_ctor_set_tag(x_1310, 0);
lean_ctor_set(x_1310, 0, x_1303);
return x_1310;
}
else
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; uint8_t x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
x_1322 = lean_ctor_get(x_1310, 0);
x_1323 = lean_ctor_get(x_1310, 1);
lean_inc(x_1323);
lean_inc(x_1322);
lean_dec(x_1310);
x_1324 = lean_io_error_to_string(x_1322);
x_1325 = 3;
x_1326 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1326, 0, x_1324);
lean_ctor_set_uint8(x_1326, sizeof(void*)*1, x_1325);
x_1327 = lean_array_get_size(x_1307);
x_1328 = lean_array_push(x_1307, x_1326);
lean_ctor_set_tag(x_1303, 1);
lean_ctor_set(x_1303, 1, x_1328);
lean_ctor_set(x_1303, 0, x_1327);
x_1329 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1329, 0, x_1303);
lean_ctor_set(x_1329, 1, x_1323);
return x_1329;
}
}
}
else
{
uint8_t x_1330; 
lean_dec(x_1306);
lean_dec(x_1291);
x_1330 = !lean_is_exclusive(x_1308);
if (x_1330 == 0)
{
lean_object* x_1331; lean_object* x_1332; uint8_t x_1333; lean_object* x_1334; lean_object* x_1335; lean_object* x_1336; 
x_1331 = lean_ctor_get(x_1308, 0);
x_1332 = lean_io_error_to_string(x_1331);
x_1333 = 3;
x_1334 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1334, 0, x_1332);
lean_ctor_set_uint8(x_1334, sizeof(void*)*1, x_1333);
x_1335 = lean_array_get_size(x_1307);
x_1336 = lean_array_push(x_1307, x_1334);
lean_ctor_set_tag(x_1303, 1);
lean_ctor_set(x_1303, 1, x_1336);
lean_ctor_set(x_1303, 0, x_1335);
lean_ctor_set_tag(x_1308, 0);
lean_ctor_set(x_1308, 0, x_1303);
return x_1308;
}
else
{
lean_object* x_1337; lean_object* x_1338; lean_object* x_1339; uint8_t x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; 
x_1337 = lean_ctor_get(x_1308, 0);
x_1338 = lean_ctor_get(x_1308, 1);
lean_inc(x_1338);
lean_inc(x_1337);
lean_dec(x_1308);
x_1339 = lean_io_error_to_string(x_1337);
x_1340 = 3;
x_1341 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1341, 0, x_1339);
lean_ctor_set_uint8(x_1341, sizeof(void*)*1, x_1340);
x_1342 = lean_array_get_size(x_1307);
x_1343 = lean_array_push(x_1307, x_1341);
lean_ctor_set_tag(x_1303, 1);
lean_ctor_set(x_1303, 1, x_1343);
lean_ctor_set(x_1303, 0, x_1342);
x_1344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1344, 0, x_1303);
lean_ctor_set(x_1344, 1, x_1338);
return x_1344;
}
}
}
else
{
lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; 
x_1345 = lean_ctor_get(x_1303, 0);
x_1346 = lean_ctor_get(x_1303, 1);
lean_inc(x_1346);
lean_inc(x_1345);
lean_dec(x_1303);
lean_inc(x_1345);
x_1347 = lean_write_module(x_1345, x_20, x_1304);
if (lean_obj_tag(x_1347) == 0)
{
lean_object* x_1348; lean_object* x_1349; 
x_1348 = lean_ctor_get(x_1347, 1);
lean_inc(x_1348);
lean_dec(x_1347);
x_1349 = lean_io_prim_handle_unlock(x_1291, x_1348);
lean_dec(x_1291);
if (lean_obj_tag(x_1349) == 0)
{
lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
x_1350 = lean_ctor_get(x_1349, 1);
lean_inc(x_1350);
if (lean_is_exclusive(x_1349)) {
 lean_ctor_release(x_1349, 0);
 lean_ctor_release(x_1349, 1);
 x_1351 = x_1349;
} else {
 lean_dec_ref(x_1349);
 x_1351 = lean_box(0);
}
x_1352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1352, 0, x_1345);
lean_ctor_set(x_1352, 1, x_1346);
if (lean_is_scalar(x_1351)) {
 x_1353 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1353 = x_1351;
}
lean_ctor_set(x_1353, 0, x_1352);
lean_ctor_set(x_1353, 1, x_1350);
return x_1353;
}
else
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; uint8_t x_1358; lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
lean_dec(x_1345);
x_1354 = lean_ctor_get(x_1349, 0);
lean_inc(x_1354);
x_1355 = lean_ctor_get(x_1349, 1);
lean_inc(x_1355);
if (lean_is_exclusive(x_1349)) {
 lean_ctor_release(x_1349, 0);
 lean_ctor_release(x_1349, 1);
 x_1356 = x_1349;
} else {
 lean_dec_ref(x_1349);
 x_1356 = lean_box(0);
}
x_1357 = lean_io_error_to_string(x_1354);
x_1358 = 3;
x_1359 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1359, 0, x_1357);
lean_ctor_set_uint8(x_1359, sizeof(void*)*1, x_1358);
x_1360 = lean_array_get_size(x_1346);
x_1361 = lean_array_push(x_1346, x_1359);
x_1362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1362, 0, x_1360);
lean_ctor_set(x_1362, 1, x_1361);
if (lean_is_scalar(x_1356)) {
 x_1363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1363 = x_1356;
 lean_ctor_set_tag(x_1363, 0);
}
lean_ctor_set(x_1363, 0, x_1362);
lean_ctor_set(x_1363, 1, x_1355);
return x_1363;
}
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; uint8_t x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; 
lean_dec(x_1345);
lean_dec(x_1291);
x_1364 = lean_ctor_get(x_1347, 0);
lean_inc(x_1364);
x_1365 = lean_ctor_get(x_1347, 1);
lean_inc(x_1365);
if (lean_is_exclusive(x_1347)) {
 lean_ctor_release(x_1347, 0);
 lean_ctor_release(x_1347, 1);
 x_1366 = x_1347;
} else {
 lean_dec_ref(x_1347);
 x_1366 = lean_box(0);
}
x_1367 = lean_io_error_to_string(x_1364);
x_1368 = 3;
x_1369 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1369, 0, x_1367);
lean_ctor_set_uint8(x_1369, sizeof(void*)*1, x_1368);
x_1370 = lean_array_get_size(x_1346);
x_1371 = lean_array_push(x_1346, x_1369);
x_1372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1372, 0, x_1370);
lean_ctor_set(x_1372, 1, x_1371);
if (lean_is_scalar(x_1366)) {
 x_1373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1373 = x_1366;
 lean_ctor_set_tag(x_1373, 0);
}
lean_ctor_set(x_1373, 0, x_1372);
lean_ctor_set(x_1373, 1, x_1365);
return x_1373;
}
}
}
else
{
uint8_t x_1374; 
lean_dec(x_1291);
lean_dec(x_20);
x_1374 = !lean_is_exclusive(x_1302);
if (x_1374 == 0)
{
lean_object* x_1375; uint8_t x_1376; 
x_1375 = lean_ctor_get(x_1302, 0);
lean_dec(x_1375);
x_1376 = !lean_is_exclusive(x_1303);
if (x_1376 == 0)
{
return x_1302;
}
else
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; 
x_1377 = lean_ctor_get(x_1303, 0);
x_1378 = lean_ctor_get(x_1303, 1);
lean_inc(x_1378);
lean_inc(x_1377);
lean_dec(x_1303);
x_1379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1379, 0, x_1377);
lean_ctor_set(x_1379, 1, x_1378);
lean_ctor_set(x_1302, 0, x_1379);
return x_1302;
}
}
else
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1380 = lean_ctor_get(x_1302, 1);
lean_inc(x_1380);
lean_dec(x_1302);
x_1381 = lean_ctor_get(x_1303, 0);
lean_inc(x_1381);
x_1382 = lean_ctor_get(x_1303, 1);
lean_inc(x_1382);
if (lean_is_exclusive(x_1303)) {
 lean_ctor_release(x_1303, 0);
 lean_ctor_release(x_1303, 1);
 x_1383 = x_1303;
} else {
 lean_dec_ref(x_1303);
 x_1383 = lean_box(0);
}
if (lean_is_scalar(x_1383)) {
 x_1384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1384 = x_1383;
}
lean_ctor_set(x_1384, 0, x_1381);
lean_ctor_set(x_1384, 1, x_1382);
x_1385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1385, 0, x_1384);
lean_ctor_set(x_1385, 1, x_1380);
return x_1385;
}
}
}
else
{
uint8_t x_1386; 
lean_dec(x_1297);
lean_dec(x_1291);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1386 = !lean_is_exclusive(x_1298);
if (x_1386 == 0)
{
lean_object* x_1387; 
x_1387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1387, 0, x_1298);
lean_ctor_set(x_1387, 1, x_1299);
return x_1387;
}
else
{
lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; 
x_1388 = lean_ctor_get(x_1298, 0);
x_1389 = lean_ctor_get(x_1298, 1);
lean_inc(x_1389);
lean_inc(x_1388);
lean_dec(x_1298);
x_1390 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1390, 0, x_1388);
lean_ctor_set(x_1390, 1, x_1389);
x_1391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1391, 0, x_1390);
lean_ctor_set(x_1391, 1, x_1299);
return x_1391;
}
}
}
block_1601:
{
lean_object* x_1395; 
x_1395 = lean_ctor_get(x_1393, 0);
lean_inc(x_1395);
if (lean_obj_tag(x_1395) == 0)
{
lean_object* x_1396; 
x_1396 = lean_ctor_get(x_1395, 0);
lean_inc(x_1396);
lean_dec(x_1395);
if (lean_obj_tag(x_1396) == 11)
{
uint8_t x_1397; 
lean_dec(x_1396);
lean_dec(x_23);
x_1397 = !lean_is_exclusive(x_1393);
if (x_1397 == 0)
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; 
x_1398 = lean_ctor_get(x_1393, 1);
x_1399 = lean_ctor_get(x_1393, 0);
lean_dec(x_1399);
x_1400 = lean_ctor_get(x_1, 0);
lean_inc(x_1400);
x_1401 = l_Lake_Env_leanGithash(x_1400);
lean_dec(x_1400);
x_1402 = l_System_Platform_target;
lean_inc(x_1297);
x_1403 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1403, 0, x_1402);
lean_ctor_set(x_1403, 1, x_1401);
lean_ctor_set(x_1403, 2, x_29);
lean_ctor_set(x_1403, 3, x_1297);
x_1404 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_1403);
x_1405 = lean_unsigned_to_nat(80u);
x_1406 = l_Lean_Json_pretty(x_1404, x_1405);
x_1407 = l_IO_FS_Handle_putStrLn(x_1291, x_1406, x_1394);
if (lean_obj_tag(x_1407) == 0)
{
lean_object* x_1408; lean_object* x_1409; 
x_1408 = lean_ctor_get(x_1407, 1);
lean_inc(x_1408);
lean_dec(x_1407);
x_1409 = lean_io_prim_handle_truncate(x_1291, x_1408);
if (lean_obj_tag(x_1409) == 0)
{
lean_object* x_1410; lean_object* x_1411; 
x_1410 = lean_ctor_get(x_1409, 0);
lean_inc(x_1410);
x_1411 = lean_ctor_get(x_1409, 1);
lean_inc(x_1411);
lean_dec(x_1409);
lean_ctor_set(x_1393, 0, x_1410);
x_1298 = x_1393;
x_1299 = x_1411;
goto block_1392;
}
else
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; uint8_t x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; 
x_1412 = lean_ctor_get(x_1409, 0);
lean_inc(x_1412);
x_1413 = lean_ctor_get(x_1409, 1);
lean_inc(x_1413);
lean_dec(x_1409);
x_1414 = lean_io_error_to_string(x_1412);
x_1415 = 3;
x_1416 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1416, 0, x_1414);
lean_ctor_set_uint8(x_1416, sizeof(void*)*1, x_1415);
x_1417 = lean_array_get_size(x_1398);
x_1418 = lean_array_push(x_1398, x_1416);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1418);
lean_ctor_set(x_1393, 0, x_1417);
x_1298 = x_1393;
x_1299 = x_1413;
goto block_1392;
}
}
else
{
uint8_t x_1419; 
lean_dec(x_1297);
lean_dec(x_1291);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1419 = !lean_is_exclusive(x_1407);
if (x_1419 == 0)
{
lean_object* x_1420; lean_object* x_1421; uint8_t x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; 
x_1420 = lean_ctor_get(x_1407, 0);
x_1421 = lean_io_error_to_string(x_1420);
x_1422 = 3;
x_1423 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1423, 0, x_1421);
lean_ctor_set_uint8(x_1423, sizeof(void*)*1, x_1422);
x_1424 = lean_array_get_size(x_1398);
x_1425 = lean_array_push(x_1398, x_1423);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1425);
lean_ctor_set(x_1393, 0, x_1424);
lean_ctor_set_tag(x_1407, 0);
lean_ctor_set(x_1407, 0, x_1393);
return x_1407;
}
else
{
lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; uint8_t x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; 
x_1426 = lean_ctor_get(x_1407, 0);
x_1427 = lean_ctor_get(x_1407, 1);
lean_inc(x_1427);
lean_inc(x_1426);
lean_dec(x_1407);
x_1428 = lean_io_error_to_string(x_1426);
x_1429 = 3;
x_1430 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1430, 0, x_1428);
lean_ctor_set_uint8(x_1430, sizeof(void*)*1, x_1429);
x_1431 = lean_array_get_size(x_1398);
x_1432 = lean_array_push(x_1398, x_1430);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1432);
lean_ctor_set(x_1393, 0, x_1431);
x_1433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1433, 0, x_1393);
lean_ctor_set(x_1433, 1, x_1427);
return x_1433;
}
}
}
else
{
lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
x_1434 = lean_ctor_get(x_1393, 1);
lean_inc(x_1434);
lean_dec(x_1393);
x_1435 = lean_ctor_get(x_1, 0);
lean_inc(x_1435);
x_1436 = l_Lake_Env_leanGithash(x_1435);
lean_dec(x_1435);
x_1437 = l_System_Platform_target;
lean_inc(x_1297);
x_1438 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1438, 0, x_1437);
lean_ctor_set(x_1438, 1, x_1436);
lean_ctor_set(x_1438, 2, x_29);
lean_ctor_set(x_1438, 3, x_1297);
x_1439 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_1438);
x_1440 = lean_unsigned_to_nat(80u);
x_1441 = l_Lean_Json_pretty(x_1439, x_1440);
x_1442 = l_IO_FS_Handle_putStrLn(x_1291, x_1441, x_1394);
if (lean_obj_tag(x_1442) == 0)
{
lean_object* x_1443; lean_object* x_1444; 
x_1443 = lean_ctor_get(x_1442, 1);
lean_inc(x_1443);
lean_dec(x_1442);
x_1444 = lean_io_prim_handle_truncate(x_1291, x_1443);
if (lean_obj_tag(x_1444) == 0)
{
lean_object* x_1445; lean_object* x_1446; lean_object* x_1447; 
x_1445 = lean_ctor_get(x_1444, 0);
lean_inc(x_1445);
x_1446 = lean_ctor_get(x_1444, 1);
lean_inc(x_1446);
lean_dec(x_1444);
x_1447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1447, 0, x_1445);
lean_ctor_set(x_1447, 1, x_1434);
x_1298 = x_1447;
x_1299 = x_1446;
goto block_1392;
}
else
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; uint8_t x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; 
x_1448 = lean_ctor_get(x_1444, 0);
lean_inc(x_1448);
x_1449 = lean_ctor_get(x_1444, 1);
lean_inc(x_1449);
lean_dec(x_1444);
x_1450 = lean_io_error_to_string(x_1448);
x_1451 = 3;
x_1452 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1452, 0, x_1450);
lean_ctor_set_uint8(x_1452, sizeof(void*)*1, x_1451);
x_1453 = lean_array_get_size(x_1434);
x_1454 = lean_array_push(x_1434, x_1452);
x_1455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1455, 0, x_1453);
lean_ctor_set(x_1455, 1, x_1454);
x_1298 = x_1455;
x_1299 = x_1449;
goto block_1392;
}
}
else
{
lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; uint8_t x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; 
lean_dec(x_1297);
lean_dec(x_1291);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1456 = lean_ctor_get(x_1442, 0);
lean_inc(x_1456);
x_1457 = lean_ctor_get(x_1442, 1);
lean_inc(x_1457);
if (lean_is_exclusive(x_1442)) {
 lean_ctor_release(x_1442, 0);
 lean_ctor_release(x_1442, 1);
 x_1458 = x_1442;
} else {
 lean_dec_ref(x_1442);
 x_1458 = lean_box(0);
}
x_1459 = lean_io_error_to_string(x_1456);
x_1460 = 3;
x_1461 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1461, 0, x_1459);
lean_ctor_set_uint8(x_1461, sizeof(void*)*1, x_1460);
x_1462 = lean_array_get_size(x_1434);
x_1463 = lean_array_push(x_1434, x_1461);
x_1464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1464, 0, x_1462);
lean_ctor_set(x_1464, 1, x_1463);
if (lean_is_scalar(x_1458)) {
 x_1465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1465 = x_1458;
 lean_ctor_set_tag(x_1465, 0);
}
lean_ctor_set(x_1465, 0, x_1464);
lean_ctor_set(x_1465, 1, x_1457);
return x_1465;
}
}
}
else
{
uint8_t x_1466; 
lean_dec(x_1297);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1466 = !lean_is_exclusive(x_1393);
if (x_1466 == 0)
{
lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; uint8_t x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
x_1467 = lean_ctor_get(x_1393, 1);
x_1468 = lean_ctor_get(x_1393, 0);
lean_dec(x_1468);
x_1469 = lean_io_error_to_string(x_1396);
x_1470 = 3;
x_1471 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1471, 0, x_1469);
lean_ctor_set_uint8(x_1471, sizeof(void*)*1, x_1470);
x_1472 = lean_array_get_size(x_1467);
x_1473 = lean_array_push(x_1467, x_1471);
x_1474 = lean_io_prim_handle_unlock(x_1291, x_1394);
lean_dec(x_1291);
if (lean_obj_tag(x_1474) == 0)
{
lean_object* x_1475; lean_object* x_1476; 
x_1475 = lean_ctor_get(x_1474, 1);
lean_inc(x_1475);
lean_dec(x_1474);
x_1476 = lean_io_remove_file(x_23, x_1475);
lean_dec(x_23);
if (lean_obj_tag(x_1476) == 0)
{
uint8_t x_1477; 
x_1477 = !lean_is_exclusive(x_1476);
if (x_1477 == 0)
{
lean_object* x_1478; 
x_1478 = lean_ctor_get(x_1476, 0);
lean_dec(x_1478);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1473);
lean_ctor_set(x_1393, 0, x_1472);
lean_ctor_set(x_1476, 0, x_1393);
return x_1476;
}
else
{
lean_object* x_1479; lean_object* x_1480; 
x_1479 = lean_ctor_get(x_1476, 1);
lean_inc(x_1479);
lean_dec(x_1476);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1473);
lean_ctor_set(x_1393, 0, x_1472);
x_1480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1480, 0, x_1393);
lean_ctor_set(x_1480, 1, x_1479);
return x_1480;
}
}
else
{
uint8_t x_1481; 
x_1481 = !lean_is_exclusive(x_1476);
if (x_1481 == 0)
{
lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; 
x_1482 = lean_ctor_get(x_1476, 0);
x_1483 = lean_io_error_to_string(x_1482);
x_1484 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1484, 0, x_1483);
lean_ctor_set_uint8(x_1484, sizeof(void*)*1, x_1470);
x_1485 = lean_array_push(x_1473, x_1484);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1485);
lean_ctor_set(x_1393, 0, x_1472);
lean_ctor_set_tag(x_1476, 0);
lean_ctor_set(x_1476, 0, x_1393);
return x_1476;
}
else
{
lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1486 = lean_ctor_get(x_1476, 0);
x_1487 = lean_ctor_get(x_1476, 1);
lean_inc(x_1487);
lean_inc(x_1486);
lean_dec(x_1476);
x_1488 = lean_io_error_to_string(x_1486);
x_1489 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1489, 0, x_1488);
lean_ctor_set_uint8(x_1489, sizeof(void*)*1, x_1470);
x_1490 = lean_array_push(x_1473, x_1489);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1490);
lean_ctor_set(x_1393, 0, x_1472);
x_1491 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1491, 0, x_1393);
lean_ctor_set(x_1491, 1, x_1487);
return x_1491;
}
}
}
else
{
uint8_t x_1492; 
lean_dec(x_23);
x_1492 = !lean_is_exclusive(x_1474);
if (x_1492 == 0)
{
lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; 
x_1493 = lean_ctor_get(x_1474, 0);
x_1494 = lean_io_error_to_string(x_1493);
x_1495 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1495, 0, x_1494);
lean_ctor_set_uint8(x_1495, sizeof(void*)*1, x_1470);
x_1496 = lean_array_push(x_1473, x_1495);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1496);
lean_ctor_set(x_1393, 0, x_1472);
lean_ctor_set_tag(x_1474, 0);
lean_ctor_set(x_1474, 0, x_1393);
return x_1474;
}
else
{
lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; 
x_1497 = lean_ctor_get(x_1474, 0);
x_1498 = lean_ctor_get(x_1474, 1);
lean_inc(x_1498);
lean_inc(x_1497);
lean_dec(x_1474);
x_1499 = lean_io_error_to_string(x_1497);
x_1500 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1500, 0, x_1499);
lean_ctor_set_uint8(x_1500, sizeof(void*)*1, x_1470);
x_1501 = lean_array_push(x_1473, x_1500);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1501);
lean_ctor_set(x_1393, 0, x_1472);
x_1502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1502, 0, x_1393);
lean_ctor_set(x_1502, 1, x_1498);
return x_1502;
}
}
}
else
{
lean_object* x_1503; lean_object* x_1504; uint8_t x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; 
x_1503 = lean_ctor_get(x_1393, 1);
lean_inc(x_1503);
lean_dec(x_1393);
x_1504 = lean_io_error_to_string(x_1396);
x_1505 = 3;
x_1506 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1506, 0, x_1504);
lean_ctor_set_uint8(x_1506, sizeof(void*)*1, x_1505);
x_1507 = lean_array_get_size(x_1503);
x_1508 = lean_array_push(x_1503, x_1506);
x_1509 = lean_io_prim_handle_unlock(x_1291, x_1394);
lean_dec(x_1291);
if (lean_obj_tag(x_1509) == 0)
{
lean_object* x_1510; lean_object* x_1511; 
x_1510 = lean_ctor_get(x_1509, 1);
lean_inc(x_1510);
lean_dec(x_1509);
x_1511 = lean_io_remove_file(x_23, x_1510);
lean_dec(x_23);
if (lean_obj_tag(x_1511) == 0)
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; 
x_1512 = lean_ctor_get(x_1511, 1);
lean_inc(x_1512);
if (lean_is_exclusive(x_1511)) {
 lean_ctor_release(x_1511, 0);
 lean_ctor_release(x_1511, 1);
 x_1513 = x_1511;
} else {
 lean_dec_ref(x_1511);
 x_1513 = lean_box(0);
}
x_1514 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1514, 0, x_1507);
lean_ctor_set(x_1514, 1, x_1508);
if (lean_is_scalar(x_1513)) {
 x_1515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1515 = x_1513;
}
lean_ctor_set(x_1515, 0, x_1514);
lean_ctor_set(x_1515, 1, x_1512);
return x_1515;
}
else
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; 
x_1516 = lean_ctor_get(x_1511, 0);
lean_inc(x_1516);
x_1517 = lean_ctor_get(x_1511, 1);
lean_inc(x_1517);
if (lean_is_exclusive(x_1511)) {
 lean_ctor_release(x_1511, 0);
 lean_ctor_release(x_1511, 1);
 x_1518 = x_1511;
} else {
 lean_dec_ref(x_1511);
 x_1518 = lean_box(0);
}
x_1519 = lean_io_error_to_string(x_1516);
x_1520 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1520, 0, x_1519);
lean_ctor_set_uint8(x_1520, sizeof(void*)*1, x_1505);
x_1521 = lean_array_push(x_1508, x_1520);
x_1522 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1522, 0, x_1507);
lean_ctor_set(x_1522, 1, x_1521);
if (lean_is_scalar(x_1518)) {
 x_1523 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1523 = x_1518;
 lean_ctor_set_tag(x_1523, 0);
}
lean_ctor_set(x_1523, 0, x_1522);
lean_ctor_set(x_1523, 1, x_1517);
return x_1523;
}
}
else
{
lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; 
lean_dec(x_23);
x_1524 = lean_ctor_get(x_1509, 0);
lean_inc(x_1524);
x_1525 = lean_ctor_get(x_1509, 1);
lean_inc(x_1525);
if (lean_is_exclusive(x_1509)) {
 lean_ctor_release(x_1509, 0);
 lean_ctor_release(x_1509, 1);
 x_1526 = x_1509;
} else {
 lean_dec_ref(x_1509);
 x_1526 = lean_box(0);
}
x_1527 = lean_io_error_to_string(x_1524);
x_1528 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1528, 0, x_1527);
lean_ctor_set_uint8(x_1528, sizeof(void*)*1, x_1505);
x_1529 = lean_array_push(x_1508, x_1528);
x_1530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1530, 0, x_1507);
lean_ctor_set(x_1530, 1, x_1529);
if (lean_is_scalar(x_1526)) {
 x_1531 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1531 = x_1526;
 lean_ctor_set_tag(x_1531, 0);
}
lean_ctor_set(x_1531, 0, x_1530);
lean_ctor_set(x_1531, 1, x_1525);
return x_1531;
}
}
}
}
else
{
uint8_t x_1532; 
lean_dec(x_1395);
lean_dec(x_23);
x_1532 = !lean_is_exclusive(x_1393);
if (x_1532 == 0)
{
lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; 
x_1533 = lean_ctor_get(x_1393, 1);
x_1534 = lean_ctor_get(x_1393, 0);
lean_dec(x_1534);
x_1535 = lean_ctor_get(x_1, 0);
lean_inc(x_1535);
x_1536 = l_Lake_Env_leanGithash(x_1535);
lean_dec(x_1535);
x_1537 = l_System_Platform_target;
lean_inc(x_1297);
x_1538 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1538, 0, x_1537);
lean_ctor_set(x_1538, 1, x_1536);
lean_ctor_set(x_1538, 2, x_29);
lean_ctor_set(x_1538, 3, x_1297);
x_1539 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_1538);
x_1540 = lean_unsigned_to_nat(80u);
x_1541 = l_Lean_Json_pretty(x_1539, x_1540);
x_1542 = l_IO_FS_Handle_putStrLn(x_1291, x_1541, x_1394);
if (lean_obj_tag(x_1542) == 0)
{
lean_object* x_1543; lean_object* x_1544; 
x_1543 = lean_ctor_get(x_1542, 1);
lean_inc(x_1543);
lean_dec(x_1542);
x_1544 = lean_io_prim_handle_truncate(x_1291, x_1543);
if (lean_obj_tag(x_1544) == 0)
{
lean_object* x_1545; lean_object* x_1546; 
x_1545 = lean_ctor_get(x_1544, 0);
lean_inc(x_1545);
x_1546 = lean_ctor_get(x_1544, 1);
lean_inc(x_1546);
lean_dec(x_1544);
lean_ctor_set(x_1393, 0, x_1545);
x_1298 = x_1393;
x_1299 = x_1546;
goto block_1392;
}
else
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; uint8_t x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; 
x_1547 = lean_ctor_get(x_1544, 0);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1544, 1);
lean_inc(x_1548);
lean_dec(x_1544);
x_1549 = lean_io_error_to_string(x_1547);
x_1550 = 3;
x_1551 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1551, 0, x_1549);
lean_ctor_set_uint8(x_1551, sizeof(void*)*1, x_1550);
x_1552 = lean_array_get_size(x_1533);
x_1553 = lean_array_push(x_1533, x_1551);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1553);
lean_ctor_set(x_1393, 0, x_1552);
x_1298 = x_1393;
x_1299 = x_1548;
goto block_1392;
}
}
else
{
uint8_t x_1554; 
lean_dec(x_1297);
lean_dec(x_1291);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1554 = !lean_is_exclusive(x_1542);
if (x_1554 == 0)
{
lean_object* x_1555; lean_object* x_1556; uint8_t x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; 
x_1555 = lean_ctor_get(x_1542, 0);
x_1556 = lean_io_error_to_string(x_1555);
x_1557 = 3;
x_1558 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1558, 0, x_1556);
lean_ctor_set_uint8(x_1558, sizeof(void*)*1, x_1557);
x_1559 = lean_array_get_size(x_1533);
x_1560 = lean_array_push(x_1533, x_1558);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1560);
lean_ctor_set(x_1393, 0, x_1559);
lean_ctor_set_tag(x_1542, 0);
lean_ctor_set(x_1542, 0, x_1393);
return x_1542;
}
else
{
lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; uint8_t x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; 
x_1561 = lean_ctor_get(x_1542, 0);
x_1562 = lean_ctor_get(x_1542, 1);
lean_inc(x_1562);
lean_inc(x_1561);
lean_dec(x_1542);
x_1563 = lean_io_error_to_string(x_1561);
x_1564 = 3;
x_1565 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1565, 0, x_1563);
lean_ctor_set_uint8(x_1565, sizeof(void*)*1, x_1564);
x_1566 = lean_array_get_size(x_1533);
x_1567 = lean_array_push(x_1533, x_1565);
lean_ctor_set_tag(x_1393, 1);
lean_ctor_set(x_1393, 1, x_1567);
lean_ctor_set(x_1393, 0, x_1566);
x_1568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1568, 0, x_1393);
lean_ctor_set(x_1568, 1, x_1562);
return x_1568;
}
}
}
else
{
lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; 
x_1569 = lean_ctor_get(x_1393, 1);
lean_inc(x_1569);
lean_dec(x_1393);
x_1570 = lean_ctor_get(x_1, 0);
lean_inc(x_1570);
x_1571 = l_Lake_Env_leanGithash(x_1570);
lean_dec(x_1570);
x_1572 = l_System_Platform_target;
lean_inc(x_1297);
x_1573 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1573, 0, x_1572);
lean_ctor_set(x_1573, 1, x_1571);
lean_ctor_set(x_1573, 2, x_29);
lean_ctor_set(x_1573, 3, x_1297);
x_1574 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_1573);
x_1575 = lean_unsigned_to_nat(80u);
x_1576 = l_Lean_Json_pretty(x_1574, x_1575);
x_1577 = l_IO_FS_Handle_putStrLn(x_1291, x_1576, x_1394);
if (lean_obj_tag(x_1577) == 0)
{
lean_object* x_1578; lean_object* x_1579; 
x_1578 = lean_ctor_get(x_1577, 1);
lean_inc(x_1578);
lean_dec(x_1577);
x_1579 = lean_io_prim_handle_truncate(x_1291, x_1578);
if (lean_obj_tag(x_1579) == 0)
{
lean_object* x_1580; lean_object* x_1581; lean_object* x_1582; 
x_1580 = lean_ctor_get(x_1579, 0);
lean_inc(x_1580);
x_1581 = lean_ctor_get(x_1579, 1);
lean_inc(x_1581);
lean_dec(x_1579);
x_1582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1582, 0, x_1580);
lean_ctor_set(x_1582, 1, x_1569);
x_1298 = x_1582;
x_1299 = x_1581;
goto block_1392;
}
else
{
lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; uint8_t x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; 
x_1583 = lean_ctor_get(x_1579, 0);
lean_inc(x_1583);
x_1584 = lean_ctor_get(x_1579, 1);
lean_inc(x_1584);
lean_dec(x_1579);
x_1585 = lean_io_error_to_string(x_1583);
x_1586 = 3;
x_1587 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1587, 0, x_1585);
lean_ctor_set_uint8(x_1587, sizeof(void*)*1, x_1586);
x_1588 = lean_array_get_size(x_1569);
x_1589 = lean_array_push(x_1569, x_1587);
x_1590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1590, 0, x_1588);
lean_ctor_set(x_1590, 1, x_1589);
x_1298 = x_1590;
x_1299 = x_1584;
goto block_1392;
}
}
else
{
lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; uint8_t x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; 
lean_dec(x_1297);
lean_dec(x_1291);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1591 = lean_ctor_get(x_1577, 0);
lean_inc(x_1591);
x_1592 = lean_ctor_get(x_1577, 1);
lean_inc(x_1592);
if (lean_is_exclusive(x_1577)) {
 lean_ctor_release(x_1577, 0);
 lean_ctor_release(x_1577, 1);
 x_1593 = x_1577;
} else {
 lean_dec_ref(x_1577);
 x_1593 = lean_box(0);
}
x_1594 = lean_io_error_to_string(x_1591);
x_1595 = 3;
x_1596 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1596, 0, x_1594);
lean_ctor_set_uint8(x_1596, sizeof(void*)*1, x_1595);
x_1597 = lean_array_get_size(x_1569);
x_1598 = lean_array_push(x_1569, x_1596);
x_1599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1599, 0, x_1597);
lean_ctor_set(x_1599, 1, x_1598);
if (lean_is_scalar(x_1593)) {
 x_1600 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1600 = x_1593;
 lean_ctor_set_tag(x_1600, 0);
}
lean_ctor_set(x_1600, 0, x_1599);
lean_ctor_set(x_1600, 1, x_1592);
return x_1600;
}
}
}
}
}
else
{
lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1661; lean_object* x_1662; lean_object* x_1762; 
x_1609 = lean_ctor_get(x_1293, 1);
lean_inc(x_1609);
lean_dec(x_1293);
x_1610 = lean_ctor_get(x_1, 4);
lean_inc(x_1610);
x_1762 = lean_io_remove_file(x_20, x_1294);
if (lean_obj_tag(x_1762) == 0)
{
lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; 
x_1763 = lean_ctor_get(x_1762, 0);
lean_inc(x_1763);
x_1764 = lean_ctor_get(x_1762, 1);
lean_inc(x_1764);
lean_dec(x_1762);
if (lean_is_scalar(x_1292)) {
 x_1765 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1765 = x_1292;
}
lean_ctor_set(x_1765, 0, x_1763);
x_1766 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1766, 0, x_1765);
lean_ctor_set(x_1766, 1, x_1609);
x_1661 = x_1766;
x_1662 = x_1764;
goto block_1761;
}
else
{
lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; 
x_1767 = lean_ctor_get(x_1762, 0);
lean_inc(x_1767);
x_1768 = lean_ctor_get(x_1762, 1);
lean_inc(x_1768);
lean_dec(x_1762);
if (lean_is_scalar(x_1292)) {
 x_1769 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1769 = x_1292;
 lean_ctor_set_tag(x_1769, 0);
}
lean_ctor_set(x_1769, 0, x_1767);
x_1770 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1770, 0, x_1769);
lean_ctor_set(x_1770, 1, x_1609);
x_1661 = x_1770;
x_1662 = x_1768;
goto block_1761;
}
block_1660:
{
if (lean_obj_tag(x_1611) == 0)
{
lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; 
x_1613 = lean_ctor_get(x_1611, 1);
lean_inc(x_1613);
lean_dec(x_1611);
x_1614 = lean_ctor_get(x_1, 5);
lean_inc(x_1614);
lean_dec(x_1);
x_1615 = l_Lake_elabConfigFile(x_6, x_1610, x_1614, x_8, x_1613, x_1612);
x_1616 = lean_ctor_get(x_1615, 0);
lean_inc(x_1616);
if (lean_obj_tag(x_1616) == 0)
{
lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
x_1617 = lean_ctor_get(x_1615, 1);
lean_inc(x_1617);
lean_dec(x_1615);
x_1618 = lean_ctor_get(x_1616, 0);
lean_inc(x_1618);
x_1619 = lean_ctor_get(x_1616, 1);
lean_inc(x_1619);
if (lean_is_exclusive(x_1616)) {
 lean_ctor_release(x_1616, 0);
 lean_ctor_release(x_1616, 1);
 x_1620 = x_1616;
} else {
 lean_dec_ref(x_1616);
 x_1620 = lean_box(0);
}
lean_inc(x_1618);
x_1621 = lean_write_module(x_1618, x_20, x_1617);
if (lean_obj_tag(x_1621) == 0)
{
lean_object* x_1622; lean_object* x_1623; 
x_1622 = lean_ctor_get(x_1621, 1);
lean_inc(x_1622);
lean_dec(x_1621);
x_1623 = lean_io_prim_handle_unlock(x_1291, x_1622);
lean_dec(x_1291);
if (lean_obj_tag(x_1623) == 0)
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; 
x_1624 = lean_ctor_get(x_1623, 1);
lean_inc(x_1624);
if (lean_is_exclusive(x_1623)) {
 lean_ctor_release(x_1623, 0);
 lean_ctor_release(x_1623, 1);
 x_1625 = x_1623;
} else {
 lean_dec_ref(x_1623);
 x_1625 = lean_box(0);
}
if (lean_is_scalar(x_1620)) {
 x_1626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1626 = x_1620;
}
lean_ctor_set(x_1626, 0, x_1618);
lean_ctor_set(x_1626, 1, x_1619);
if (lean_is_scalar(x_1625)) {
 x_1627 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1627 = x_1625;
}
lean_ctor_set(x_1627, 0, x_1626);
lean_ctor_set(x_1627, 1, x_1624);
return x_1627;
}
else
{
lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; uint8_t x_1632; lean_object* x_1633; lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; 
lean_dec(x_1618);
x_1628 = lean_ctor_get(x_1623, 0);
lean_inc(x_1628);
x_1629 = lean_ctor_get(x_1623, 1);
lean_inc(x_1629);
if (lean_is_exclusive(x_1623)) {
 lean_ctor_release(x_1623, 0);
 lean_ctor_release(x_1623, 1);
 x_1630 = x_1623;
} else {
 lean_dec_ref(x_1623);
 x_1630 = lean_box(0);
}
x_1631 = lean_io_error_to_string(x_1628);
x_1632 = 3;
x_1633 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1633, 0, x_1631);
lean_ctor_set_uint8(x_1633, sizeof(void*)*1, x_1632);
x_1634 = lean_array_get_size(x_1619);
x_1635 = lean_array_push(x_1619, x_1633);
if (lean_is_scalar(x_1620)) {
 x_1636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1636 = x_1620;
 lean_ctor_set_tag(x_1636, 1);
}
lean_ctor_set(x_1636, 0, x_1634);
lean_ctor_set(x_1636, 1, x_1635);
if (lean_is_scalar(x_1630)) {
 x_1637 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1637 = x_1630;
 lean_ctor_set_tag(x_1637, 0);
}
lean_ctor_set(x_1637, 0, x_1636);
lean_ctor_set(x_1637, 1, x_1629);
return x_1637;
}
}
else
{
lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; uint8_t x_1642; lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; 
lean_dec(x_1618);
lean_dec(x_1291);
x_1638 = lean_ctor_get(x_1621, 0);
lean_inc(x_1638);
x_1639 = lean_ctor_get(x_1621, 1);
lean_inc(x_1639);
if (lean_is_exclusive(x_1621)) {
 lean_ctor_release(x_1621, 0);
 lean_ctor_release(x_1621, 1);
 x_1640 = x_1621;
} else {
 lean_dec_ref(x_1621);
 x_1640 = lean_box(0);
}
x_1641 = lean_io_error_to_string(x_1638);
x_1642 = 3;
x_1643 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1643, 0, x_1641);
lean_ctor_set_uint8(x_1643, sizeof(void*)*1, x_1642);
x_1644 = lean_array_get_size(x_1619);
x_1645 = lean_array_push(x_1619, x_1643);
if (lean_is_scalar(x_1620)) {
 x_1646 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1646 = x_1620;
 lean_ctor_set_tag(x_1646, 1);
}
lean_ctor_set(x_1646, 0, x_1644);
lean_ctor_set(x_1646, 1, x_1645);
if (lean_is_scalar(x_1640)) {
 x_1647 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1647 = x_1640;
 lean_ctor_set_tag(x_1647, 0);
}
lean_ctor_set(x_1647, 0, x_1646);
lean_ctor_set(x_1647, 1, x_1639);
return x_1647;
}
}
else
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; 
lean_dec(x_1291);
lean_dec(x_20);
x_1648 = lean_ctor_get(x_1615, 1);
lean_inc(x_1648);
if (lean_is_exclusive(x_1615)) {
 lean_ctor_release(x_1615, 0);
 lean_ctor_release(x_1615, 1);
 x_1649 = x_1615;
} else {
 lean_dec_ref(x_1615);
 x_1649 = lean_box(0);
}
x_1650 = lean_ctor_get(x_1616, 0);
lean_inc(x_1650);
x_1651 = lean_ctor_get(x_1616, 1);
lean_inc(x_1651);
if (lean_is_exclusive(x_1616)) {
 lean_ctor_release(x_1616, 0);
 lean_ctor_release(x_1616, 1);
 x_1652 = x_1616;
} else {
 lean_dec_ref(x_1616);
 x_1652 = lean_box(0);
}
if (lean_is_scalar(x_1652)) {
 x_1653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1653 = x_1652;
}
lean_ctor_set(x_1653, 0, x_1650);
lean_ctor_set(x_1653, 1, x_1651);
if (lean_is_scalar(x_1649)) {
 x_1654 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1654 = x_1649;
}
lean_ctor_set(x_1654, 0, x_1653);
lean_ctor_set(x_1654, 1, x_1648);
return x_1654;
}
}
else
{
lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; 
lean_dec(x_1610);
lean_dec(x_1291);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1655 = lean_ctor_get(x_1611, 0);
lean_inc(x_1655);
x_1656 = lean_ctor_get(x_1611, 1);
lean_inc(x_1656);
if (lean_is_exclusive(x_1611)) {
 lean_ctor_release(x_1611, 0);
 lean_ctor_release(x_1611, 1);
 x_1657 = x_1611;
} else {
 lean_dec_ref(x_1611);
 x_1657 = lean_box(0);
}
if (lean_is_scalar(x_1657)) {
 x_1658 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1658 = x_1657;
}
lean_ctor_set(x_1658, 0, x_1655);
lean_ctor_set(x_1658, 1, x_1656);
x_1659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1659, 0, x_1658);
lean_ctor_set(x_1659, 1, x_1612);
return x_1659;
}
}
block_1761:
{
lean_object* x_1663; 
x_1663 = lean_ctor_get(x_1661, 0);
lean_inc(x_1663);
if (lean_obj_tag(x_1663) == 0)
{
lean_object* x_1664; 
x_1664 = lean_ctor_get(x_1663, 0);
lean_inc(x_1664);
lean_dec(x_1663);
if (lean_obj_tag(x_1664) == 11)
{
lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; 
lean_dec(x_1664);
lean_dec(x_23);
x_1665 = lean_ctor_get(x_1661, 1);
lean_inc(x_1665);
if (lean_is_exclusive(x_1661)) {
 lean_ctor_release(x_1661, 0);
 lean_ctor_release(x_1661, 1);
 x_1666 = x_1661;
} else {
 lean_dec_ref(x_1661);
 x_1666 = lean_box(0);
}
x_1667 = lean_ctor_get(x_1, 0);
lean_inc(x_1667);
x_1668 = l_Lake_Env_leanGithash(x_1667);
lean_dec(x_1667);
x_1669 = l_System_Platform_target;
lean_inc(x_1610);
x_1670 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1670, 0, x_1669);
lean_ctor_set(x_1670, 1, x_1668);
lean_ctor_set(x_1670, 2, x_29);
lean_ctor_set(x_1670, 3, x_1610);
x_1671 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_1670);
x_1672 = lean_unsigned_to_nat(80u);
x_1673 = l_Lean_Json_pretty(x_1671, x_1672);
x_1674 = l_IO_FS_Handle_putStrLn(x_1291, x_1673, x_1662);
if (lean_obj_tag(x_1674) == 0)
{
lean_object* x_1675; lean_object* x_1676; 
x_1675 = lean_ctor_get(x_1674, 1);
lean_inc(x_1675);
lean_dec(x_1674);
x_1676 = lean_io_prim_handle_truncate(x_1291, x_1675);
if (lean_obj_tag(x_1676) == 0)
{
lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; 
x_1677 = lean_ctor_get(x_1676, 0);
lean_inc(x_1677);
x_1678 = lean_ctor_get(x_1676, 1);
lean_inc(x_1678);
lean_dec(x_1676);
if (lean_is_scalar(x_1666)) {
 x_1679 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1679 = x_1666;
}
lean_ctor_set(x_1679, 0, x_1677);
lean_ctor_set(x_1679, 1, x_1665);
x_1611 = x_1679;
x_1612 = x_1678;
goto block_1660;
}
else
{
lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; uint8_t x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; 
x_1680 = lean_ctor_get(x_1676, 0);
lean_inc(x_1680);
x_1681 = lean_ctor_get(x_1676, 1);
lean_inc(x_1681);
lean_dec(x_1676);
x_1682 = lean_io_error_to_string(x_1680);
x_1683 = 3;
x_1684 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1684, 0, x_1682);
lean_ctor_set_uint8(x_1684, sizeof(void*)*1, x_1683);
x_1685 = lean_array_get_size(x_1665);
x_1686 = lean_array_push(x_1665, x_1684);
if (lean_is_scalar(x_1666)) {
 x_1687 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1687 = x_1666;
 lean_ctor_set_tag(x_1687, 1);
}
lean_ctor_set(x_1687, 0, x_1685);
lean_ctor_set(x_1687, 1, x_1686);
x_1611 = x_1687;
x_1612 = x_1681;
goto block_1660;
}
}
else
{
lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; uint8_t x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; 
lean_dec(x_1610);
lean_dec(x_1291);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1688 = lean_ctor_get(x_1674, 0);
lean_inc(x_1688);
x_1689 = lean_ctor_get(x_1674, 1);
lean_inc(x_1689);
if (lean_is_exclusive(x_1674)) {
 lean_ctor_release(x_1674, 0);
 lean_ctor_release(x_1674, 1);
 x_1690 = x_1674;
} else {
 lean_dec_ref(x_1674);
 x_1690 = lean_box(0);
}
x_1691 = lean_io_error_to_string(x_1688);
x_1692 = 3;
x_1693 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1693, 0, x_1691);
lean_ctor_set_uint8(x_1693, sizeof(void*)*1, x_1692);
x_1694 = lean_array_get_size(x_1665);
x_1695 = lean_array_push(x_1665, x_1693);
if (lean_is_scalar(x_1666)) {
 x_1696 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1696 = x_1666;
 lean_ctor_set_tag(x_1696, 1);
}
lean_ctor_set(x_1696, 0, x_1694);
lean_ctor_set(x_1696, 1, x_1695);
if (lean_is_scalar(x_1690)) {
 x_1697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1697 = x_1690;
 lean_ctor_set_tag(x_1697, 0);
}
lean_ctor_set(x_1697, 0, x_1696);
lean_ctor_set(x_1697, 1, x_1689);
return x_1697;
}
}
else
{
lean_object* x_1698; lean_object* x_1699; lean_object* x_1700; uint8_t x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; 
lean_dec(x_1610);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1698 = lean_ctor_get(x_1661, 1);
lean_inc(x_1698);
if (lean_is_exclusive(x_1661)) {
 lean_ctor_release(x_1661, 0);
 lean_ctor_release(x_1661, 1);
 x_1699 = x_1661;
} else {
 lean_dec_ref(x_1661);
 x_1699 = lean_box(0);
}
x_1700 = lean_io_error_to_string(x_1664);
x_1701 = 3;
x_1702 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1702, 0, x_1700);
lean_ctor_set_uint8(x_1702, sizeof(void*)*1, x_1701);
x_1703 = lean_array_get_size(x_1698);
x_1704 = lean_array_push(x_1698, x_1702);
x_1705 = lean_io_prim_handle_unlock(x_1291, x_1662);
lean_dec(x_1291);
if (lean_obj_tag(x_1705) == 0)
{
lean_object* x_1706; lean_object* x_1707; 
x_1706 = lean_ctor_get(x_1705, 1);
lean_inc(x_1706);
lean_dec(x_1705);
x_1707 = lean_io_remove_file(x_23, x_1706);
lean_dec(x_23);
if (lean_obj_tag(x_1707) == 0)
{
lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; 
x_1708 = lean_ctor_get(x_1707, 1);
lean_inc(x_1708);
if (lean_is_exclusive(x_1707)) {
 lean_ctor_release(x_1707, 0);
 lean_ctor_release(x_1707, 1);
 x_1709 = x_1707;
} else {
 lean_dec_ref(x_1707);
 x_1709 = lean_box(0);
}
if (lean_is_scalar(x_1699)) {
 x_1710 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1710 = x_1699;
 lean_ctor_set_tag(x_1710, 1);
}
lean_ctor_set(x_1710, 0, x_1703);
lean_ctor_set(x_1710, 1, x_1704);
if (lean_is_scalar(x_1709)) {
 x_1711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1711 = x_1709;
}
lean_ctor_set(x_1711, 0, x_1710);
lean_ctor_set(x_1711, 1, x_1708);
return x_1711;
}
else
{
lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; lean_object* x_1719; 
x_1712 = lean_ctor_get(x_1707, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1707, 1);
lean_inc(x_1713);
if (lean_is_exclusive(x_1707)) {
 lean_ctor_release(x_1707, 0);
 lean_ctor_release(x_1707, 1);
 x_1714 = x_1707;
} else {
 lean_dec_ref(x_1707);
 x_1714 = lean_box(0);
}
x_1715 = lean_io_error_to_string(x_1712);
x_1716 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1716, 0, x_1715);
lean_ctor_set_uint8(x_1716, sizeof(void*)*1, x_1701);
x_1717 = lean_array_push(x_1704, x_1716);
if (lean_is_scalar(x_1699)) {
 x_1718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1718 = x_1699;
 lean_ctor_set_tag(x_1718, 1);
}
lean_ctor_set(x_1718, 0, x_1703);
lean_ctor_set(x_1718, 1, x_1717);
if (lean_is_scalar(x_1714)) {
 x_1719 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1719 = x_1714;
 lean_ctor_set_tag(x_1719, 0);
}
lean_ctor_set(x_1719, 0, x_1718);
lean_ctor_set(x_1719, 1, x_1713);
return x_1719;
}
}
else
{
lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; 
lean_dec(x_23);
x_1720 = lean_ctor_get(x_1705, 0);
lean_inc(x_1720);
x_1721 = lean_ctor_get(x_1705, 1);
lean_inc(x_1721);
if (lean_is_exclusive(x_1705)) {
 lean_ctor_release(x_1705, 0);
 lean_ctor_release(x_1705, 1);
 x_1722 = x_1705;
} else {
 lean_dec_ref(x_1705);
 x_1722 = lean_box(0);
}
x_1723 = lean_io_error_to_string(x_1720);
x_1724 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1724, 0, x_1723);
lean_ctor_set_uint8(x_1724, sizeof(void*)*1, x_1701);
x_1725 = lean_array_push(x_1704, x_1724);
if (lean_is_scalar(x_1699)) {
 x_1726 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1726 = x_1699;
 lean_ctor_set_tag(x_1726, 1);
}
lean_ctor_set(x_1726, 0, x_1703);
lean_ctor_set(x_1726, 1, x_1725);
if (lean_is_scalar(x_1722)) {
 x_1727 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1727 = x_1722;
 lean_ctor_set_tag(x_1727, 0);
}
lean_ctor_set(x_1727, 0, x_1726);
lean_ctor_set(x_1727, 1, x_1721);
return x_1727;
}
}
}
else
{
lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; 
lean_dec(x_1663);
lean_dec(x_23);
x_1728 = lean_ctor_get(x_1661, 1);
lean_inc(x_1728);
if (lean_is_exclusive(x_1661)) {
 lean_ctor_release(x_1661, 0);
 lean_ctor_release(x_1661, 1);
 x_1729 = x_1661;
} else {
 lean_dec_ref(x_1661);
 x_1729 = lean_box(0);
}
x_1730 = lean_ctor_get(x_1, 0);
lean_inc(x_1730);
x_1731 = l_Lake_Env_leanGithash(x_1730);
lean_dec(x_1730);
x_1732 = l_System_Platform_target;
lean_inc(x_1610);
x_1733 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1733, 0, x_1732);
lean_ctor_set(x_1733, 1, x_1731);
lean_ctor_set(x_1733, 2, x_29);
lean_ctor_set(x_1733, 3, x_1610);
x_1734 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_1733);
x_1735 = lean_unsigned_to_nat(80u);
x_1736 = l_Lean_Json_pretty(x_1734, x_1735);
x_1737 = l_IO_FS_Handle_putStrLn(x_1291, x_1736, x_1662);
if (lean_obj_tag(x_1737) == 0)
{
lean_object* x_1738; lean_object* x_1739; 
x_1738 = lean_ctor_get(x_1737, 1);
lean_inc(x_1738);
lean_dec(x_1737);
x_1739 = lean_io_prim_handle_truncate(x_1291, x_1738);
if (lean_obj_tag(x_1739) == 0)
{
lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; 
x_1740 = lean_ctor_get(x_1739, 0);
lean_inc(x_1740);
x_1741 = lean_ctor_get(x_1739, 1);
lean_inc(x_1741);
lean_dec(x_1739);
if (lean_is_scalar(x_1729)) {
 x_1742 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1742 = x_1729;
}
lean_ctor_set(x_1742, 0, x_1740);
lean_ctor_set(x_1742, 1, x_1728);
x_1611 = x_1742;
x_1612 = x_1741;
goto block_1660;
}
else
{
lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; uint8_t x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; 
x_1743 = lean_ctor_get(x_1739, 0);
lean_inc(x_1743);
x_1744 = lean_ctor_get(x_1739, 1);
lean_inc(x_1744);
lean_dec(x_1739);
x_1745 = lean_io_error_to_string(x_1743);
x_1746 = 3;
x_1747 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1747, 0, x_1745);
lean_ctor_set_uint8(x_1747, sizeof(void*)*1, x_1746);
x_1748 = lean_array_get_size(x_1728);
x_1749 = lean_array_push(x_1728, x_1747);
if (lean_is_scalar(x_1729)) {
 x_1750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1750 = x_1729;
 lean_ctor_set_tag(x_1750, 1);
}
lean_ctor_set(x_1750, 0, x_1748);
lean_ctor_set(x_1750, 1, x_1749);
x_1611 = x_1750;
x_1612 = x_1744;
goto block_1660;
}
}
else
{
lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; uint8_t x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; 
lean_dec(x_1610);
lean_dec(x_1291);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1751 = lean_ctor_get(x_1737, 0);
lean_inc(x_1751);
x_1752 = lean_ctor_get(x_1737, 1);
lean_inc(x_1752);
if (lean_is_exclusive(x_1737)) {
 lean_ctor_release(x_1737, 0);
 lean_ctor_release(x_1737, 1);
 x_1753 = x_1737;
} else {
 lean_dec_ref(x_1737);
 x_1753 = lean_box(0);
}
x_1754 = lean_io_error_to_string(x_1751);
x_1755 = 3;
x_1756 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1756, 0, x_1754);
lean_ctor_set_uint8(x_1756, sizeof(void*)*1, x_1755);
x_1757 = lean_array_get_size(x_1728);
x_1758 = lean_array_push(x_1728, x_1756);
if (lean_is_scalar(x_1729)) {
 x_1759 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1759 = x_1729;
 lean_ctor_set_tag(x_1759, 1);
}
lean_ctor_set(x_1759, 0, x_1757);
lean_ctor_set(x_1759, 1, x_1758);
if (lean_is_scalar(x_1753)) {
 x_1760 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1760 = x_1753;
 lean_ctor_set_tag(x_1760, 0);
}
lean_ctor_set(x_1760, 0, x_1759);
lean_ctor_set(x_1760, 1, x_1752);
return x_1760;
}
}
}
}
}
else
{
uint8_t x_1771; 
lean_dec(x_1292);
lean_dec(x_1291);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1771 = !lean_is_exclusive(x_1293);
if (x_1771 == 0)
{
lean_object* x_1772; 
x_1772 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1772, 0, x_1293);
lean_ctor_set(x_1772, 1, x_1294);
return x_1772;
}
else
{
lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; 
x_1773 = lean_ctor_get(x_1293, 0);
x_1774 = lean_ctor_get(x_1293, 1);
lean_inc(x_1774);
lean_inc(x_1773);
lean_dec(x_1293);
x_1775 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1775, 0, x_1773);
lean_ctor_set(x_1775, 1, x_1774);
x_1776 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1776, 0, x_1775);
lean_ctor_set(x_1776, 1, x_1294);
return x_1776;
}
}
}
}
else
{
lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; uint8_t x_1963; lean_object* x_1964; 
x_1789 = lean_ctor_get(x_1239, 1);
lean_inc(x_1789);
lean_dec(x_1239);
x_1790 = lean_ctor_get(x_1241, 0);
lean_inc(x_1790);
if (lean_is_exclusive(x_1241)) {
 lean_ctor_release(x_1241, 0);
 x_1791 = x_1241;
} else {
 lean_dec_ref(x_1241);
 x_1791 = lean_box(0);
}
x_1963 = 1;
x_1964 = lean_io_prim_handle_lock(x_1790, x_1963, x_1240);
if (lean_obj_tag(x_1964) == 0)
{
lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; 
x_1965 = lean_ctor_get(x_1964, 0);
lean_inc(x_1965);
x_1966 = lean_ctor_get(x_1964, 1);
lean_inc(x_1966);
lean_dec(x_1964);
x_1967 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1967, 0, x_1965);
lean_ctor_set(x_1967, 1, x_1789);
x_1792 = x_1967;
x_1793 = x_1966;
goto block_1962;
}
else
{
lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; uint8_t x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; 
x_1968 = lean_ctor_get(x_1964, 0);
lean_inc(x_1968);
x_1969 = lean_ctor_get(x_1964, 1);
lean_inc(x_1969);
lean_dec(x_1964);
x_1970 = lean_io_error_to_string(x_1968);
x_1971 = 3;
x_1972 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1972, 0, x_1970);
lean_ctor_set_uint8(x_1972, sizeof(void*)*1, x_1971);
x_1973 = lean_array_get_size(x_1789);
x_1974 = lean_array_push(x_1789, x_1972);
x_1975 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1975, 0, x_1973);
lean_ctor_set(x_1975, 1, x_1974);
x_1792 = x_1975;
x_1793 = x_1969;
goto block_1962;
}
block_1962:
{
if (lean_obj_tag(x_1792) == 0)
{
lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1847; lean_object* x_1848; lean_object* x_1948; 
x_1794 = lean_ctor_get(x_1792, 1);
lean_inc(x_1794);
if (lean_is_exclusive(x_1792)) {
 lean_ctor_release(x_1792, 0);
 lean_ctor_release(x_1792, 1);
 x_1795 = x_1792;
} else {
 lean_dec_ref(x_1792);
 x_1795 = lean_box(0);
}
x_1796 = lean_ctor_get(x_1, 4);
lean_inc(x_1796);
x_1948 = lean_io_remove_file(x_20, x_1793);
if (lean_obj_tag(x_1948) == 0)
{
lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; 
x_1949 = lean_ctor_get(x_1948, 0);
lean_inc(x_1949);
x_1950 = lean_ctor_get(x_1948, 1);
lean_inc(x_1950);
lean_dec(x_1948);
if (lean_is_scalar(x_1791)) {
 x_1951 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1951 = x_1791;
}
lean_ctor_set(x_1951, 0, x_1949);
if (lean_is_scalar(x_1795)) {
 x_1952 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1952 = x_1795;
}
lean_ctor_set(x_1952, 0, x_1951);
lean_ctor_set(x_1952, 1, x_1794);
x_1847 = x_1952;
x_1848 = x_1950;
goto block_1947;
}
else
{
lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; 
x_1953 = lean_ctor_get(x_1948, 0);
lean_inc(x_1953);
x_1954 = lean_ctor_get(x_1948, 1);
lean_inc(x_1954);
lean_dec(x_1948);
if (lean_is_scalar(x_1791)) {
 x_1955 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1955 = x_1791;
 lean_ctor_set_tag(x_1955, 0);
}
lean_ctor_set(x_1955, 0, x_1953);
if (lean_is_scalar(x_1795)) {
 x_1956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1956 = x_1795;
}
lean_ctor_set(x_1956, 0, x_1955);
lean_ctor_set(x_1956, 1, x_1794);
x_1847 = x_1956;
x_1848 = x_1954;
goto block_1947;
}
block_1846:
{
if (lean_obj_tag(x_1797) == 0)
{
lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; 
x_1799 = lean_ctor_get(x_1797, 1);
lean_inc(x_1799);
lean_dec(x_1797);
x_1800 = lean_ctor_get(x_1, 5);
lean_inc(x_1800);
lean_dec(x_1);
x_1801 = l_Lake_elabConfigFile(x_6, x_1796, x_1800, x_8, x_1799, x_1798);
x_1802 = lean_ctor_get(x_1801, 0);
lean_inc(x_1802);
if (lean_obj_tag(x_1802) == 0)
{
lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; 
x_1803 = lean_ctor_get(x_1801, 1);
lean_inc(x_1803);
lean_dec(x_1801);
x_1804 = lean_ctor_get(x_1802, 0);
lean_inc(x_1804);
x_1805 = lean_ctor_get(x_1802, 1);
lean_inc(x_1805);
if (lean_is_exclusive(x_1802)) {
 lean_ctor_release(x_1802, 0);
 lean_ctor_release(x_1802, 1);
 x_1806 = x_1802;
} else {
 lean_dec_ref(x_1802);
 x_1806 = lean_box(0);
}
lean_inc(x_1804);
x_1807 = lean_write_module(x_1804, x_20, x_1803);
if (lean_obj_tag(x_1807) == 0)
{
lean_object* x_1808; lean_object* x_1809; 
x_1808 = lean_ctor_get(x_1807, 1);
lean_inc(x_1808);
lean_dec(x_1807);
x_1809 = lean_io_prim_handle_unlock(x_1790, x_1808);
lean_dec(x_1790);
if (lean_obj_tag(x_1809) == 0)
{
lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; 
x_1810 = lean_ctor_get(x_1809, 1);
lean_inc(x_1810);
if (lean_is_exclusive(x_1809)) {
 lean_ctor_release(x_1809, 0);
 lean_ctor_release(x_1809, 1);
 x_1811 = x_1809;
} else {
 lean_dec_ref(x_1809);
 x_1811 = lean_box(0);
}
if (lean_is_scalar(x_1806)) {
 x_1812 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1812 = x_1806;
}
lean_ctor_set(x_1812, 0, x_1804);
lean_ctor_set(x_1812, 1, x_1805);
if (lean_is_scalar(x_1811)) {
 x_1813 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1813 = x_1811;
}
lean_ctor_set(x_1813, 0, x_1812);
lean_ctor_set(x_1813, 1, x_1810);
return x_1813;
}
else
{
lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; uint8_t x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; 
lean_dec(x_1804);
x_1814 = lean_ctor_get(x_1809, 0);
lean_inc(x_1814);
x_1815 = lean_ctor_get(x_1809, 1);
lean_inc(x_1815);
if (lean_is_exclusive(x_1809)) {
 lean_ctor_release(x_1809, 0);
 lean_ctor_release(x_1809, 1);
 x_1816 = x_1809;
} else {
 lean_dec_ref(x_1809);
 x_1816 = lean_box(0);
}
x_1817 = lean_io_error_to_string(x_1814);
x_1818 = 3;
x_1819 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1819, 0, x_1817);
lean_ctor_set_uint8(x_1819, sizeof(void*)*1, x_1818);
x_1820 = lean_array_get_size(x_1805);
x_1821 = lean_array_push(x_1805, x_1819);
if (lean_is_scalar(x_1806)) {
 x_1822 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1822 = x_1806;
 lean_ctor_set_tag(x_1822, 1);
}
lean_ctor_set(x_1822, 0, x_1820);
lean_ctor_set(x_1822, 1, x_1821);
if (lean_is_scalar(x_1816)) {
 x_1823 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1823 = x_1816;
 lean_ctor_set_tag(x_1823, 0);
}
lean_ctor_set(x_1823, 0, x_1822);
lean_ctor_set(x_1823, 1, x_1815);
return x_1823;
}
}
else
{
lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; uint8_t x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; 
lean_dec(x_1804);
lean_dec(x_1790);
x_1824 = lean_ctor_get(x_1807, 0);
lean_inc(x_1824);
x_1825 = lean_ctor_get(x_1807, 1);
lean_inc(x_1825);
if (lean_is_exclusive(x_1807)) {
 lean_ctor_release(x_1807, 0);
 lean_ctor_release(x_1807, 1);
 x_1826 = x_1807;
} else {
 lean_dec_ref(x_1807);
 x_1826 = lean_box(0);
}
x_1827 = lean_io_error_to_string(x_1824);
x_1828 = 3;
x_1829 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1829, 0, x_1827);
lean_ctor_set_uint8(x_1829, sizeof(void*)*1, x_1828);
x_1830 = lean_array_get_size(x_1805);
x_1831 = lean_array_push(x_1805, x_1829);
if (lean_is_scalar(x_1806)) {
 x_1832 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1832 = x_1806;
 lean_ctor_set_tag(x_1832, 1);
}
lean_ctor_set(x_1832, 0, x_1830);
lean_ctor_set(x_1832, 1, x_1831);
if (lean_is_scalar(x_1826)) {
 x_1833 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1833 = x_1826;
 lean_ctor_set_tag(x_1833, 0);
}
lean_ctor_set(x_1833, 0, x_1832);
lean_ctor_set(x_1833, 1, x_1825);
return x_1833;
}
}
else
{
lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; 
lean_dec(x_1790);
lean_dec(x_20);
x_1834 = lean_ctor_get(x_1801, 1);
lean_inc(x_1834);
if (lean_is_exclusive(x_1801)) {
 lean_ctor_release(x_1801, 0);
 lean_ctor_release(x_1801, 1);
 x_1835 = x_1801;
} else {
 lean_dec_ref(x_1801);
 x_1835 = lean_box(0);
}
x_1836 = lean_ctor_get(x_1802, 0);
lean_inc(x_1836);
x_1837 = lean_ctor_get(x_1802, 1);
lean_inc(x_1837);
if (lean_is_exclusive(x_1802)) {
 lean_ctor_release(x_1802, 0);
 lean_ctor_release(x_1802, 1);
 x_1838 = x_1802;
} else {
 lean_dec_ref(x_1802);
 x_1838 = lean_box(0);
}
if (lean_is_scalar(x_1838)) {
 x_1839 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1839 = x_1838;
}
lean_ctor_set(x_1839, 0, x_1836);
lean_ctor_set(x_1839, 1, x_1837);
if (lean_is_scalar(x_1835)) {
 x_1840 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1840 = x_1835;
}
lean_ctor_set(x_1840, 0, x_1839);
lean_ctor_set(x_1840, 1, x_1834);
return x_1840;
}
}
else
{
lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; 
lean_dec(x_1796);
lean_dec(x_1790);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1841 = lean_ctor_get(x_1797, 0);
lean_inc(x_1841);
x_1842 = lean_ctor_get(x_1797, 1);
lean_inc(x_1842);
if (lean_is_exclusive(x_1797)) {
 lean_ctor_release(x_1797, 0);
 lean_ctor_release(x_1797, 1);
 x_1843 = x_1797;
} else {
 lean_dec_ref(x_1797);
 x_1843 = lean_box(0);
}
if (lean_is_scalar(x_1843)) {
 x_1844 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1844 = x_1843;
}
lean_ctor_set(x_1844, 0, x_1841);
lean_ctor_set(x_1844, 1, x_1842);
x_1845 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1845, 0, x_1844);
lean_ctor_set(x_1845, 1, x_1798);
return x_1845;
}
}
block_1947:
{
lean_object* x_1849; 
x_1849 = lean_ctor_get(x_1847, 0);
lean_inc(x_1849);
if (lean_obj_tag(x_1849) == 0)
{
lean_object* x_1850; 
x_1850 = lean_ctor_get(x_1849, 0);
lean_inc(x_1850);
lean_dec(x_1849);
if (lean_obj_tag(x_1850) == 11)
{
lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; 
lean_dec(x_1850);
lean_dec(x_23);
x_1851 = lean_ctor_get(x_1847, 1);
lean_inc(x_1851);
if (lean_is_exclusive(x_1847)) {
 lean_ctor_release(x_1847, 0);
 lean_ctor_release(x_1847, 1);
 x_1852 = x_1847;
} else {
 lean_dec_ref(x_1847);
 x_1852 = lean_box(0);
}
x_1853 = lean_ctor_get(x_1, 0);
lean_inc(x_1853);
x_1854 = l_Lake_Env_leanGithash(x_1853);
lean_dec(x_1853);
x_1855 = l_System_Platform_target;
lean_inc(x_1796);
x_1856 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1856, 0, x_1855);
lean_ctor_set(x_1856, 1, x_1854);
lean_ctor_set(x_1856, 2, x_29);
lean_ctor_set(x_1856, 3, x_1796);
x_1857 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_1856);
x_1858 = lean_unsigned_to_nat(80u);
x_1859 = l_Lean_Json_pretty(x_1857, x_1858);
x_1860 = l_IO_FS_Handle_putStrLn(x_1790, x_1859, x_1848);
if (lean_obj_tag(x_1860) == 0)
{
lean_object* x_1861; lean_object* x_1862; 
x_1861 = lean_ctor_get(x_1860, 1);
lean_inc(x_1861);
lean_dec(x_1860);
x_1862 = lean_io_prim_handle_truncate(x_1790, x_1861);
if (lean_obj_tag(x_1862) == 0)
{
lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; 
x_1863 = lean_ctor_get(x_1862, 0);
lean_inc(x_1863);
x_1864 = lean_ctor_get(x_1862, 1);
lean_inc(x_1864);
lean_dec(x_1862);
if (lean_is_scalar(x_1852)) {
 x_1865 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1865 = x_1852;
}
lean_ctor_set(x_1865, 0, x_1863);
lean_ctor_set(x_1865, 1, x_1851);
x_1797 = x_1865;
x_1798 = x_1864;
goto block_1846;
}
else
{
lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; uint8_t x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; 
x_1866 = lean_ctor_get(x_1862, 0);
lean_inc(x_1866);
x_1867 = lean_ctor_get(x_1862, 1);
lean_inc(x_1867);
lean_dec(x_1862);
x_1868 = lean_io_error_to_string(x_1866);
x_1869 = 3;
x_1870 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1870, 0, x_1868);
lean_ctor_set_uint8(x_1870, sizeof(void*)*1, x_1869);
x_1871 = lean_array_get_size(x_1851);
x_1872 = lean_array_push(x_1851, x_1870);
if (lean_is_scalar(x_1852)) {
 x_1873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1873 = x_1852;
 lean_ctor_set_tag(x_1873, 1);
}
lean_ctor_set(x_1873, 0, x_1871);
lean_ctor_set(x_1873, 1, x_1872);
x_1797 = x_1873;
x_1798 = x_1867;
goto block_1846;
}
}
else
{
lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; uint8_t x_1878; lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; 
lean_dec(x_1796);
lean_dec(x_1790);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1874 = lean_ctor_get(x_1860, 0);
lean_inc(x_1874);
x_1875 = lean_ctor_get(x_1860, 1);
lean_inc(x_1875);
if (lean_is_exclusive(x_1860)) {
 lean_ctor_release(x_1860, 0);
 lean_ctor_release(x_1860, 1);
 x_1876 = x_1860;
} else {
 lean_dec_ref(x_1860);
 x_1876 = lean_box(0);
}
x_1877 = lean_io_error_to_string(x_1874);
x_1878 = 3;
x_1879 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1879, 0, x_1877);
lean_ctor_set_uint8(x_1879, sizeof(void*)*1, x_1878);
x_1880 = lean_array_get_size(x_1851);
x_1881 = lean_array_push(x_1851, x_1879);
if (lean_is_scalar(x_1852)) {
 x_1882 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1882 = x_1852;
 lean_ctor_set_tag(x_1882, 1);
}
lean_ctor_set(x_1882, 0, x_1880);
lean_ctor_set(x_1882, 1, x_1881);
if (lean_is_scalar(x_1876)) {
 x_1883 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1883 = x_1876;
 lean_ctor_set_tag(x_1883, 0);
}
lean_ctor_set(x_1883, 0, x_1882);
lean_ctor_set(x_1883, 1, x_1875);
return x_1883;
}
}
else
{
lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; uint8_t x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; 
lean_dec(x_1796);
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1884 = lean_ctor_get(x_1847, 1);
lean_inc(x_1884);
if (lean_is_exclusive(x_1847)) {
 lean_ctor_release(x_1847, 0);
 lean_ctor_release(x_1847, 1);
 x_1885 = x_1847;
} else {
 lean_dec_ref(x_1847);
 x_1885 = lean_box(0);
}
x_1886 = lean_io_error_to_string(x_1850);
x_1887 = 3;
x_1888 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1888, 0, x_1886);
lean_ctor_set_uint8(x_1888, sizeof(void*)*1, x_1887);
x_1889 = lean_array_get_size(x_1884);
x_1890 = lean_array_push(x_1884, x_1888);
x_1891 = lean_io_prim_handle_unlock(x_1790, x_1848);
lean_dec(x_1790);
if (lean_obj_tag(x_1891) == 0)
{
lean_object* x_1892; lean_object* x_1893; 
x_1892 = lean_ctor_get(x_1891, 1);
lean_inc(x_1892);
lean_dec(x_1891);
x_1893 = lean_io_remove_file(x_23, x_1892);
lean_dec(x_23);
if (lean_obj_tag(x_1893) == 0)
{
lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; 
x_1894 = lean_ctor_get(x_1893, 1);
lean_inc(x_1894);
if (lean_is_exclusive(x_1893)) {
 lean_ctor_release(x_1893, 0);
 lean_ctor_release(x_1893, 1);
 x_1895 = x_1893;
} else {
 lean_dec_ref(x_1893);
 x_1895 = lean_box(0);
}
if (lean_is_scalar(x_1885)) {
 x_1896 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1896 = x_1885;
 lean_ctor_set_tag(x_1896, 1);
}
lean_ctor_set(x_1896, 0, x_1889);
lean_ctor_set(x_1896, 1, x_1890);
if (lean_is_scalar(x_1895)) {
 x_1897 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1897 = x_1895;
}
lean_ctor_set(x_1897, 0, x_1896);
lean_ctor_set(x_1897, 1, x_1894);
return x_1897;
}
else
{
lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; 
x_1898 = lean_ctor_get(x_1893, 0);
lean_inc(x_1898);
x_1899 = lean_ctor_get(x_1893, 1);
lean_inc(x_1899);
if (lean_is_exclusive(x_1893)) {
 lean_ctor_release(x_1893, 0);
 lean_ctor_release(x_1893, 1);
 x_1900 = x_1893;
} else {
 lean_dec_ref(x_1893);
 x_1900 = lean_box(0);
}
x_1901 = lean_io_error_to_string(x_1898);
x_1902 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1902, 0, x_1901);
lean_ctor_set_uint8(x_1902, sizeof(void*)*1, x_1887);
x_1903 = lean_array_push(x_1890, x_1902);
if (lean_is_scalar(x_1885)) {
 x_1904 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1904 = x_1885;
 lean_ctor_set_tag(x_1904, 1);
}
lean_ctor_set(x_1904, 0, x_1889);
lean_ctor_set(x_1904, 1, x_1903);
if (lean_is_scalar(x_1900)) {
 x_1905 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1905 = x_1900;
 lean_ctor_set_tag(x_1905, 0);
}
lean_ctor_set(x_1905, 0, x_1904);
lean_ctor_set(x_1905, 1, x_1899);
return x_1905;
}
}
else
{
lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; lean_object* x_1913; 
lean_dec(x_23);
x_1906 = lean_ctor_get(x_1891, 0);
lean_inc(x_1906);
x_1907 = lean_ctor_get(x_1891, 1);
lean_inc(x_1907);
if (lean_is_exclusive(x_1891)) {
 lean_ctor_release(x_1891, 0);
 lean_ctor_release(x_1891, 1);
 x_1908 = x_1891;
} else {
 lean_dec_ref(x_1891);
 x_1908 = lean_box(0);
}
x_1909 = lean_io_error_to_string(x_1906);
x_1910 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1910, 0, x_1909);
lean_ctor_set_uint8(x_1910, sizeof(void*)*1, x_1887);
x_1911 = lean_array_push(x_1890, x_1910);
if (lean_is_scalar(x_1885)) {
 x_1912 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1912 = x_1885;
 lean_ctor_set_tag(x_1912, 1);
}
lean_ctor_set(x_1912, 0, x_1889);
lean_ctor_set(x_1912, 1, x_1911);
if (lean_is_scalar(x_1908)) {
 x_1913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1913 = x_1908;
 lean_ctor_set_tag(x_1913, 0);
}
lean_ctor_set(x_1913, 0, x_1912);
lean_ctor_set(x_1913, 1, x_1907);
return x_1913;
}
}
}
else
{
lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; 
lean_dec(x_1849);
lean_dec(x_23);
x_1914 = lean_ctor_get(x_1847, 1);
lean_inc(x_1914);
if (lean_is_exclusive(x_1847)) {
 lean_ctor_release(x_1847, 0);
 lean_ctor_release(x_1847, 1);
 x_1915 = x_1847;
} else {
 lean_dec_ref(x_1847);
 x_1915 = lean_box(0);
}
x_1916 = lean_ctor_get(x_1, 0);
lean_inc(x_1916);
x_1917 = l_Lake_Env_leanGithash(x_1916);
lean_dec(x_1916);
x_1918 = l_System_Platform_target;
lean_inc(x_1796);
x_1919 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1919, 0, x_1918);
lean_ctor_set(x_1919, 1, x_1917);
lean_ctor_set(x_1919, 2, x_29);
lean_ctor_set(x_1919, 3, x_1796);
x_1920 = l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059_(x_1919);
x_1921 = lean_unsigned_to_nat(80u);
x_1922 = l_Lean_Json_pretty(x_1920, x_1921);
x_1923 = l_IO_FS_Handle_putStrLn(x_1790, x_1922, x_1848);
if (lean_obj_tag(x_1923) == 0)
{
lean_object* x_1924; lean_object* x_1925; 
x_1924 = lean_ctor_get(x_1923, 1);
lean_inc(x_1924);
lean_dec(x_1923);
x_1925 = lean_io_prim_handle_truncate(x_1790, x_1924);
if (lean_obj_tag(x_1925) == 0)
{
lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; 
x_1926 = lean_ctor_get(x_1925, 0);
lean_inc(x_1926);
x_1927 = lean_ctor_get(x_1925, 1);
lean_inc(x_1927);
lean_dec(x_1925);
if (lean_is_scalar(x_1915)) {
 x_1928 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1928 = x_1915;
}
lean_ctor_set(x_1928, 0, x_1926);
lean_ctor_set(x_1928, 1, x_1914);
x_1797 = x_1928;
x_1798 = x_1927;
goto block_1846;
}
else
{
lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; uint8_t x_1932; lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; 
x_1929 = lean_ctor_get(x_1925, 0);
lean_inc(x_1929);
x_1930 = lean_ctor_get(x_1925, 1);
lean_inc(x_1930);
lean_dec(x_1925);
x_1931 = lean_io_error_to_string(x_1929);
x_1932 = 3;
x_1933 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1933, 0, x_1931);
lean_ctor_set_uint8(x_1933, sizeof(void*)*1, x_1932);
x_1934 = lean_array_get_size(x_1914);
x_1935 = lean_array_push(x_1914, x_1933);
if (lean_is_scalar(x_1915)) {
 x_1936 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1936 = x_1915;
 lean_ctor_set_tag(x_1936, 1);
}
lean_ctor_set(x_1936, 0, x_1934);
lean_ctor_set(x_1936, 1, x_1935);
x_1797 = x_1936;
x_1798 = x_1930;
goto block_1846;
}
}
else
{
lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; uint8_t x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; 
lean_dec(x_1796);
lean_dec(x_1790);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1937 = lean_ctor_get(x_1923, 0);
lean_inc(x_1937);
x_1938 = lean_ctor_get(x_1923, 1);
lean_inc(x_1938);
if (lean_is_exclusive(x_1923)) {
 lean_ctor_release(x_1923, 0);
 lean_ctor_release(x_1923, 1);
 x_1939 = x_1923;
} else {
 lean_dec_ref(x_1923);
 x_1939 = lean_box(0);
}
x_1940 = lean_io_error_to_string(x_1937);
x_1941 = 3;
x_1942 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1942, 0, x_1940);
lean_ctor_set_uint8(x_1942, sizeof(void*)*1, x_1941);
x_1943 = lean_array_get_size(x_1914);
x_1944 = lean_array_push(x_1914, x_1942);
if (lean_is_scalar(x_1915)) {
 x_1945 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1945 = x_1915;
 lean_ctor_set_tag(x_1945, 1);
}
lean_ctor_set(x_1945, 0, x_1943);
lean_ctor_set(x_1945, 1, x_1944);
if (lean_is_scalar(x_1939)) {
 x_1946 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1946 = x_1939;
 lean_ctor_set_tag(x_1946, 0);
}
lean_ctor_set(x_1946, 0, x_1945);
lean_ctor_set(x_1946, 1, x_1938);
return x_1946;
}
}
}
}
else
{
lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; 
lean_dec(x_1791);
lean_dec(x_1790);
lean_dec(x_29);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1957 = lean_ctor_get(x_1792, 0);
lean_inc(x_1957);
x_1958 = lean_ctor_get(x_1792, 1);
lean_inc(x_1958);
if (lean_is_exclusive(x_1792)) {
 lean_ctor_release(x_1792, 0);
 lean_ctor_release(x_1792, 1);
 x_1959 = x_1792;
} else {
 lean_dec_ref(x_1792);
 x_1959 = lean_box(0);
}
if (lean_is_scalar(x_1959)) {
 x_1960 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1960 = x_1959;
}
lean_ctor_set(x_1960, 0, x_1957);
lean_ctor_set(x_1960, 1, x_1958);
x_1961 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1961, 0, x_1960);
lean_ctor_set(x_1961, 1, x_1793);
return x_1961;
}
}
}
}
}
}
else
{
uint8_t x_2024; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_2024 = !lean_is_exclusive(x_27);
if (x_2024 == 0)
{
lean_object* x_2025; 
x_2025 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2025, 0, x_27);
lean_ctor_set(x_2025, 1, x_28);
return x_2025;
}
else
{
lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; 
x_2026 = lean_ctor_get(x_27, 0);
x_2027 = lean_ctor_get(x_27, 1);
lean_inc(x_2027);
lean_inc(x_2026);
lean_dec(x_27);
x_2028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2028, 0, x_2026);
lean_ctor_set(x_2028, 1, x_2027);
x_2029 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2029, 0, x_2028);
lean_ctor_set(x_2029, 1, x_28);
return x_2029;
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
LEAN_EXPORT lean_object* initialize_Lake_Load_Elab(uint8_t builtin, lean_object* w) {
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
res = l_Lake_initFn____x40_Lake_Load_Elab___hyg_123_(lean_io_mk_world());
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
l_Lake_importConfigFileCore_lakeExts = _init_l_Lake_importConfigFileCore_lakeExts();
lean_mark_persistent(l_Lake_importConfigFileCore_lakeExts);
l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___closed__1);
l_Lake_importConfigFileCore___closed__1 = _init_l_Lake_importConfigFileCore___closed__1();
lean_mark_persistent(l_Lake_importConfigFileCore___closed__1);
l_Lake_instFromJsonHash___closed__1 = _init_l_Lake_instFromJsonHash___closed__1();
lean_mark_persistent(l_Lake_instFromJsonHash___closed__1);
l_Lake_instFromJsonHash___closed__2 = _init_l_Lake_instFromJsonHash___closed__2();
lean_mark_persistent(l_Lake_instFromJsonHash___closed__2);
l_Lake_instFromJsonHash___closed__3 = _init_l_Lake_instFromJsonHash___closed__3();
lean_mark_persistent(l_Lake_instFromJsonHash___closed__3);
l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__1 = _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__1();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__1);
l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__2 = _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__2();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__2);
l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__3 = _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__3();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__3);
l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__4 = _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__4();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__4);
l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__5 = _init_l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__5();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Elab___hyg_1059____closed__5);
l_Lake_instToJsonConfigTrace___closed__1 = _init_l_Lake_instToJsonConfigTrace___closed__1();
lean_mark_persistent(l_Lake_instToJsonConfigTrace___closed__1);
l_Lake_instToJsonConfigTrace = _init_l_Lake_instToJsonConfigTrace();
lean_mark_persistent(l_Lake_instToJsonConfigTrace);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__1 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__1();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__1);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__2 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__2();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__2);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__3 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__3();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__3);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__4 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__4();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__4);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__5 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__5();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__5);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__6 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__6();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__6);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__7 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__7();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__7);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__8 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__8();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__8);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__9 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__9();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__9);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__10 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__10();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__10);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__11 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__11();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__11);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__12 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__12();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__12);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__13 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__13();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__13);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__14 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__14();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__14);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__15 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__15();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__15);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__16 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__16();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__16);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__17 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__17();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__17);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__18 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__18();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__18);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__19 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__19();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__19);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__20 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__20();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__20);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__21 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__21();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__21);
l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__22 = _init_l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__22();
lean_mark_persistent(l___private_Lake_Load_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Elab___hyg_1133____closed__22);
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
