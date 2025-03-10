// Lean compiler output
// Module: Lake.Load.Lean.Elab
// Imports: Lean.Elab.Frontend Lake.DSL.Extensions Lake.DSL.Attributes Lake.Load.Config Lake.Build.Trace Lake.Util.Log
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
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__20;
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__40;
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t, lean_object*);
lean_object* lean_read_module_data(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_unlock(lean_object*, lean_object*);
extern lean_object* l_Lake_dirExt;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__17;
static lean_object* l_Lake_instHashableImport__lake___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_80____boxed(lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3;
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lake_instBEqImport__lake;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__49;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_instInhabitedEnvExtensionState;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__8;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__3;
static lean_object* l_Lake_importConfigFile___closed__10;
lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__11;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__39;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_mkExtNameMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166_(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__2;
static lean_object* l_Lake_importConfigFile___closed__9;
static lean_object* l_Lake_instToJsonConfigTrace___closed__1;
static lean_object* l_Lake_configModuleName___closed__2;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lake_importConfigFile___closed__4;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_elabConfigFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__52;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__3;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__11;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__12;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__14;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__6;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__12;
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_headerToImports(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__22;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__29;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__17;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_optsExt;
lean_object* l_Lean_Environment_enableRealizationsForImports(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__6___at_Lake_importModulesUsingCache___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__19;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__21;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__10;
static lean_object* l_Lake_importConfigFileCore___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__15;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__21;
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__5;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__10;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__24;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__51;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____lambda__1___boxed(lean_object*);
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__13;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__12;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_elabConfigFile___closed__2;
static lean_object* l_Lake_instBEqImport__lake___closed__1;
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121_(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__43;
lean_object* l_Lean_MessageLog_toList(lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__18;
static uint64_t l_Lake_importModulesUsingCache___closed__4;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__22;
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__1;
static lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__3;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__4;
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__32;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__34;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__23;
static uint64_t l_Lake_importModulesUsingCache___closed__3;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__18;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__5;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_processHeader___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__38;
LEAN_EXPORT uint64_t l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_80_(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonConfigTrace___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__27;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__2___boxed(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__16;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__31;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__19;
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__7;
LEAN_EXPORT lean_object* l_Lake_instFromJsonConfigTrace;
lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_configModuleName___closed__1;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__14;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___lambda__1(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__4;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__35;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__41;
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
static uint64_t l_Lake_importModulesUsingCache___closed__2;
LEAN_EXPORT lean_object* l_Lake_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__53;
LEAN_EXPORT lean_object* l_Lake_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__50;
LEAN_EXPORT lean_object* l_Lake_instToJsonConfigTrace;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__47;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__25;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__2;
static lean_object* l_Lake_elabConfigFile___closed__1;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__9;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_importModulesUsingCache___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__6(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__3;
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__37;
static lean_object* l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1;
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__8;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__45;
lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__3;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__1;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__23;
static lean_object* l_Lake_importConfigFile___closed__1;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__33;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importEnvCache;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__44;
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__16;
lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__20;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__7;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__6;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__30;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static size_t l_Lake_importModulesUsingCache___closed__5;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__48;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__11;
lean_object* l_Lean_Json_Parser_any(lean_object*);
static lean_object* l_Lake_importConfigFile___closed__8;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__42;
lean_object* l_List_flatMapTR_go___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55____spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_bignumToJson(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__46;
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__2;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__9;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_elabConfigFile___closed__3;
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__2(lean_object*, lean_object*);
static uint64_t l_Lake_importModulesUsingCache___closed__1;
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore_lakeExts;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_write_module(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__2;
LEAN_EXPORT lean_object* l_Lake_instHashableImport__lake;
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__2;
lean_object* lean_io_prim_handle_truncate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configModuleName;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importModulesUsingCache___lambda__1___closed__2;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__26;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__36;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_importModulesUsingCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_import_modules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__54;
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(lean_object*, size_t, size_t, uint64_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lake_environment_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__28;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__13;
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_importModulesUsingCache___spec__3(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l_Lake_importConfigFile___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__15;
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10(lean_object*, lean_object*);
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
LEAN_EXPORT uint64_t l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_80_(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_80____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_80_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instHashableImport__lake___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_80____boxed), 1, 0);
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
static lean_object* _init_l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__3;
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_array_fget(x_4, x_11);
x_13 = lean_array_fget(x_5, x_11);
x_14 = l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
x_3 = lean_box(0);
x_6 = x_11;
x_7 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = 1;
return x_17;
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1(lean_object* x_1, lean_object* x_2) {
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
if (x_8 == 0)
{
lean_dec(x_6);
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_10; 
x_10 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__2(x_1, x_4, lean_box(0), x_4, x_1, x_6, lean_box(0));
if (x_10 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = 1;
return x_12;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_80_(x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__6___at_Lake_importModulesUsingCache___spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; uint64_t x_17; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 lean_ctor_release(x_2, 2);
 x_6 = x_2;
} else {
 lean_dec_ref(x_2);
 x_6 = lean_box(0);
}
x_7 = lean_array_get_size(x_1);
x_8 = 7;
x_9 = lean_array_get_size(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
x_12 = 32;
x_13 = 16;
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = 1;
x_16 = lean_usize_sub(x_14, x_15);
if (x_11 == 0)
{
lean_dec(x_9);
x_17 = x_8;
goto block_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_9, x_9);
if (x_29 == 0)
{
lean_dec(x_9);
x_17 = x_8;
goto block_28;
}
else
{
size_t x_30; size_t x_31; uint64_t x_32; 
x_30 = 0;
x_31 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_32 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(x_3, x_30, x_31, x_8);
x_17 = x_32;
goto block_28;
}
}
block_28:
{
uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_uint64_shift_right(x_17, x_12);
x_19 = lean_uint64_xor(x_17, x_18);
x_20 = lean_uint64_shift_right(x_19, x_13);
x_21 = lean_uint64_xor(x_19, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_land(x_22, x_16);
x_24 = lean_array_uget(x_1, x_23);
if (lean_is_scalar(x_6)) {
 x_25 = lean_alloc_ctor(1, 3, 0);
} else {
 x_25 = x_6;
}
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_array_uset(x_1, x_23, x_25);
x_1 = x_26;
x_2 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_importModulesUsingCache___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__6___at_Lake_importModulesUsingCache___spec__7(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_importModulesUsingCache___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_importModulesUsingCache___spec__4(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_array_fget(x_4, x_11);
x_13 = lean_array_fget(x_5, x_11);
x_14 = l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
x_3 = lean_box(0);
x_6 = x_11;
x_7 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = 1;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_12);
return x_3;
}
else
{
uint8_t x_13; 
x_13 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__9(x_1, x_6, lean_box(0), x_6, x_1, x_9, lean_box(0));
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_14);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 2);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_3);
x_18 = lean_array_get_size(x_15);
x_19 = lean_array_get_size(x_1);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
x_21 = l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(x_1, x_2, x_17);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_21);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__9(x_1, x_15, lean_box(0), x_15, x_1, x_18, lean_box(0));
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(x_1, x_2, x_17);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_15);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_24);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_16);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_17);
return x_26;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_array_fget(x_4, x_11);
x_13 = lean_array_fget(x_5, x_11);
x_14 = l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
x_3 = lean_box(0);
x_6 = x_11;
x_7 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = 1;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10(lean_object* x_1, lean_object* x_2) {
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
if (x_9 == 0)
{
lean_dec(x_7);
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__11(x_1, x_4, lean_box(0), x_4, x_1, x_7, lean_box(0));
if (x_11 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_13; 
lean_inc(x_5);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_5);
return x_13;
}
}
}
}
}
static lean_object* _init_l_Lake_importModulesUsingCache___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_importModulesUsingCache___lambda__1___closed__2() {
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = l_Lake_importModulesUsingCache___lambda__1___closed__1;
x_7 = 0;
lean_inc(x_1);
x_8 = lean_import_modules(x_1, x_2, x_3, x_6, x_7, x_5);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; uint64_t x_28; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lake_importModulesUsingCache___lambda__1___closed__2;
x_12 = lean_st_ref_take(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_17 = x_13;
} else {
 lean_dec_ref(x_13);
 x_17 = lean_box(0);
}
x_18 = lean_array_get_size(x_16);
x_19 = 7;
x_20 = lean_array_get_size(x_1);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_lt(x_21, x_20);
x_23 = 32;
x_24 = 16;
x_25 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_26 = 1;
x_27 = lean_usize_sub(x_25, x_26);
if (x_22 == 0)
{
lean_dec(x_20);
x_28 = x_19;
goto block_70;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_20, x_20);
if (x_71 == 0)
{
lean_dec(x_20);
x_28 = x_19;
goto block_70;
}
else
{
size_t x_72; size_t x_73; uint64_t x_74; 
x_72 = 0;
x_73 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_74 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(x_1, x_72, x_73, x_19);
x_28 = x_74;
goto block_70;
}
}
block_70:
{
uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; lean_object* x_35; uint8_t x_36; 
x_29 = lean_uint64_shift_right(x_28, x_23);
x_30 = lean_uint64_xor(x_28, x_29);
x_31 = lean_uint64_shift_right(x_30, x_24);
x_32 = lean_uint64_xor(x_30, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_land(x_33, x_27);
x_35 = lean_array_uget(x_16, x_34);
x_36 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1(x_1, x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_15, x_37);
lean_dec(x_15);
lean_inc(x_9);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_9);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_array_uset(x_16, x_34, x_39);
x_41 = lean_unsigned_to_nat(4u);
x_42 = lean_nat_mul(x_38, x_41);
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_nat_div(x_42, x_43);
lean_dec(x_42);
x_45 = lean_array_get_size(x_40);
x_46 = lean_nat_dec_le(x_44, x_45);
lean_dec(x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_importModulesUsingCache___spec__3(x_40);
if (lean_is_scalar(x_17)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_17;
}
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_st_ref_set(x_11, x_48, x_14);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_9);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_9);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
if (lean_is_scalar(x_17)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_17;
}
lean_ctor_set(x_54, 0, x_38);
lean_ctor_set(x_54, 1, x_40);
x_55 = lean_st_ref_set(x_11, x_54, x_14);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_9);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_9);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_60 = lean_box(0);
x_61 = lean_array_uset(x_16, x_34, x_60);
lean_inc(x_9);
x_62 = l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(x_1, x_9, x_35);
x_63 = lean_array_uset(x_61, x_34, x_62);
if (lean_is_scalar(x_17)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_17;
}
lean_ctor_set(x_64, 0, x_15);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_st_ref_set(x_11, x_64, x_14);
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_65, 0);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_9);
return x_65;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_9);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_8);
if (x_75 == 0)
{
return x_8;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_8, 0);
x_77 = lean_ctor_get(x_8, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_8);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
static uint64_t _init_l_Lake_importModulesUsingCache___closed__1() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 7;
x_2 = 32;
x_3 = lean_uint64_shift_right(x_1, x_2);
return x_3;
}
}
static uint64_t _init_l_Lake_importModulesUsingCache___closed__2() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 7;
x_2 = l_Lake_importModulesUsingCache___closed__1;
x_3 = lean_uint64_xor(x_1, x_2);
return x_3;
}
}
static uint64_t _init_l_Lake_importModulesUsingCache___closed__3() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = 16;
x_2 = l_Lake_importModulesUsingCache___closed__2;
x_3 = lean_uint64_shift_right(x_2, x_1);
return x_3;
}
}
static uint64_t _init_l_Lake_importModulesUsingCache___closed__4() {
_start:
{
uint64_t x_1; uint64_t x_2; uint64_t x_3; 
x_1 = l_Lake_importModulesUsingCache___closed__2;
x_2 = l_Lake_importModulesUsingCache___closed__3;
x_3 = lean_uint64_xor(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lake_importModulesUsingCache___closed__5() {
_start:
{
uint64_t x_1; size_t x_2; 
x_1 = l_Lake_importModulesUsingCache___closed__4;
x_2 = lean_uint64_to_usize(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object* x_1, lean_object* x_2, uint32_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lake_importModulesUsingCache___lambda__1___closed__2;
x_6 = lean_st_ref_get(x_5, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_get_size(x_10);
x_12 = 7;
x_13 = lean_array_get_size(x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_lt(x_14, x_13);
x_16 = 32;
x_17 = 16;
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = 1;
x_20 = lean_usize_sub(x_18, x_19);
if (x_15 == 0)
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
x_21 = l_Lake_importModulesUsingCache___closed__5;
x_22 = lean_usize_land(x_21, x_20);
x_23 = lean_array_uget(x_10, x_22);
lean_dec(x_10);
x_24 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10(x_1, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_6);
x_25 = lean_box(0);
x_26 = l_Lake_importModulesUsingCache___lambda__1(x_1, x_2, x_3, x_25, x_9);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
lean_ctor_set(x_6, 0, x_27);
return x_6;
}
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_le(x_13, x_13);
if (x_28 == 0)
{
size_t x_29; size_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
x_29 = l_Lake_importModulesUsingCache___closed__5;
x_30 = lean_usize_land(x_29, x_20);
x_31 = lean_array_uget(x_10, x_30);
lean_dec(x_10);
x_32 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10(x_1, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_free_object(x_6);
x_33 = lean_box(0);
x_34 = l_Lake_importModulesUsingCache___lambda__1(x_1, x_2, x_3, x_33, x_9);
return x_34;
}
else
{
lean_object* x_35; 
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_dec(x_32);
lean_ctor_set(x_6, 0, x_35);
return x_6;
}
}
else
{
size_t x_36; size_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_38 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(x_1, x_36, x_37, x_12);
x_39 = lean_uint64_shift_right(x_38, x_16);
x_40 = lean_uint64_xor(x_38, x_39);
x_41 = lean_uint64_shift_right(x_40, x_17);
x_42 = lean_uint64_xor(x_40, x_41);
x_43 = lean_uint64_to_usize(x_42);
x_44 = lean_usize_land(x_43, x_20);
x_45 = lean_array_uget(x_10, x_44);
lean_dec(x_10);
x_46 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10(x_1, x_45);
lean_dec(x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_free_object(x_6);
x_47 = lean_box(0);
x_48 = l_Lake_importModulesUsingCache___lambda__1(x_1, x_2, x_3, x_47, x_9);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
lean_ctor_set(x_6, 0, x_49);
return x_6;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; uint64_t x_58; uint64_t x_59; size_t x_60; size_t x_61; size_t x_62; 
x_50 = lean_ctor_get(x_6, 0);
x_51 = lean_ctor_get(x_6, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_6);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_array_get_size(x_52);
x_54 = 7;
x_55 = lean_array_get_size(x_1);
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_nat_dec_lt(x_56, x_55);
x_58 = 32;
x_59 = 16;
x_60 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_61 = 1;
x_62 = lean_usize_sub(x_60, x_61);
if (x_57 == 0)
{
size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
x_63 = l_Lake_importModulesUsingCache___closed__5;
x_64 = lean_usize_land(x_63, x_62);
x_65 = lean_array_uget(x_52, x_64);
lean_dec(x_52);
x_66 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10(x_1, x_65);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_box(0);
x_68 = l_Lake_importModulesUsingCache___lambda__1(x_1, x_2, x_3, x_67, x_51);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_51);
return x_70;
}
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_55, x_55);
if (x_71 == 0)
{
size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_55);
x_72 = l_Lake_importModulesUsingCache___closed__5;
x_73 = lean_usize_land(x_72, x_62);
x_74 = lean_array_uget(x_52, x_73);
lean_dec(x_52);
x_75 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10(x_1, x_74);
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_box(0);
x_77 = l_Lake_importModulesUsingCache___lambda__1(x_1, x_2, x_3, x_76, x_51);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_ctor_get(x_75, 0);
lean_inc(x_78);
lean_dec(x_75);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_51);
return x_79;
}
}
else
{
size_t x_80; size_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; 
x_80 = 0;
x_81 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_82 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(x_1, x_80, x_81, x_54);
x_83 = lean_uint64_shift_right(x_82, x_58);
x_84 = lean_uint64_xor(x_82, x_83);
x_85 = lean_uint64_shift_right(x_84, x_59);
x_86 = lean_uint64_xor(x_84, x_85);
x_87 = lean_uint64_to_usize(x_86);
x_88 = lean_usize_land(x_87, x_62);
x_89 = lean_array_uget(x_52, x_88);
lean_dec(x_52);
x_90 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10(x_1, x_89);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_box(0);
x_92 = l_Lake_importModulesUsingCache___lambda__1(x_1, x_2, x_3, x_91, x_51);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_51);
return x_94;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10(x_1, x_2);
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
x_1 = lean_mk_string_unchecked("", 0, 0);
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
x_34 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_22);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_34, 4, x_25);
lean_ctor_set_uint8(x_34, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_34, sizeof(void*)*5 + 1, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*5 + 2, x_19);
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
x_43 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_43, 0, x_21);
lean_ctor_set(x_43, 1, x_40);
lean_ctor_set(x_43, 2, x_22);
lean_ctor_set(x_43, 3, x_42);
lean_ctor_set(x_43, 4, x_25);
lean_ctor_set_uint8(x_43, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 1, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*5 + 2, x_19);
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
x_57 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_22);
lean_ctor_set(x_57, 3, x_56);
lean_ctor_set(x_57, 4, x_25);
lean_ctor_set_uint8(x_57, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_57, sizeof(void*)*5 + 1, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*5 + 2, x_19);
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
x_65 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_65, 0, x_21);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_65, 2, x_22);
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_65, 4, x_25);
lean_ctor_set_uint8(x_65, sizeof(void*)*5, x_19);
lean_ctor_set_uint8(x_65, sizeof(void*)*5 + 1, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*5 + 2, x_19);
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
x_1 = lean_mk_string_unchecked("lakefile", 8, 8);
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
static lean_object* _init_l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 1);
switch (x_5) {
case 0:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Message_toString(x_1, x_6, x_4);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = 1;
x_11 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_10);
x_12 = lean_array_push(x_3, x_11);
x_13 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = lean_array_push(x_3, x_18);
x_20 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
case 1:
{
uint8_t x_27; lean_object* x_28; 
x_27 = 0;
x_28 = l_Lean_Message_toString(x_1, x_27, x_4);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = 2;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_array_push(x_3, x_32);
x_34 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_28, 0, x_35);
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = 2;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_push(x_3, x_39);
x_41 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_28);
if (x_44 == 0)
{
return x_28;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_28, 0);
x_46 = lean_ctor_get(x_28, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_28);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
default: 
{
uint8_t x_48; lean_object* x_49; 
x_48 = 0;
x_49 = l_Lean_Message_toString(x_1, x_48, x_4);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = 3;
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_52);
x_54 = lean_array_push(x_3, x_53);
x_55 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_49, 0, x_56);
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = 3;
x_60 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_59);
x_61 = lean_array_push(x_3, x_60);
x_62 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1;
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_49);
if (x_65 == 0)
{
return x_49;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_49, 0);
x_67 = lean_ctor_get(x_49, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_49);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_5);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*5 + 2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_box(0);
x_15 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1(x_11, x_14, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_15, 1);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_28 = x_16;
} else {
 lean_dec_ref(x_16);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_17, 0);
lean_inc(x_29);
lean_dec(x_17);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_28;
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_4 = x_13;
x_5 = x_34;
x_6 = lean_box(0);
x_7 = x_33;
x_8 = x_32;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_dec(x_13);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_15, 0);
lean_dec(x_37);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_15;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_16, 0);
x_40 = lean_ctor_get(x_16, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_16);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_15, 0, x_41);
return x_15;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_15, 1);
lean_inc(x_42);
lean_dec(x_15);
x_43 = lean_ctor_get(x_16, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_45 = x_16;
} else {
 lean_dec_ref(x_16);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_13);
x_48 = !lean_is_exclusive(x_15);
if (x_48 == 0)
{
return x_15;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_15, 0);
x_50 = lean_ctor_get(x_15, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_15);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_11);
x_52 = lean_ctor_get(x_4, 1);
lean_inc(x_52);
lean_dec(x_4);
x_53 = lean_box(0);
x_4 = x_52;
x_5 = x_53;
x_6 = lean_box(0);
goto _start;
}
}
}
}
static lean_object* _init_l_Lake_elabConfigFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package configuration has errors", 34, 34);
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
lean_object* x_7; lean_object* x_8; lean_object* x_78; lean_object* x_79; lean_object* x_314; 
x_314 = l_IO_FS_readFile(x_4, x_6);
if (lean_obj_tag(x_314) == 0)
{
uint8_t x_315; 
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_314, 1);
lean_ctor_set(x_314, 1, x_5);
x_78 = x_314;
x_79 = x_316;
goto block_313;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_314, 0);
x_318 = lean_ctor_get(x_314, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_314);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_5);
x_78 = x_319;
x_79 = x_318;
goto block_313;
}
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_314);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_321 = lean_ctor_get(x_314, 0);
x_322 = lean_ctor_get(x_314, 1);
x_323 = lean_io_error_to_string(x_321);
x_324 = 3;
x_325 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set_uint8(x_325, sizeof(void*)*1, x_324);
x_326 = lean_array_get_size(x_5);
x_327 = lean_array_push(x_5, x_325);
lean_ctor_set(x_314, 1, x_327);
lean_ctor_set(x_314, 0, x_326);
x_78 = x_314;
x_79 = x_322;
goto block_313;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_328 = lean_ctor_get(x_314, 0);
x_329 = lean_ctor_get(x_314, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_314);
x_330 = lean_io_error_to_string(x_328);
x_331 = 3;
x_332 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set_uint8(x_332, sizeof(void*)*1, x_331);
x_333 = lean_array_get_size(x_5);
x_334 = lean_array_push(x_5, x_332);
x_335 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_78 = x_335;
x_79 = x_329;
goto block_313;
}
}
block_77:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_box(0);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MessageLog_toList(x_14);
x_16 = lean_box(0);
lean_inc(x_15);
x_17 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1(x_11, x_15, x_15, x_15, x_16, lean_box(0), x_10, x_8);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = l_Lean_MessageLog_hasErrors(x_14);
lean_dec(x_14);
if (x_24 == 0)
{
lean_dec(x_4);
lean_ctor_set(x_18, 0, x_13);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_13);
x_25 = l_Lake_processHeader___closed__1;
x_26 = lean_string_append(x_25, x_4);
lean_dec(x_4);
x_27 = l_Lake_elabConfigFile___closed__1;
x_28 = lean_string_append(x_26, x_27);
x_29 = 3;
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_29);
x_31 = lean_array_get_size(x_22);
x_32 = lean_array_push(x_22, x_30);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 1, x_32);
lean_ctor_set(x_18, 0, x_31);
return x_17;
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_dec(x_18);
x_34 = l_Lean_MessageLog_hasErrors(x_14);
lean_dec(x_14);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_4);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_13);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_17, 0, x_35);
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_13);
x_36 = l_Lake_processHeader___closed__1;
x_37 = lean_string_append(x_36, x_4);
lean_dec(x_4);
x_38 = l_Lake_elabConfigFile___closed__1;
x_39 = lean_string_append(x_37, x_38);
x_40 = 3;
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_40);
x_42 = lean_array_get_size(x_33);
x_43 = lean_array_push(x_33, x_41);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_ctor_set(x_17, 0, x_44);
return x_17;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_17, 1);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_47 = x_18;
} else {
 lean_dec_ref(x_18);
 x_47 = lean_box(0);
}
x_48 = l_Lean_MessageLog_hasErrors(x_14);
lean_dec(x_14);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_46);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_13);
x_51 = l_Lake_processHeader___closed__1;
x_52 = lean_string_append(x_51, x_4);
lean_dec(x_4);
x_53 = l_Lake_elabConfigFile___closed__1;
x_54 = lean_string_append(x_52, x_53);
x_55 = 3;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_array_get_size(x_46);
x_58 = lean_array_push(x_46, x_56);
if (lean_is_scalar(x_47)) {
 x_59 = lean_alloc_ctor(1, 2, 0);
} else {
 x_59 = x_47;
 lean_ctor_set_tag(x_59, 1);
}
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_45);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_17);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_17, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_18);
if (x_63 == 0)
{
return x_17;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_18, 0);
x_65 = lean_ctor_get(x_18, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_18);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_17, 0, x_66);
return x_17;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_17, 1);
lean_inc(x_67);
lean_dec(x_17);
x_68 = lean_ctor_get(x_18, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_18, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_70 = x_18;
} else {
 lean_dec_ref(x_18);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_17);
if (x_73 == 0)
{
return x_17;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_17, 0);
x_75 = lean_ctor_get(x_17, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_17);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
block_313:
{
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_220; 
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 1);
x_83 = 1;
lean_inc(x_4);
x_84 = l_Lean_Parser_mkInputContext(x_81, x_4, x_83);
lean_inc(x_84);
x_220 = l_Lean_Parser_parseHeader(x_84, x_79);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
lean_ctor_set(x_78, 0, x_221);
x_85 = x_78;
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
x_228 = lean_array_get_size(x_82);
x_229 = lean_array_push(x_82, x_227);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_229);
lean_ctor_set(x_78, 0, x_228);
x_85 = x_78;
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
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_153; 
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
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_95 = x_88;
} else {
 lean_dec_ref(x_88);
 x_95 = lean_box(0);
}
lean_inc(x_84);
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
x_96 = x_85;
x_97 = x_155;
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
x_96 = x_85;
x_97 = x_157;
goto block_152;
}
block_152:
{
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_98; 
lean_dec(x_95);
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_99 = lean_ctor_get(x_96, 0);
x_100 = lean_ctor_get(x_96, 1);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = l_Lake_configModuleName;
x_104 = l_Lean_Environment_setMainModule(x_101, x_103);
lean_inc(x_3);
x_105 = l_Lean_Environment_enableRealizationsForImports(x_104, x_3, x_97);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_1);
x_109 = l_Lake_elabConfigFile___closed__2;
x_110 = l_Lean_EnvExtension_setState___rarg(x_109, x_106, x_108);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_2);
x_112 = l_Lake_elabConfigFile___closed__3;
x_113 = l_Lean_EnvExtension_setState___rarg(x_112, x_110, x_111);
x_114 = l_Lean_Elab_Command_mkState(x_113, x_102, x_3);
x_115 = l_Lean_Elab_IO_processCommands(x_84, x_93, x_114, x_107);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_ctor_set(x_96, 0, x_116);
x_7 = x_96;
x_8 = x_117;
goto block_77;
}
else
{
uint8_t x_118; 
lean_dec(x_102);
lean_free_object(x_96);
lean_dec(x_100);
lean_dec(x_93);
lean_dec(x_84);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_105);
if (x_118 == 0)
{
return x_105;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_105, 0);
x_120 = lean_ctor_get(x_105, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_105);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_122 = lean_ctor_get(x_96, 0);
x_123 = lean_ctor_get(x_96, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_96);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = l_Lake_configModuleName;
x_127 = l_Lean_Environment_setMainModule(x_124, x_126);
lean_inc(x_3);
x_128 = l_Lean_Environment_enableRealizationsForImports(x_127, x_3, x_97);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_1);
x_132 = l_Lake_elabConfigFile___closed__2;
x_133 = l_Lean_EnvExtension_setState___rarg(x_132, x_129, x_131);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_2);
x_135 = l_Lake_elabConfigFile___closed__3;
x_136 = l_Lean_EnvExtension_setState___rarg(x_135, x_133, x_134);
x_137 = l_Lean_Elab_Command_mkState(x_136, x_125, x_3);
x_138 = l_Lean_Elab_IO_processCommands(x_84, x_93, x_137, x_130);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_123);
x_7 = x_141;
x_8 = x_140;
goto block_77;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_93);
lean_dec(x_84);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = lean_ctor_get(x_128, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_128, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_144 = x_128;
} else {
 lean_dec_ref(x_128);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
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
x_146 = !lean_is_exclusive(x_96);
if (x_146 == 0)
{
lean_object* x_147; 
if (lean_is_scalar(x_95)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_95;
}
lean_ctor_set(x_147, 0, x_96);
lean_ctor_set(x_147, 1, x_97);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_96, 0);
x_149 = lean_ctor_get(x_96, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_96);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
if (lean_is_scalar(x_95)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_95;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_97);
return x_151;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_201; 
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
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_167 = x_88;
} else {
 lean_dec_ref(x_88);
 x_167 = lean_box(0);
}
lean_inc(x_84);
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
x_168 = x_204;
x_169 = x_203;
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
x_168 = x_212;
x_169 = x_206;
goto block_200;
}
block_200:
{
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_172 = x_168;
} else {
 lean_dec_ref(x_168);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_170, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
lean_dec(x_170);
x_175 = l_Lake_configModuleName;
x_176 = l_Lean_Environment_setMainModule(x_173, x_175);
lean_inc(x_3);
x_177 = l_Lean_Environment_enableRealizationsForImports(x_176, x_3, x_169);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_1);
x_181 = l_Lake_elabConfigFile___closed__2;
x_182 = l_Lean_EnvExtension_setState___rarg(x_181, x_178, x_180);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_2);
x_184 = l_Lake_elabConfigFile___closed__3;
x_185 = l_Lean_EnvExtension_setState___rarg(x_184, x_182, x_183);
x_186 = l_Lean_Elab_Command_mkState(x_185, x_174, x_3);
x_187 = l_Lean_Elab_IO_processCommands(x_84, x_165, x_186, x_179);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
if (lean_is_scalar(x_172)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_172;
}
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_171);
x_7 = x_190;
x_8 = x_189;
goto block_77;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_174);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_165);
lean_dec(x_84);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = lean_ctor_get(x_177, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_177, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_193 = x_177;
} else {
 lean_dec_ref(x_177);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
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
x_195 = lean_ctor_get(x_168, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_168, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_197 = x_168;
} else {
 lean_dec_ref(x_168);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
if (lean_is_scalar(x_167)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_167;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_169);
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
lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_295; 
x_230 = lean_ctor_get(x_78, 0);
x_231 = lean_ctor_get(x_78, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_78);
x_232 = 1;
lean_inc(x_4);
x_233 = l_Lean_Parser_mkInputContext(x_230, x_4, x_232);
lean_inc(x_233);
x_295 = l_Lean_Parser_parseHeader(x_233, x_79);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_295, 1);
lean_inc(x_297);
lean_dec(x_295);
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_231);
x_234 = x_298;
x_235 = x_297;
goto block_294;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_299 = lean_ctor_get(x_295, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_295, 1);
lean_inc(x_300);
lean_dec(x_295);
x_301 = lean_io_error_to_string(x_299);
x_302 = 3;
x_303 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*1, x_302);
x_304 = lean_array_get_size(x_231);
x_305 = lean_array_push(x_231, x_303);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_234 = x_306;
x_235 = x_300;
goto block_294;
}
block_294:
{
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_277; 
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_234, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_239 = x_234;
} else {
 lean_dec_ref(x_234);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_236, 0);
lean_inc(x_240);
lean_dec(x_236);
x_241 = lean_ctor_get(x_237, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_237, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_243 = x_237;
} else {
 lean_dec_ref(x_237);
 x_243 = lean_box(0);
}
lean_inc(x_233);
lean_inc(x_3);
x_277 = l_Lake_processHeader(x_240, x_3, x_233, x_242, x_235);
lean_dec(x_240);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
if (lean_is_scalar(x_239)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_239;
}
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_238);
x_244 = x_280;
x_245 = x_279;
goto block_276;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_281 = lean_ctor_get(x_277, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_277, 1);
lean_inc(x_282);
lean_dec(x_277);
x_283 = lean_io_error_to_string(x_281);
x_284 = 3;
x_285 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set_uint8(x_285, sizeof(void*)*1, x_284);
x_286 = lean_array_get_size(x_238);
x_287 = lean_array_push(x_238, x_285);
if (lean_is_scalar(x_239)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_239;
 lean_ctor_set_tag(x_288, 1);
}
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_244 = x_288;
x_245 = x_282;
goto block_276;
}
block_276:
{
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_243);
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_248 = x_244;
} else {
 lean_dec_ref(x_244);
 x_248 = lean_box(0);
}
x_249 = lean_ctor_get(x_246, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_250);
lean_dec(x_246);
x_251 = l_Lake_configModuleName;
x_252 = l_Lean_Environment_setMainModule(x_249, x_251);
lean_inc(x_3);
x_253 = l_Lean_Environment_enableRealizationsForImports(x_252, x_3, x_245);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_256, 0, x_1);
x_257 = l_Lake_elabConfigFile___closed__2;
x_258 = l_Lean_EnvExtension_setState___rarg(x_257, x_254, x_256);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_2);
x_260 = l_Lake_elabConfigFile___closed__3;
x_261 = l_Lean_EnvExtension_setState___rarg(x_260, x_258, x_259);
x_262 = l_Lean_Elab_Command_mkState(x_261, x_250, x_3);
x_263 = l_Lean_Elab_IO_processCommands(x_233, x_241, x_262, x_255);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
if (lean_is_scalar(x_248)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_248;
}
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_247);
x_7 = x_266;
x_8 = x_265;
goto block_77;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_250);
lean_dec(x_248);
lean_dec(x_247);
lean_dec(x_241);
lean_dec(x_233);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_267 = lean_ctor_get(x_253, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_253, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_269 = x_253;
} else {
 lean_dec_ref(x_253);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_241);
lean_dec(x_233);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_271 = lean_ctor_get(x_244, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_244, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_273 = x_244;
} else {
 lean_dec_ref(x_244);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
if (lean_is_scalar(x_243)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_243;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_245);
return x_275;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_233);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_289 = lean_ctor_get(x_234, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_234, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_234)) {
 lean_ctor_release(x_234, 0);
 lean_ctor_release(x_234, 1);
 x_291 = x_234;
} else {
 lean_dec_ref(x_234);
 x_291 = lean_box(0);
}
if (lean_is_scalar(x_291)) {
 x_292 = lean_alloc_ctor(1, 2, 0);
} else {
 x_292 = x_291;
}
lean_ctor_set(x_292, 0, x_289);
lean_ctor_set(x_292, 1, x_290);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_235);
return x_293;
}
}
}
}
else
{
uint8_t x_307; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_307 = !lean_is_exclusive(x_78);
if (x_307 == 0)
{
lean_object* x_308; 
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_78);
lean_ctor_set(x_308, 1, x_79);
return x_308;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_309 = lean_ctor_get(x_78, 0);
x_310 = lean_ctor_get(x_78, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_78);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_79);
return x_312;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lake_environment_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packageAttr", 11, 11);
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
x_1 = lean_mk_string_unchecked("packageDepAttr", 14, 14);
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
x_1 = lean_mk_string_unchecked("postUpdateAttr", 14, 14);
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
x_1 = lean_mk_string_unchecked("scriptAttr", 10, 10);
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
x_1 = lean_mk_string_unchecked("defaultScriptAttr", 17, 17);
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
x_1 = lean_mk_string_unchecked("leanLibAttr", 11, 11);
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
x_1 = lean_mk_string_unchecked("leanExeAttr", 11, 11);
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
x_1 = lean_mk_string_unchecked("externLibAttr", 13, 13);
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
x_1 = lean_mk_string_unchecked("targetAttr", 10, 10);
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
x_1 = lean_mk_string_unchecked("defaultTargetAttr", 17, 17);
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
x_1 = lean_mk_string_unchecked("testDriverAttr", 14, 14);
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
x_1 = lean_mk_string_unchecked("lintDriverAttr", 14, 14);
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
x_1 = lean_mk_string_unchecked("moduleFacetAttr", 15, 15);
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
x_1 = lean_mk_string_unchecked("packageFacetAttr", 16, 16);
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
x_1 = lean_mk_string_unchecked("libraryFacetAttr", 16, 16);
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
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("docStringExt", 12, 12);
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
x_1 = lean_mk_string_unchecked("IR", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFileCore_lakeExts___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declMapExt", 10, 10);
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
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedEnvExtensionState;
x_2 = l_Lean_instInhabitedPersistentEnvExtension(lean_box(0), lean_box(0), lean_box(0), x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
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
lean_object* x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_array_get_size(x_16);
x_18 = l_Lean_Name_hash___override(x_11);
x_19 = 32;
x_20 = lean_uint64_shift_right(x_18, x_19);
x_21 = lean_uint64_xor(x_18, x_20);
x_22 = 16;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_27 = lean_usize_sub(x_26, x_9);
x_28 = lean_usize_land(x_25, x_27);
x_29 = lean_array_uget(x_16, x_28);
x_30 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(x_11, x_29);
lean_dec(x_29);
lean_dec(x_11);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___closed__1;
x_34 = lean_array_get(x_33, x_1, x_32);
lean_dec(x_32);
x_35 = lean_array_get_size(x_12);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_lt(x_36, x_35);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_35, x_35);
if (x_39 == 0)
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
else
{
size_t x_41; size_t x_42; lean_object* x_43; 
x_41 = 0;
x_42 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_43 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1(x_34, x_12, x_41, x_42, x_6);
lean_dec(x_12);
x_4 = x_10;
x_6 = x_43;
goto _start;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lake_environment_add(x_4, x_6);
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
x_48 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(x_13, x_46, x_47, x_11);
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
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(x_20, x_24, x_25, x_29, x_30, x_19);
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
x_42 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(x_20, x_32, x_34, x_40, x_41, x_19);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(x_1, x_5, x_6, x_4);
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
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("platform", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanHash", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configHash", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("options", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(lean_object* x_1) {
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
x_7 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__2;
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
x_18 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__3;
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
x_24 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__4;
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
x_31 = l_Lake_importModulesUsingCache___lambda__1___closed__1;
x_32 = l_List_flatMapTR_go___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55____spec__2(x_30, x_31);
x_33 = l_Lean_Json_mkObj(x_32);
return x_33;
}
}
static lean_object* _init_l_Lake_instToJsonConfigTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_), 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value '{j}' is too large for `UInt64`", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__1;
x_10 = lean_nat_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(0);
x_12 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___lambda__1(x_8, x_11);
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
x_16 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__3;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__2(lean_object* x_1, lean_object* x_2) {
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
x_10 = l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(x_9, x_8);
return x_10;
}
}
}
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__2;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__4;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__7;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__6;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__9;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__12;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__6;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__14;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__17() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__16;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__6;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__17;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__18;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__21() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__20;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__6;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__21;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__22;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__1;
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
x_6 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__11;
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
x_9 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__11;
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
x_13 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__2;
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
x_17 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__15;
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
x_20 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__15;
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
x_24 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__3;
lean_inc(x_1);
x_25 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1(x_1, x_24);
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
x_28 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__19;
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
x_31 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__19;
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
x_35 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__4;
x_36 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__2(x_1, x_35);
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
x_39 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__23;
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
x_42 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__23;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instFromJsonConfigTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166_), 1, 0);
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
x_1 = lean_mk_string_unchecked("invalid configuration file name", 31, 31);
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
x_1 = lean_mk_string_unchecked("olean", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("olean.trace", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("olean.lock", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Json_Parser_any), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("compiled configuration is invalid; run with '-R' to reconfigure", 63, 63);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_importConfigFile___closed__7;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not acquire an exclusive configuration lock; ", 51, 51);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("another process may already be reconfiguring the package", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFile___closed__9;
x_2 = l_Lake_importConfigFile___closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_importConfigFile___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_importConfigFile___closed__11;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
x_6 = l_System_FilePath_join(x_4, x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_inc(x_6);
x_8 = l_System_FilePath_join(x_6, x_7);
lean_dec(x_7);
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
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_2116; 
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
lean_dec(x_20);
x_22 = l_Lake_importConfigFile___closed__4;
lean_inc(x_15);
x_23 = l_System_FilePath_withExtension(x_15, x_22);
lean_inc(x_18);
x_24 = l_System_FilePath_join(x_18, x_23);
lean_dec(x_23);
x_25 = l_Lake_importConfigFile___closed__5;
x_26 = l_System_FilePath_withExtension(x_15, x_25);
lean_inc(x_18);
x_27 = l_System_FilePath_join(x_18, x_26);
lean_dec(x_26);
x_2116 = l_Lake_computeTextFileHash(x_8, x_3);
if (lean_obj_tag(x_2116) == 0)
{
uint8_t x_2117; 
x_2117 = !lean_is_exclusive(x_2116);
if (x_2117 == 0)
{
lean_object* x_2118; 
x_2118 = lean_ctor_get(x_2116, 1);
lean_ctor_set(x_2116, 1, x_2);
x_28 = x_2116;
x_29 = x_2118;
goto block_2115;
}
else
{
lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; 
x_2119 = lean_ctor_get(x_2116, 0);
x_2120 = lean_ctor_get(x_2116, 1);
lean_inc(x_2120);
lean_inc(x_2119);
lean_dec(x_2116);
x_2121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2121, 0, x_2119);
lean_ctor_set(x_2121, 1, x_2);
x_28 = x_2121;
x_29 = x_2120;
goto block_2115;
}
}
else
{
uint8_t x_2122; 
x_2122 = !lean_is_exclusive(x_2116);
if (x_2122 == 0)
{
lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; uint8_t x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; 
x_2123 = lean_ctor_get(x_2116, 0);
x_2124 = lean_ctor_get(x_2116, 1);
x_2125 = lean_io_error_to_string(x_2123);
x_2126 = 3;
x_2127 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2127, 0, x_2125);
lean_ctor_set_uint8(x_2127, sizeof(void*)*1, x_2126);
x_2128 = lean_array_get_size(x_2);
x_2129 = lean_array_push(x_2, x_2127);
lean_ctor_set(x_2116, 1, x_2129);
lean_ctor_set(x_2116, 0, x_2128);
x_28 = x_2116;
x_29 = x_2124;
goto block_2115;
}
else
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; uint8_t x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; lean_object* x_2137; 
x_2130 = lean_ctor_get(x_2116, 0);
x_2131 = lean_ctor_get(x_2116, 1);
lean_inc(x_2131);
lean_inc(x_2130);
lean_dec(x_2116);
x_2132 = lean_io_error_to_string(x_2130);
x_2133 = 3;
x_2134 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2134, 0, x_2132);
lean_ctor_set_uint8(x_2134, sizeof(void*)*1, x_2133);
x_2135 = lean_array_get_size(x_2);
x_2136 = lean_array_push(x_2, x_2134);
x_2137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2137, 0, x_2135);
lean_ctor_set(x_2137, 1, x_2136);
x_28 = x_2137;
x_29 = x_2131;
goto block_2115;
}
}
block_2115:
{
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_527; lean_object* x_528; lean_object* x_1269; lean_object* x_1270; lean_object* x_2019; lean_object* x_2020; uint8_t x_2021; 
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
x_2019 = l_System_FilePath_pathExists(x_24, x_29);
x_2020 = lean_ctor_get(x_2019, 0);
lean_inc(x_2020);
x_2021 = lean_unbox(x_2020);
lean_dec(x_2020);
if (x_2021 == 0)
{
uint8_t x_2022; 
x_2022 = !lean_is_exclusive(x_2019);
if (x_2022 == 0)
{
lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; 
x_2023 = lean_ctor_get(x_2019, 1);
x_2024 = lean_ctor_get(x_2019, 0);
lean_dec(x_2024);
x_2025 = l_IO_FS_createDirAll(x_18, x_2023);
lean_dec(x_18);
if (lean_obj_tag(x_2025) == 0)
{
lean_object* x_2026; uint8_t x_2027; lean_object* x_2028; 
lean_free_object(x_2019);
x_2026 = lean_ctor_get(x_2025, 1);
lean_inc(x_2026);
lean_dec(x_2025);
x_2027 = 2;
x_2028 = lean_io_prim_handle_mk(x_24, x_2027, x_2026);
if (lean_obj_tag(x_2028) == 0)
{
uint8_t x_2029; 
x_2029 = !lean_is_exclusive(x_2028);
if (x_2029 == 0)
{
lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; 
x_2030 = lean_ctor_get(x_2028, 0);
x_2031 = lean_ctor_get(x_2028, 1);
x_2032 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2032, 0, x_2030);
lean_ctor_set(x_2028, 1, x_31);
lean_ctor_set(x_2028, 0, x_2032);
x_1269 = x_2028;
x_1270 = x_2031;
goto block_2018;
}
else
{
lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; 
x_2033 = lean_ctor_get(x_2028, 0);
x_2034 = lean_ctor_get(x_2028, 1);
lean_inc(x_2034);
lean_inc(x_2033);
lean_dec(x_2028);
x_2035 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2035, 0, x_2033);
x_2036 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2036, 0, x_2035);
lean_ctor_set(x_2036, 1, x_31);
x_1269 = x_2036;
x_1270 = x_2034;
goto block_2018;
}
}
else
{
uint8_t x_2037; 
x_2037 = !lean_is_exclusive(x_2028);
if (x_2037 == 0)
{
lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; 
x_2038 = lean_ctor_get(x_2028, 0);
x_2039 = lean_ctor_get(x_2028, 1);
x_2040 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2040, 0, x_2038);
lean_ctor_set_tag(x_2028, 0);
lean_ctor_set(x_2028, 1, x_31);
lean_ctor_set(x_2028, 0, x_2040);
x_1269 = x_2028;
x_1270 = x_2039;
goto block_2018;
}
else
{
lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; 
x_2041 = lean_ctor_get(x_2028, 0);
x_2042 = lean_ctor_get(x_2028, 1);
lean_inc(x_2042);
lean_inc(x_2041);
lean_dec(x_2028);
x_2043 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2043, 0, x_2041);
x_2044 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2044, 0, x_2043);
lean_ctor_set(x_2044, 1, x_31);
x_1269 = x_2044;
x_1270 = x_2042;
goto block_2018;
}
}
}
else
{
uint8_t x_2045; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_2045 = !lean_is_exclusive(x_2025);
if (x_2045 == 0)
{
lean_object* x_2046; lean_object* x_2047; uint8_t x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; 
x_2046 = lean_ctor_get(x_2025, 0);
x_2047 = lean_io_error_to_string(x_2046);
x_2048 = 3;
x_2049 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2049, 0, x_2047);
lean_ctor_set_uint8(x_2049, sizeof(void*)*1, x_2048);
x_2050 = lean_array_get_size(x_31);
x_2051 = lean_array_push(x_31, x_2049);
lean_ctor_set_tag(x_2019, 1);
lean_ctor_set(x_2019, 1, x_2051);
lean_ctor_set(x_2019, 0, x_2050);
lean_ctor_set_tag(x_2025, 0);
lean_ctor_set(x_2025, 0, x_2019);
return x_2025;
}
else
{
lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; uint8_t x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; 
x_2052 = lean_ctor_get(x_2025, 0);
x_2053 = lean_ctor_get(x_2025, 1);
lean_inc(x_2053);
lean_inc(x_2052);
lean_dec(x_2025);
x_2054 = lean_io_error_to_string(x_2052);
x_2055 = 3;
x_2056 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2056, 0, x_2054);
lean_ctor_set_uint8(x_2056, sizeof(void*)*1, x_2055);
x_2057 = lean_array_get_size(x_31);
x_2058 = lean_array_push(x_31, x_2056);
lean_ctor_set_tag(x_2019, 1);
lean_ctor_set(x_2019, 1, x_2058);
lean_ctor_set(x_2019, 0, x_2057);
x_2059 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2059, 0, x_2019);
lean_ctor_set(x_2059, 1, x_2053);
return x_2059;
}
}
}
else
{
lean_object* x_2060; lean_object* x_2061; 
x_2060 = lean_ctor_get(x_2019, 1);
lean_inc(x_2060);
lean_dec(x_2019);
x_2061 = l_IO_FS_createDirAll(x_18, x_2060);
lean_dec(x_18);
if (lean_obj_tag(x_2061) == 0)
{
lean_object* x_2062; uint8_t x_2063; lean_object* x_2064; 
x_2062 = lean_ctor_get(x_2061, 1);
lean_inc(x_2062);
lean_dec(x_2061);
x_2063 = 2;
x_2064 = lean_io_prim_handle_mk(x_24, x_2063, x_2062);
if (lean_obj_tag(x_2064) == 0)
{
lean_object* x_2065; lean_object* x_2066; lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; 
x_2065 = lean_ctor_get(x_2064, 0);
lean_inc(x_2065);
x_2066 = lean_ctor_get(x_2064, 1);
lean_inc(x_2066);
if (lean_is_exclusive(x_2064)) {
 lean_ctor_release(x_2064, 0);
 lean_ctor_release(x_2064, 1);
 x_2067 = x_2064;
} else {
 lean_dec_ref(x_2064);
 x_2067 = lean_box(0);
}
x_2068 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2068, 0, x_2065);
if (lean_is_scalar(x_2067)) {
 x_2069 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2069 = x_2067;
}
lean_ctor_set(x_2069, 0, x_2068);
lean_ctor_set(x_2069, 1, x_31);
x_1269 = x_2069;
x_1270 = x_2066;
goto block_2018;
}
else
{
lean_object* x_2070; lean_object* x_2071; lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; 
x_2070 = lean_ctor_get(x_2064, 0);
lean_inc(x_2070);
x_2071 = lean_ctor_get(x_2064, 1);
lean_inc(x_2071);
if (lean_is_exclusive(x_2064)) {
 lean_ctor_release(x_2064, 0);
 lean_ctor_release(x_2064, 1);
 x_2072 = x_2064;
} else {
 lean_dec_ref(x_2064);
 x_2072 = lean_box(0);
}
x_2073 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2073, 0, x_2070);
if (lean_is_scalar(x_2072)) {
 x_2074 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2074 = x_2072;
 lean_ctor_set_tag(x_2074, 0);
}
lean_ctor_set(x_2074, 0, x_2073);
lean_ctor_set(x_2074, 1, x_31);
x_1269 = x_2074;
x_1270 = x_2071;
goto block_2018;
}
}
else
{
lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; uint8_t x_2079; lean_object* x_2080; lean_object* x_2081; lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_2075 = lean_ctor_get(x_2061, 0);
lean_inc(x_2075);
x_2076 = lean_ctor_get(x_2061, 1);
lean_inc(x_2076);
if (lean_is_exclusive(x_2061)) {
 lean_ctor_release(x_2061, 0);
 lean_ctor_release(x_2061, 1);
 x_2077 = x_2061;
} else {
 lean_dec_ref(x_2061);
 x_2077 = lean_box(0);
}
x_2078 = lean_io_error_to_string(x_2075);
x_2079 = 3;
x_2080 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2080, 0, x_2078);
lean_ctor_set_uint8(x_2080, sizeof(void*)*1, x_2079);
x_2081 = lean_array_get_size(x_31);
x_2082 = lean_array_push(x_31, x_2080);
x_2083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2083, 0, x_2081);
lean_ctor_set(x_2083, 1, x_2082);
if (lean_is_scalar(x_2077)) {
 x_2084 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2084 = x_2077;
 lean_ctor_set_tag(x_2084, 0);
}
lean_ctor_set(x_2084, 0, x_2083);
lean_ctor_set(x_2084, 1, x_2076);
return x_2084;
}
}
}
else
{
lean_object* x_2085; uint8_t x_2086; lean_object* x_2087; 
lean_dec(x_18);
x_2085 = lean_ctor_get(x_2019, 1);
lean_inc(x_2085);
lean_dec(x_2019);
x_2086 = 0;
x_2087 = lean_io_prim_handle_mk(x_24, x_2086, x_2085);
if (lean_obj_tag(x_2087) == 0)
{
uint8_t x_2088; 
x_2088 = !lean_is_exclusive(x_2087);
if (x_2088 == 0)
{
lean_object* x_2089; 
x_2089 = lean_ctor_get(x_2087, 1);
lean_ctor_set(x_2087, 1, x_31);
x_527 = x_2087;
x_528 = x_2089;
goto block_1268;
}
else
{
lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; 
x_2090 = lean_ctor_get(x_2087, 0);
x_2091 = lean_ctor_get(x_2087, 1);
lean_inc(x_2091);
lean_inc(x_2090);
lean_dec(x_2087);
x_2092 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2092, 0, x_2090);
lean_ctor_set(x_2092, 1, x_31);
x_527 = x_2092;
x_528 = x_2091;
goto block_1268;
}
}
else
{
uint8_t x_2093; 
x_2093 = !lean_is_exclusive(x_2087);
if (x_2093 == 0)
{
lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; uint8_t x_2097; lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; 
x_2094 = lean_ctor_get(x_2087, 0);
x_2095 = lean_ctor_get(x_2087, 1);
x_2096 = lean_io_error_to_string(x_2094);
x_2097 = 3;
x_2098 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2098, 0, x_2096);
lean_ctor_set_uint8(x_2098, sizeof(void*)*1, x_2097);
x_2099 = lean_array_get_size(x_31);
x_2100 = lean_array_push(x_31, x_2098);
lean_ctor_set(x_2087, 1, x_2100);
lean_ctor_set(x_2087, 0, x_2099);
x_527 = x_2087;
x_528 = x_2095;
goto block_1268;
}
else
{
lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; uint8_t x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; 
x_2101 = lean_ctor_get(x_2087, 0);
x_2102 = lean_ctor_get(x_2087, 1);
lean_inc(x_2102);
lean_inc(x_2101);
lean_dec(x_2087);
x_2103 = lean_io_error_to_string(x_2101);
x_2104 = 3;
x_2105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2105, 0, x_2103);
lean_ctor_set_uint8(x_2105, sizeof(void*)*1, x_2104);
x_2106 = lean_array_get_size(x_31);
x_2107 = lean_array_push(x_31, x_2105);
x_2108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2108, 0, x_2106);
lean_ctor_set(x_2108, 1, x_2107);
x_527 = x_2108;
x_528 = x_2102;
goto block_1268;
}
}
}
block_526:
{
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_137; lean_object* x_138; lean_object* x_346; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_1, 6);
lean_inc(x_37);
x_346 = lean_io_remove_file(x_21, x_34);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_346, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 1);
lean_inc(x_348);
lean_dec(x_346);
if (lean_is_scalar(x_16)) {
 x_349 = lean_alloc_ctor(1, 1, 0);
} else {
 x_349 = x_16;
}
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_33, 0, x_349);
x_137 = x_33;
x_138 = x_348;
goto block_345;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_346, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_346, 1);
lean_inc(x_351);
lean_dec(x_346);
if (lean_is_scalar(x_16)) {
 x_352 = lean_alloc_ctor(0, 1, 0);
} else {
 x_352 = x_16;
 lean_ctor_set_tag(x_352, 0);
}
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_33, 0, x_352);
x_137 = x_33;
x_138 = x_351;
goto block_345;
}
block_136:
{
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_1, 7);
lean_inc(x_41);
lean_dec(x_1);
x_42 = l_Lake_elabConfigFile(x_6, x_37, x_41, x_8, x_40, x_39);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
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
lean_dec(x_36);
lean_dec(x_21);
x_126 = !lean_is_exclusive(x_42);
if (x_126 == 0)
{
return x_42;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_42, 0);
x_128 = lean_ctor_get(x_42, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_42);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_38);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_38);
lean_ctor_set(x_131, 1, x_39);
return x_131;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_38, 0);
x_133 = lean_ctor_get(x_38, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_38);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_39);
return x_135;
}
}
}
block_345:
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
if (lean_obj_tag(x_140) == 11)
{
uint8_t x_141; 
lean_dec(x_140);
lean_dec(x_24);
x_141 = !lean_is_exclusive(x_137);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_142 = lean_ctor_get(x_137, 1);
x_143 = lean_ctor_get(x_137, 0);
lean_dec(x_143);
x_144 = lean_ctor_get(x_1, 0);
lean_inc(x_144);
x_145 = l_Lake_Env_leanGithash(x_144);
lean_dec(x_144);
x_146 = l_System_Platform_target;
lean_inc(x_37);
x_147 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_30);
lean_ctor_set(x_147, 3, x_37);
x_148 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_147);
x_149 = lean_unsigned_to_nat(80u);
x_150 = l_Lean_Json_pretty(x_148, x_149);
x_151 = l_IO_FS_Handle_putStrLn(x_36, x_150, x_138);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_io_prim_handle_truncate(x_36, x_152);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_ctor_set(x_137, 0, x_154);
x_38 = x_137;
x_39 = x_155;
goto block_136;
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
x_161 = lean_array_get_size(x_142);
x_162 = lean_array_push(x_142, x_160);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_162);
lean_ctor_set(x_137, 0, x_161);
x_38 = x_137;
x_39 = x_157;
goto block_136;
}
}
else
{
uint8_t x_163; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_151);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_164 = lean_ctor_get(x_151, 0);
x_165 = lean_io_error_to_string(x_164);
x_166 = 3;
x_167 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set_uint8(x_167, sizeof(void*)*1, x_166);
x_168 = lean_array_get_size(x_142);
x_169 = lean_array_push(x_142, x_167);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_169);
lean_ctor_set(x_137, 0, x_168);
lean_ctor_set_tag(x_151, 0);
lean_ctor_set(x_151, 0, x_137);
return x_151;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_170 = lean_ctor_get(x_151, 0);
x_171 = lean_ctor_get(x_151, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_151);
x_172 = lean_io_error_to_string(x_170);
x_173 = 3;
x_174 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set_uint8(x_174, sizeof(void*)*1, x_173);
x_175 = lean_array_get_size(x_142);
x_176 = lean_array_push(x_142, x_174);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_176);
lean_ctor_set(x_137, 0, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_137);
lean_ctor_set(x_177, 1, x_171);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_178 = lean_ctor_get(x_137, 1);
lean_inc(x_178);
lean_dec(x_137);
x_179 = lean_ctor_get(x_1, 0);
lean_inc(x_179);
x_180 = l_Lake_Env_leanGithash(x_179);
lean_dec(x_179);
x_181 = l_System_Platform_target;
lean_inc(x_37);
x_182 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
lean_ctor_set(x_182, 2, x_30);
lean_ctor_set(x_182, 3, x_37);
x_183 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_182);
x_184 = lean_unsigned_to_nat(80u);
x_185 = l_Lean_Json_pretty(x_183, x_184);
x_186 = l_IO_FS_Handle_putStrLn(x_36, x_185, x_138);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = lean_io_prim_handle_truncate(x_36, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_178);
x_38 = x_191;
x_39 = x_190;
goto block_136;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
lean_dec(x_188);
x_194 = lean_io_error_to_string(x_192);
x_195 = 3;
x_196 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set_uint8(x_196, sizeof(void*)*1, x_195);
x_197 = lean_array_get_size(x_178);
x_198 = lean_array_push(x_178, x_196);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_38 = x_199;
x_39 = x_193;
goto block_136;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_200 = lean_ctor_get(x_186, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_186, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_202 = x_186;
} else {
 lean_dec_ref(x_186);
 x_202 = lean_box(0);
}
x_203 = lean_io_error_to_string(x_200);
x_204 = 3;
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_204);
x_206 = lean_array_get_size(x_178);
x_207 = lean_array_push(x_178, x_205);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
if (lean_is_scalar(x_202)) {
 x_209 = lean_alloc_ctor(0, 2, 0);
} else {
 x_209 = x_202;
 lean_ctor_set_tag(x_209, 0);
}
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set(x_209, 1, x_201);
return x_209;
}
}
}
else
{
uint8_t x_210; 
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_137);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_211 = lean_ctor_get(x_137, 1);
x_212 = lean_ctor_get(x_137, 0);
lean_dec(x_212);
x_213 = lean_io_error_to_string(x_140);
x_214 = 3;
x_215 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set_uint8(x_215, sizeof(void*)*1, x_214);
x_216 = lean_array_get_size(x_211);
x_217 = lean_array_push(x_211, x_215);
x_218 = lean_io_prim_handle_unlock(x_36, x_138);
lean_dec(x_36);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = lean_io_remove_file(x_24, x_219);
lean_dec(x_24);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_220, 0);
lean_dec(x_222);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_217);
lean_ctor_set(x_137, 0, x_216);
lean_ctor_set(x_220, 0, x_137);
return x_220;
}
else
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_217);
lean_ctor_set(x_137, 0, x_216);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_137);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
else
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_220);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_220, 0);
x_227 = lean_io_error_to_string(x_226);
x_228 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set_uint8(x_228, sizeof(void*)*1, x_214);
x_229 = lean_array_push(x_217, x_228);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_229);
lean_ctor_set(x_137, 0, x_216);
lean_ctor_set_tag(x_220, 0);
lean_ctor_set(x_220, 0, x_137);
return x_220;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_230 = lean_ctor_get(x_220, 0);
x_231 = lean_ctor_get(x_220, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_220);
x_232 = lean_io_error_to_string(x_230);
x_233 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set_uint8(x_233, sizeof(void*)*1, x_214);
x_234 = lean_array_push(x_217, x_233);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_234);
lean_ctor_set(x_137, 0, x_216);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_137);
lean_ctor_set(x_235, 1, x_231);
return x_235;
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_24);
x_236 = !lean_is_exclusive(x_218);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_218, 0);
x_238 = lean_io_error_to_string(x_237);
x_239 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set_uint8(x_239, sizeof(void*)*1, x_214);
x_240 = lean_array_push(x_217, x_239);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_240);
lean_ctor_set(x_137, 0, x_216);
lean_ctor_set_tag(x_218, 0);
lean_ctor_set(x_218, 0, x_137);
return x_218;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_218, 0);
x_242 = lean_ctor_get(x_218, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_218);
x_243 = lean_io_error_to_string(x_241);
x_244 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set_uint8(x_244, sizeof(void*)*1, x_214);
x_245 = lean_array_push(x_217, x_244);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_245);
lean_ctor_set(x_137, 0, x_216);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_137);
lean_ctor_set(x_246, 1, x_242);
return x_246;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_247 = lean_ctor_get(x_137, 1);
lean_inc(x_247);
lean_dec(x_137);
x_248 = lean_io_error_to_string(x_140);
x_249 = 3;
x_250 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set_uint8(x_250, sizeof(void*)*1, x_249);
x_251 = lean_array_get_size(x_247);
x_252 = lean_array_push(x_247, x_250);
x_253 = lean_io_prim_handle_unlock(x_36, x_138);
lean_dec(x_36);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_253, 1);
lean_inc(x_254);
lean_dec(x_253);
x_255 = lean_io_remove_file(x_24, x_254);
lean_dec(x_24);
if (lean_obj_tag(x_255) == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_251);
lean_ctor_set(x_258, 1, x_252);
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_256);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_260 = lean_ctor_get(x_255, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_255, 1);
lean_inc(x_261);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_262 = x_255;
} else {
 lean_dec_ref(x_255);
 x_262 = lean_box(0);
}
x_263 = lean_io_error_to_string(x_260);
x_264 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set_uint8(x_264, sizeof(void*)*1, x_249);
x_265 = lean_array_push(x_252, x_264);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_251);
lean_ctor_set(x_266, 1, x_265);
if (lean_is_scalar(x_262)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_262;
 lean_ctor_set_tag(x_267, 0);
}
lean_ctor_set(x_267, 0, x_266);
lean_ctor_set(x_267, 1, x_261);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_24);
x_268 = lean_ctor_get(x_253, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_253, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_270 = x_253;
} else {
 lean_dec_ref(x_253);
 x_270 = lean_box(0);
}
x_271 = lean_io_error_to_string(x_268);
x_272 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set_uint8(x_272, sizeof(void*)*1, x_249);
x_273 = lean_array_push(x_252, x_272);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_251);
lean_ctor_set(x_274, 1, x_273);
if (lean_is_scalar(x_270)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_270;
 lean_ctor_set_tag(x_275, 0);
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_269);
return x_275;
}
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_139);
lean_dec(x_24);
x_276 = !lean_is_exclusive(x_137);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_277 = lean_ctor_get(x_137, 1);
x_278 = lean_ctor_get(x_137, 0);
lean_dec(x_278);
x_279 = lean_ctor_get(x_1, 0);
lean_inc(x_279);
x_280 = l_Lake_Env_leanGithash(x_279);
lean_dec(x_279);
x_281 = l_System_Platform_target;
lean_inc(x_37);
x_282 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
lean_ctor_set(x_282, 2, x_30);
lean_ctor_set(x_282, 3, x_37);
x_283 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_282);
x_284 = lean_unsigned_to_nat(80u);
x_285 = l_Lean_Json_pretty(x_283, x_284);
x_286 = l_IO_FS_Handle_putStrLn(x_36, x_285, x_138);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
x_288 = lean_io_prim_handle_truncate(x_36, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
lean_ctor_set(x_137, 0, x_289);
x_38 = x_137;
x_39 = x_290;
goto block_136;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_291 = lean_ctor_get(x_288, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_288, 1);
lean_inc(x_292);
lean_dec(x_288);
x_293 = lean_io_error_to_string(x_291);
x_294 = 3;
x_295 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_295, 0, x_293);
lean_ctor_set_uint8(x_295, sizeof(void*)*1, x_294);
x_296 = lean_array_get_size(x_277);
x_297 = lean_array_push(x_277, x_295);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_297);
lean_ctor_set(x_137, 0, x_296);
x_38 = x_137;
x_39 = x_292;
goto block_136;
}
}
else
{
uint8_t x_298; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_298 = !lean_is_exclusive(x_286);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_299 = lean_ctor_get(x_286, 0);
x_300 = lean_io_error_to_string(x_299);
x_301 = 3;
x_302 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*1, x_301);
x_303 = lean_array_get_size(x_277);
x_304 = lean_array_push(x_277, x_302);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_304);
lean_ctor_set(x_137, 0, x_303);
lean_ctor_set_tag(x_286, 0);
lean_ctor_set(x_286, 0, x_137);
return x_286;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_305 = lean_ctor_get(x_286, 0);
x_306 = lean_ctor_get(x_286, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_286);
x_307 = lean_io_error_to_string(x_305);
x_308 = 3;
x_309 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set_uint8(x_309, sizeof(void*)*1, x_308);
x_310 = lean_array_get_size(x_277);
x_311 = lean_array_push(x_277, x_309);
lean_ctor_set_tag(x_137, 1);
lean_ctor_set(x_137, 1, x_311);
lean_ctor_set(x_137, 0, x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_137);
lean_ctor_set(x_312, 1, x_306);
return x_312;
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_313 = lean_ctor_get(x_137, 1);
lean_inc(x_313);
lean_dec(x_137);
x_314 = lean_ctor_get(x_1, 0);
lean_inc(x_314);
x_315 = l_Lake_Env_leanGithash(x_314);
lean_dec(x_314);
x_316 = l_System_Platform_target;
lean_inc(x_37);
x_317 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_317, 0, x_316);
lean_ctor_set(x_317, 1, x_315);
lean_ctor_set(x_317, 2, x_30);
lean_ctor_set(x_317, 3, x_37);
x_318 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_317);
x_319 = lean_unsigned_to_nat(80u);
x_320 = l_Lean_Json_pretty(x_318, x_319);
x_321 = l_IO_FS_Handle_putStrLn(x_36, x_320, x_138);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
x_323 = lean_io_prim_handle_truncate(x_36, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_313);
x_38 = x_326;
x_39 = x_325;
goto block_136;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_327 = lean_ctor_get(x_323, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_323, 1);
lean_inc(x_328);
lean_dec(x_323);
x_329 = lean_io_error_to_string(x_327);
x_330 = 3;
x_331 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set_uint8(x_331, sizeof(void*)*1, x_330);
x_332 = lean_array_get_size(x_313);
x_333 = lean_array_push(x_313, x_331);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_38 = x_334;
x_39 = x_328;
goto block_136;
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_335 = lean_ctor_get(x_321, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_321, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_337 = x_321;
} else {
 lean_dec_ref(x_321);
 x_337 = lean_box(0);
}
x_338 = lean_io_error_to_string(x_335);
x_339 = 3;
x_340 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set_uint8(x_340, sizeof(void*)*1, x_339);
x_341 = lean_array_get_size(x_313);
x_342 = lean_array_push(x_313, x_340);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
if (lean_is_scalar(x_337)) {
 x_344 = lean_alloc_ctor(0, 2, 0);
} else {
 x_344 = x_337;
 lean_ctor_set_tag(x_344, 0);
}
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_336);
return x_344;
}
}
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_410; lean_object* x_411; lean_object* x_511; 
x_353 = lean_ctor_get(x_33, 0);
x_354 = lean_ctor_get(x_33, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_33);
x_355 = lean_ctor_get(x_1, 6);
lean_inc(x_355);
x_511 = lean_io_remove_file(x_21, x_34);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
if (lean_is_scalar(x_16)) {
 x_514 = lean_alloc_ctor(1, 1, 0);
} else {
 x_514 = x_16;
}
lean_ctor_set(x_514, 0, x_512);
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_354);
x_410 = x_515;
x_411 = x_513;
goto block_510;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_516 = lean_ctor_get(x_511, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_511, 1);
lean_inc(x_517);
lean_dec(x_511);
if (lean_is_scalar(x_16)) {
 x_518 = lean_alloc_ctor(0, 1, 0);
} else {
 x_518 = x_16;
 lean_ctor_set_tag(x_518, 0);
}
lean_ctor_set(x_518, 0, x_516);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_354);
x_410 = x_519;
x_411 = x_517;
goto block_510;
}
block_409:
{
if (lean_obj_tag(x_356) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_356, 1);
lean_inc(x_358);
lean_dec(x_356);
x_359 = lean_ctor_get(x_1, 7);
lean_inc(x_359);
lean_dec(x_1);
x_360 = l_Lake_elabConfigFile(x_6, x_355, x_359, x_8, x_358, x_357);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; 
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_362 = lean_ctor_get(x_360, 1);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_ctor_get(x_361, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_361, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_365 = x_361;
} else {
 lean_dec_ref(x_361);
 x_365 = lean_box(0);
}
lean_inc(x_363);
x_366 = lean_write_module(x_363, x_21, x_362);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
x_368 = lean_io_prim_handle_unlock(x_353, x_367);
lean_dec(x_353);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_370 = x_368;
} else {
 lean_dec_ref(x_368);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_365;
}
lean_ctor_set(x_371, 0, x_363);
lean_ctor_set(x_371, 1, x_364);
if (lean_is_scalar(x_370)) {
 x_372 = lean_alloc_ctor(0, 2, 0);
} else {
 x_372 = x_370;
}
lean_ctor_set(x_372, 0, x_371);
lean_ctor_set(x_372, 1, x_369);
return x_372;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_363);
x_373 = lean_ctor_get(x_368, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_368, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_375 = x_368;
} else {
 lean_dec_ref(x_368);
 x_375 = lean_box(0);
}
x_376 = lean_io_error_to_string(x_373);
x_377 = 3;
x_378 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set_uint8(x_378, sizeof(void*)*1, x_377);
x_379 = lean_array_get_size(x_364);
x_380 = lean_array_push(x_364, x_378);
if (lean_is_scalar(x_365)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_365;
 lean_ctor_set_tag(x_381, 1);
}
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
if (lean_is_scalar(x_375)) {
 x_382 = lean_alloc_ctor(0, 2, 0);
} else {
 x_382 = x_375;
 lean_ctor_set_tag(x_382, 0);
}
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_374);
return x_382;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_363);
lean_dec(x_353);
x_383 = lean_ctor_get(x_366, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_366, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_385 = x_366;
} else {
 lean_dec_ref(x_366);
 x_385 = lean_box(0);
}
x_386 = lean_io_error_to_string(x_383);
x_387 = 3;
x_388 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*1, x_387);
x_389 = lean_array_get_size(x_364);
x_390 = lean_array_push(x_364, x_388);
if (lean_is_scalar(x_365)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_365;
 lean_ctor_set_tag(x_391, 1);
}
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
if (lean_is_scalar(x_385)) {
 x_392 = lean_alloc_ctor(0, 2, 0);
} else {
 x_392 = x_385;
 lean_ctor_set_tag(x_392, 0);
}
lean_ctor_set(x_392, 0, x_391);
lean_ctor_set(x_392, 1, x_384);
return x_392;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_353);
lean_dec(x_21);
x_393 = lean_ctor_get(x_360, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_394 = x_360;
} else {
 lean_dec_ref(x_360);
 x_394 = lean_box(0);
}
x_395 = lean_ctor_get(x_361, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_361, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_397 = x_361;
} else {
 lean_dec_ref(x_361);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
if (lean_is_scalar(x_394)) {
 x_399 = lean_alloc_ctor(0, 2, 0);
} else {
 x_399 = x_394;
}
lean_ctor_set(x_399, 0, x_398);
lean_ctor_set(x_399, 1, x_393);
return x_399;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_353);
lean_dec(x_21);
x_400 = lean_ctor_get(x_360, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_360, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_402 = x_360;
} else {
 lean_dec_ref(x_360);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 2, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_400);
lean_ctor_set(x_403, 1, x_401);
return x_403;
}
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_355);
lean_dec(x_353);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_404 = lean_ctor_get(x_356, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_356, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_356)) {
 lean_ctor_release(x_356, 0);
 lean_ctor_release(x_356, 1);
 x_406 = x_356;
} else {
 lean_dec_ref(x_356);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 2, 0);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_405);
x_408 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_357);
return x_408;
}
}
block_510:
{
lean_object* x_412; 
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
lean_dec(x_412);
if (lean_obj_tag(x_413) == 11)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_413);
lean_dec(x_24);
x_414 = lean_ctor_get(x_410, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_415 = x_410;
} else {
 lean_dec_ref(x_410);
 x_415 = lean_box(0);
}
x_416 = lean_ctor_get(x_1, 0);
lean_inc(x_416);
x_417 = l_Lake_Env_leanGithash(x_416);
lean_dec(x_416);
x_418 = l_System_Platform_target;
lean_inc(x_355);
x_419 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_417);
lean_ctor_set(x_419, 2, x_30);
lean_ctor_set(x_419, 3, x_355);
x_420 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_419);
x_421 = lean_unsigned_to_nat(80u);
x_422 = l_Lean_Json_pretty(x_420, x_421);
x_423 = l_IO_FS_Handle_putStrLn(x_353, x_422, x_411);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_425 = lean_io_prim_handle_truncate(x_353, x_424);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_425, 1);
lean_inc(x_427);
lean_dec(x_425);
if (lean_is_scalar(x_415)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_415;
}
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_414);
x_356 = x_428;
x_357 = x_427;
goto block_409;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_429 = lean_ctor_get(x_425, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_425, 1);
lean_inc(x_430);
lean_dec(x_425);
x_431 = lean_io_error_to_string(x_429);
x_432 = 3;
x_433 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*1, x_432);
x_434 = lean_array_get_size(x_414);
x_435 = lean_array_push(x_414, x_433);
if (lean_is_scalar(x_415)) {
 x_436 = lean_alloc_ctor(1, 2, 0);
} else {
 x_436 = x_415;
 lean_ctor_set_tag(x_436, 1);
}
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
x_356 = x_436;
x_357 = x_430;
goto block_409;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_355);
lean_dec(x_353);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_437 = lean_ctor_get(x_423, 0);
lean_inc(x_437);
x_438 = lean_ctor_get(x_423, 1);
lean_inc(x_438);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_439 = x_423;
} else {
 lean_dec_ref(x_423);
 x_439 = lean_box(0);
}
x_440 = lean_io_error_to_string(x_437);
x_441 = 3;
x_442 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set_uint8(x_442, sizeof(void*)*1, x_441);
x_443 = lean_array_get_size(x_414);
x_444 = lean_array_push(x_414, x_442);
if (lean_is_scalar(x_415)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_415;
 lean_ctor_set_tag(x_445, 1);
}
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set(x_445, 1, x_444);
if (lean_is_scalar(x_439)) {
 x_446 = lean_alloc_ctor(0, 2, 0);
} else {
 x_446 = x_439;
 lean_ctor_set_tag(x_446, 0);
}
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_438);
return x_446;
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_355);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_447 = lean_ctor_get(x_410, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_448 = x_410;
} else {
 lean_dec_ref(x_410);
 x_448 = lean_box(0);
}
x_449 = lean_io_error_to_string(x_413);
x_450 = 3;
x_451 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set_uint8(x_451, sizeof(void*)*1, x_450);
x_452 = lean_array_get_size(x_447);
x_453 = lean_array_push(x_447, x_451);
x_454 = lean_io_prim_handle_unlock(x_353, x_411);
lean_dec(x_353);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_454, 1);
lean_inc(x_455);
lean_dec(x_454);
x_456 = lean_io_remove_file(x_24, x_455);
lean_dec(x_24);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_459 = lean_alloc_ctor(1, 2, 0);
} else {
 x_459 = x_448;
 lean_ctor_set_tag(x_459, 1);
}
lean_ctor_set(x_459, 0, x_452);
lean_ctor_set(x_459, 1, x_453);
if (lean_is_scalar(x_458)) {
 x_460 = lean_alloc_ctor(0, 2, 0);
} else {
 x_460 = x_458;
}
lean_ctor_set(x_460, 0, x_459);
lean_ctor_set(x_460, 1, x_457);
return x_460;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_461 = lean_ctor_get(x_456, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_456, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_463 = x_456;
} else {
 lean_dec_ref(x_456);
 x_463 = lean_box(0);
}
x_464 = lean_io_error_to_string(x_461);
x_465 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set_uint8(x_465, sizeof(void*)*1, x_450);
x_466 = lean_array_push(x_453, x_465);
if (lean_is_scalar(x_448)) {
 x_467 = lean_alloc_ctor(1, 2, 0);
} else {
 x_467 = x_448;
 lean_ctor_set_tag(x_467, 1);
}
lean_ctor_set(x_467, 0, x_452);
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
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_24);
x_469 = lean_ctor_get(x_454, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_454, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_454)) {
 lean_ctor_release(x_454, 0);
 lean_ctor_release(x_454, 1);
 x_471 = x_454;
} else {
 lean_dec_ref(x_454);
 x_471 = lean_box(0);
}
x_472 = lean_io_error_to_string(x_469);
x_473 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set_uint8(x_473, sizeof(void*)*1, x_450);
x_474 = lean_array_push(x_453, x_473);
if (lean_is_scalar(x_448)) {
 x_475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_475 = x_448;
 lean_ctor_set_tag(x_475, 1);
}
lean_ctor_set(x_475, 0, x_452);
lean_ctor_set(x_475, 1, x_474);
if (lean_is_scalar(x_471)) {
 x_476 = lean_alloc_ctor(0, 2, 0);
} else {
 x_476 = x_471;
 lean_ctor_set_tag(x_476, 0);
}
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_470);
return x_476;
}
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_412);
lean_dec(x_24);
x_477 = lean_ctor_get(x_410, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_478 = x_410;
} else {
 lean_dec_ref(x_410);
 x_478 = lean_box(0);
}
x_479 = lean_ctor_get(x_1, 0);
lean_inc(x_479);
x_480 = l_Lake_Env_leanGithash(x_479);
lean_dec(x_479);
x_481 = l_System_Platform_target;
lean_inc(x_355);
x_482 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_480);
lean_ctor_set(x_482, 2, x_30);
lean_ctor_set(x_482, 3, x_355);
x_483 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_482);
x_484 = lean_unsigned_to_nat(80u);
x_485 = l_Lean_Json_pretty(x_483, x_484);
x_486 = l_IO_FS_Handle_putStrLn(x_353, x_485, x_411);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
lean_dec(x_486);
x_488 = lean_io_prim_handle_truncate(x_353, x_487);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_488, 1);
lean_inc(x_490);
lean_dec(x_488);
if (lean_is_scalar(x_478)) {
 x_491 = lean_alloc_ctor(0, 2, 0);
} else {
 x_491 = x_478;
}
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_477);
x_356 = x_491;
x_357 = x_490;
goto block_409;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_492 = lean_ctor_get(x_488, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_488, 1);
lean_inc(x_493);
lean_dec(x_488);
x_494 = lean_io_error_to_string(x_492);
x_495 = 3;
x_496 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set_uint8(x_496, sizeof(void*)*1, x_495);
x_497 = lean_array_get_size(x_477);
x_498 = lean_array_push(x_477, x_496);
if (lean_is_scalar(x_478)) {
 x_499 = lean_alloc_ctor(1, 2, 0);
} else {
 x_499 = x_478;
 lean_ctor_set_tag(x_499, 1);
}
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
x_356 = x_499;
x_357 = x_493;
goto block_409;
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_355);
lean_dec(x_353);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_500 = lean_ctor_get(x_486, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_486, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_502 = x_486;
} else {
 lean_dec_ref(x_486);
 x_502 = lean_box(0);
}
x_503 = lean_io_error_to_string(x_500);
x_504 = 3;
x_505 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set_uint8(x_505, sizeof(void*)*1, x_504);
x_506 = lean_array_get_size(x_477);
x_507 = lean_array_push(x_477, x_505);
if (lean_is_scalar(x_478)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_478;
 lean_ctor_set_tag(x_508, 1);
}
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
if (lean_is_scalar(x_502)) {
 x_509 = lean_alloc_ctor(0, 2, 0);
} else {
 x_509 = x_502;
 lean_ctor_set_tag(x_509, 0);
}
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_501);
return x_509;
}
}
}
}
}
else
{
uint8_t x_520; 
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_520 = !lean_is_exclusive(x_33);
if (x_520 == 0)
{
lean_object* x_521; 
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_33);
lean_ctor_set(x_521, 1, x_34);
return x_521;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_33, 0);
x_523 = lean_ctor_get(x_33, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_33);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
x_525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_34);
return x_525;
}
}
}
block_1268:
{
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_1169; 
x_529 = lean_ctor_get(x_527, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_527, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_527)) {
 lean_ctor_release(x_527, 0);
 lean_ctor_release(x_527, 1);
 x_531 = x_527;
} else {
 lean_dec_ref(x_527);
 x_531 = lean_box(0);
}
x_1169 = lean_ctor_get_uint8(x_1, sizeof(void*)*10);
if (x_1169 == 0)
{
uint8_t x_1170; lean_object* x_1171; 
lean_dec(x_16);
x_1170 = 0;
x_1171 = lean_io_prim_handle_lock(x_529, x_1170, x_528);
if (lean_obj_tag(x_1171) == 0)
{
lean_object* x_1172; lean_object* x_1173; 
x_1172 = lean_ctor_get(x_1171, 1);
lean_inc(x_1172);
lean_dec(x_1171);
x_1173 = l_IO_FS_Handle_readToEnd(x_529, x_1172);
if (lean_obj_tag(x_1173) == 0)
{
uint8_t x_1174; 
x_1174 = !lean_is_exclusive(x_1173);
if (x_1174 == 0)
{
lean_object* x_1175; 
x_1175 = lean_ctor_get(x_1173, 1);
lean_ctor_set(x_1173, 1, x_530);
x_532 = x_1173;
x_533 = x_1175;
goto block_1168;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1176 = lean_ctor_get(x_1173, 0);
x_1177 = lean_ctor_get(x_1173, 1);
lean_inc(x_1177);
lean_inc(x_1176);
lean_dec(x_1173);
x_1178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1178, 0, x_1176);
lean_ctor_set(x_1178, 1, x_530);
x_532 = x_1178;
x_533 = x_1177;
goto block_1168;
}
}
else
{
uint8_t x_1179; 
x_1179 = !lean_is_exclusive(x_1173);
if (x_1179 == 0)
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; uint8_t x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1180 = lean_ctor_get(x_1173, 0);
x_1181 = lean_ctor_get(x_1173, 1);
x_1182 = lean_io_error_to_string(x_1180);
x_1183 = 3;
x_1184 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1184, 0, x_1182);
lean_ctor_set_uint8(x_1184, sizeof(void*)*1, x_1183);
x_1185 = lean_array_get_size(x_530);
x_1186 = lean_array_push(x_530, x_1184);
lean_ctor_set(x_1173, 1, x_1186);
lean_ctor_set(x_1173, 0, x_1185);
x_532 = x_1173;
x_533 = x_1181;
goto block_1168;
}
else
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; uint8_t x_1190; lean_object* x_1191; lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1187 = lean_ctor_get(x_1173, 0);
x_1188 = lean_ctor_get(x_1173, 1);
lean_inc(x_1188);
lean_inc(x_1187);
lean_dec(x_1173);
x_1189 = lean_io_error_to_string(x_1187);
x_1190 = 3;
x_1191 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1191, 0, x_1189);
lean_ctor_set_uint8(x_1191, sizeof(void*)*1, x_1190);
x_1192 = lean_array_get_size(x_530);
x_1193 = lean_array_push(x_530, x_1191);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set(x_1194, 1, x_1193);
x_532 = x_1194;
x_533 = x_1188;
goto block_1168;
}
}
}
else
{
uint8_t x_1195; 
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1195 = !lean_is_exclusive(x_1171);
if (x_1195 == 0)
{
lean_object* x_1196; lean_object* x_1197; uint8_t x_1198; lean_object* x_1199; lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1196 = lean_ctor_get(x_1171, 0);
x_1197 = lean_io_error_to_string(x_1196);
x_1198 = 3;
x_1199 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1199, 0, x_1197);
lean_ctor_set_uint8(x_1199, sizeof(void*)*1, x_1198);
x_1200 = lean_array_get_size(x_530);
x_1201 = lean_array_push(x_530, x_1199);
x_1202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1202, 0, x_1200);
lean_ctor_set(x_1202, 1, x_1201);
lean_ctor_set_tag(x_1171, 0);
lean_ctor_set(x_1171, 0, x_1202);
return x_1171;
}
else
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; uint8_t x_1206; lean_object* x_1207; lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1203 = lean_ctor_get(x_1171, 0);
x_1204 = lean_ctor_get(x_1171, 1);
lean_inc(x_1204);
lean_inc(x_1203);
lean_dec(x_1171);
x_1205 = lean_io_error_to_string(x_1203);
x_1206 = 3;
x_1207 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1207, 0, x_1205);
lean_ctor_set_uint8(x_1207, sizeof(void*)*1, x_1206);
x_1208 = lean_array_get_size(x_530);
x_1209 = lean_array_push(x_530, x_1207);
x_1210 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1210, 0, x_1208);
lean_ctor_set(x_1210, 1, x_1209);
x_1211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1211, 0, x_1210);
lean_ctor_set(x_1211, 1, x_1204);
return x_1211;
}
}
}
else
{
lean_object* x_1212; lean_object* x_1213; uint8_t x_1221; lean_object* x_1222; 
lean_dec(x_531);
lean_dec(x_32);
x_1221 = 1;
x_1222 = lean_io_prim_handle_mk(x_27, x_1221, x_528);
lean_dec(x_27);
if (lean_obj_tag(x_1222) == 0)
{
lean_object* x_1223; lean_object* x_1224; uint8_t x_1225; lean_object* x_1226; 
x_1223 = lean_ctor_get(x_1222, 0);
lean_inc(x_1223);
x_1224 = lean_ctor_get(x_1222, 1);
lean_inc(x_1224);
lean_dec(x_1222);
x_1225 = 1;
x_1226 = lean_io_prim_handle_try_lock(x_1223, x_1225, x_1224);
if (lean_obj_tag(x_1226) == 0)
{
lean_object* x_1227; uint8_t x_1228; 
x_1227 = lean_ctor_get(x_1226, 0);
lean_inc(x_1227);
x_1228 = lean_unbox(x_1227);
lean_dec(x_1227);
if (x_1228 == 0)
{
lean_object* x_1229; lean_object* x_1230; 
lean_dec(x_1223);
x_1229 = lean_ctor_get(x_1226, 1);
lean_inc(x_1229);
lean_dec(x_1226);
x_1230 = lean_io_prim_handle_unlock(x_529, x_1229);
lean_dec(x_529);
if (lean_obj_tag(x_1230) == 0)
{
lean_object* x_1231; lean_object* x_1232; 
x_1231 = lean_ctor_get(x_1230, 1);
lean_inc(x_1231);
lean_dec(x_1230);
x_1232 = l_Lake_importConfigFile___closed__12;
x_1212 = x_1232;
x_1213 = x_1231;
goto block_1220;
}
else
{
lean_object* x_1233; lean_object* x_1234; 
x_1233 = lean_ctor_get(x_1230, 0);
lean_inc(x_1233);
x_1234 = lean_ctor_get(x_1230, 1);
lean_inc(x_1234);
lean_dec(x_1230);
x_1212 = x_1233;
x_1213 = x_1234;
goto block_1220;
}
}
else
{
lean_object* x_1235; lean_object* x_1236; 
x_1235 = lean_ctor_get(x_1226, 1);
lean_inc(x_1235);
lean_dec(x_1226);
x_1236 = lean_io_prim_handle_unlock(x_529, x_1235);
lean_dec(x_529);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; uint8_t x_1238; lean_object* x_1239; 
x_1237 = lean_ctor_get(x_1236, 1);
lean_inc(x_1237);
lean_dec(x_1236);
x_1238 = 3;
x_1239 = lean_io_prim_handle_mk(x_24, x_1238, x_1237);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
x_1240 = lean_ctor_get(x_1239, 0);
lean_inc(x_1240);
x_1241 = lean_ctor_get(x_1239, 1);
lean_inc(x_1241);
lean_dec(x_1239);
x_1242 = lean_io_prim_handle_lock(x_1240, x_1225, x_1241);
if (lean_obj_tag(x_1242) == 0)
{
lean_object* x_1243; lean_object* x_1244; 
x_1243 = lean_ctor_get(x_1242, 1);
lean_inc(x_1243);
lean_dec(x_1242);
x_1244 = lean_io_prim_handle_unlock(x_1223, x_1243);
lean_dec(x_1223);
if (lean_obj_tag(x_1244) == 0)
{
uint8_t x_1245; 
x_1245 = !lean_is_exclusive(x_1244);
if (x_1245 == 0)
{
lean_object* x_1246; lean_object* x_1247; 
x_1246 = lean_ctor_get(x_1244, 1);
x_1247 = lean_ctor_get(x_1244, 0);
lean_dec(x_1247);
lean_ctor_set(x_1244, 1, x_530);
lean_ctor_set(x_1244, 0, x_1240);
x_33 = x_1244;
x_34 = x_1246;
goto block_526;
}
else
{
lean_object* x_1248; lean_object* x_1249; 
x_1248 = lean_ctor_get(x_1244, 1);
lean_inc(x_1248);
lean_dec(x_1244);
x_1249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1249, 0, x_1240);
lean_ctor_set(x_1249, 1, x_530);
x_33 = x_1249;
x_34 = x_1248;
goto block_526;
}
}
else
{
lean_object* x_1250; lean_object* x_1251; 
lean_dec(x_1240);
x_1250 = lean_ctor_get(x_1244, 0);
lean_inc(x_1250);
x_1251 = lean_ctor_get(x_1244, 1);
lean_inc(x_1251);
lean_dec(x_1244);
x_1212 = x_1250;
x_1213 = x_1251;
goto block_1220;
}
}
else
{
lean_object* x_1252; lean_object* x_1253; 
lean_dec(x_1240);
lean_dec(x_1223);
x_1252 = lean_ctor_get(x_1242, 0);
lean_inc(x_1252);
x_1253 = lean_ctor_get(x_1242, 1);
lean_inc(x_1253);
lean_dec(x_1242);
x_1212 = x_1252;
x_1213 = x_1253;
goto block_1220;
}
}
else
{
lean_object* x_1254; lean_object* x_1255; 
lean_dec(x_1223);
x_1254 = lean_ctor_get(x_1239, 0);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_1239, 1);
lean_inc(x_1255);
lean_dec(x_1239);
x_1212 = x_1254;
x_1213 = x_1255;
goto block_1220;
}
}
else
{
lean_object* x_1256; lean_object* x_1257; 
lean_dec(x_1223);
x_1256 = lean_ctor_get(x_1236, 0);
lean_inc(x_1256);
x_1257 = lean_ctor_get(x_1236, 1);
lean_inc(x_1257);
lean_dec(x_1236);
x_1212 = x_1256;
x_1213 = x_1257;
goto block_1220;
}
}
}
else
{
lean_object* x_1258; lean_object* x_1259; 
lean_dec(x_1223);
lean_dec(x_529);
x_1258 = lean_ctor_get(x_1226, 0);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_1226, 1);
lean_inc(x_1259);
lean_dec(x_1226);
x_1212 = x_1258;
x_1213 = x_1259;
goto block_1220;
}
}
else
{
lean_object* x_1260; lean_object* x_1261; 
lean_dec(x_529);
x_1260 = lean_ctor_get(x_1222, 0);
lean_inc(x_1260);
x_1261 = lean_ctor_get(x_1222, 1);
lean_inc(x_1261);
lean_dec(x_1222);
x_1212 = x_1260;
x_1213 = x_1261;
goto block_1220;
}
block_1220:
{
lean_object* x_1214; uint8_t x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; 
x_1214 = lean_io_error_to_string(x_1212);
x_1215 = 3;
x_1216 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1216, 0, x_1214);
lean_ctor_set_uint8(x_1216, sizeof(void*)*1, x_1215);
x_1217 = lean_array_get_size(x_530);
x_1218 = lean_array_push(x_530, x_1216);
x_1219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1219, 0, x_1217);
lean_ctor_set(x_1219, 1, x_1218);
x_33 = x_1219;
x_34 = x_1213;
goto block_526;
}
}
block_1168:
{
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_534 = lean_ctor_get(x_532, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_532, 1);
lean_inc(x_535);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_536 = x_532;
} else {
 lean_dec_ref(x_532);
 x_536 = lean_box(0);
}
x_537 = l_Lake_importConfigFile___closed__6;
x_538 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_537, x_534);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_538);
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_539 = lean_array_get_size(x_535);
x_540 = l_Lake_importConfigFile___closed__8;
x_541 = lean_array_push(x_535, x_540);
if (lean_is_scalar(x_536)) {
 x_542 = lean_alloc_ctor(1, 2, 0);
} else {
 x_542 = x_536;
 lean_ctor_set_tag(x_542, 1);
}
lean_ctor_set(x_542, 0, x_539);
lean_ctor_set(x_542, 1, x_541);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_533);
return x_543;
}
else
{
lean_object* x_544; lean_object* x_545; 
x_544 = lean_ctor_get(x_538, 0);
lean_inc(x_544);
lean_dec(x_538);
x_545 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166_(x_544);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_545);
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_546 = lean_array_get_size(x_535);
x_547 = l_Lake_importConfigFile___closed__8;
x_548 = lean_array_push(x_535, x_547);
if (lean_is_scalar(x_536)) {
 x_549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_549 = x_536;
 lean_ctor_set_tag(x_549, 1);
}
lean_ctor_set(x_549, 0, x_546);
lean_ctor_set(x_549, 1, x_548);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_533);
return x_550;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; uint8_t x_1101; 
x_551 = lean_ctor_get(x_545, 0);
lean_inc(x_551);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 x_552 = x_545;
} else {
 lean_dec_ref(x_545);
 x_552 = lean_box(0);
}
x_1049 = l_System_FilePath_pathExists(x_21, x_533);
x_1050 = lean_ctor_get(x_1049, 0);
lean_inc(x_1050);
x_1051 = lean_ctor_get(x_1049, 1);
lean_inc(x_1051);
lean_dec(x_1049);
x_1101 = lean_unbox(x_1050);
lean_dec(x_1050);
if (x_1101 == 0)
{
lean_object* x_1102; 
lean_dec(x_32);
x_1102 = lean_box(0);
x_1052 = x_1102;
goto block_1100;
}
else
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; uint8_t x_1107; 
x_1103 = lean_ctor_get(x_551, 0);
lean_inc(x_1103);
x_1104 = lean_ctor_get(x_551, 1);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_551, 2);
lean_inc(x_1105);
x_1106 = l_System_Platform_target;
x_1107 = lean_string_dec_eq(x_1103, x_1106);
lean_dec(x_1103);
if (x_1107 == 0)
{
lean_object* x_1108; 
lean_dec(x_1105);
lean_dec(x_1104);
lean_dec(x_32);
x_1108 = lean_box(0);
x_1052 = x_1108;
goto block_1100;
}
else
{
lean_object* x_1109; lean_object* x_1110; uint8_t x_1111; 
x_1109 = lean_ctor_get(x_1, 0);
lean_inc(x_1109);
x_1110 = l_Lake_Env_leanGithash(x_1109);
lean_dec(x_1109);
x_1111 = lean_string_dec_eq(x_1104, x_1110);
lean_dec(x_1110);
lean_dec(x_1104);
if (x_1111 == 0)
{
lean_object* x_1112; 
lean_dec(x_1105);
lean_dec(x_32);
x_1112 = lean_box(0);
x_1052 = x_1112;
goto block_1100;
}
else
{
uint64_t x_1113; uint64_t x_1114; uint8_t x_1115; 
x_1113 = lean_unbox_uint64(x_1105);
lean_dec(x_1105);
x_1114 = lean_unbox_uint64(x_30);
x_1115 = lean_uint64_dec_eq(x_1113, x_1114);
if (x_1115 == 0)
{
lean_object* x_1116; 
lean_dec(x_32);
x_1116 = lean_box(0);
x_1052 = x_1116;
goto block_1100;
}
else
{
lean_object* x_1117; lean_object* x_1118; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_536);
lean_dec(x_531);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_6);
x_1117 = lean_ctor_get(x_1, 7);
lean_inc(x_1117);
lean_dec(x_1);
x_1118 = l_Lake_importConfigFileCore(x_21, x_1117, x_1051);
lean_dec(x_21);
if (lean_obj_tag(x_1118) == 0)
{
lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; 
x_1119 = lean_ctor_get(x_1118, 0);
lean_inc(x_1119);
x_1120 = lean_ctor_get(x_1118, 1);
lean_inc(x_1120);
lean_dec(x_1118);
x_1121 = lean_io_prim_handle_unlock(x_529, x_1120);
lean_dec(x_529);
if (lean_obj_tag(x_1121) == 0)
{
uint8_t x_1122; 
x_1122 = !lean_is_exclusive(x_1121);
if (x_1122 == 0)
{
lean_object* x_1123; lean_object* x_1124; 
x_1123 = lean_ctor_get(x_1121, 0);
lean_dec(x_1123);
if (lean_is_scalar(x_32)) {
 x_1124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1124 = x_32;
}
lean_ctor_set(x_1124, 0, x_1119);
lean_ctor_set(x_1124, 1, x_535);
lean_ctor_set(x_1121, 0, x_1124);
return x_1121;
}
else
{
lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1125 = lean_ctor_get(x_1121, 1);
lean_inc(x_1125);
lean_dec(x_1121);
if (lean_is_scalar(x_32)) {
 x_1126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1126 = x_32;
}
lean_ctor_set(x_1126, 0, x_1119);
lean_ctor_set(x_1126, 1, x_535);
x_1127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1127, 0, x_1126);
lean_ctor_set(x_1127, 1, x_1125);
return x_1127;
}
}
else
{
uint8_t x_1128; 
lean_dec(x_1119);
x_1128 = !lean_is_exclusive(x_1121);
if (x_1128 == 0)
{
lean_object* x_1129; lean_object* x_1130; uint8_t x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; 
x_1129 = lean_ctor_get(x_1121, 0);
x_1130 = lean_io_error_to_string(x_1129);
x_1131 = 3;
x_1132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set_uint8(x_1132, sizeof(void*)*1, x_1131);
x_1133 = lean_array_get_size(x_535);
x_1134 = lean_array_push(x_535, x_1132);
if (lean_is_scalar(x_32)) {
 x_1135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1135 = x_32;
 lean_ctor_set_tag(x_1135, 1);
}
lean_ctor_set(x_1135, 0, x_1133);
lean_ctor_set(x_1135, 1, x_1134);
lean_ctor_set_tag(x_1121, 0);
lean_ctor_set(x_1121, 0, x_1135);
return x_1121;
}
else
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; uint8_t x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; 
x_1136 = lean_ctor_get(x_1121, 0);
x_1137 = lean_ctor_get(x_1121, 1);
lean_inc(x_1137);
lean_inc(x_1136);
lean_dec(x_1121);
x_1138 = lean_io_error_to_string(x_1136);
x_1139 = 3;
x_1140 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1140, 0, x_1138);
lean_ctor_set_uint8(x_1140, sizeof(void*)*1, x_1139);
x_1141 = lean_array_get_size(x_535);
x_1142 = lean_array_push(x_535, x_1140);
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
else
{
uint8_t x_1145; 
lean_dec(x_529);
x_1145 = !lean_is_exclusive(x_1118);
if (x_1145 == 0)
{
lean_object* x_1146; lean_object* x_1147; uint8_t x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
x_1146 = lean_ctor_get(x_1118, 0);
x_1147 = lean_io_error_to_string(x_1146);
x_1148 = 3;
x_1149 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1149, 0, x_1147);
lean_ctor_set_uint8(x_1149, sizeof(void*)*1, x_1148);
x_1150 = lean_array_get_size(x_535);
x_1151 = lean_array_push(x_535, x_1149);
if (lean_is_scalar(x_32)) {
 x_1152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1152 = x_32;
 lean_ctor_set_tag(x_1152, 1);
}
lean_ctor_set(x_1152, 0, x_1150);
lean_ctor_set(x_1152, 1, x_1151);
lean_ctor_set_tag(x_1118, 0);
lean_ctor_set(x_1118, 0, x_1152);
return x_1118;
}
else
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; uint8_t x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
x_1153 = lean_ctor_get(x_1118, 0);
x_1154 = lean_ctor_get(x_1118, 1);
lean_inc(x_1154);
lean_inc(x_1153);
lean_dec(x_1118);
x_1155 = lean_io_error_to_string(x_1153);
x_1156 = 3;
x_1157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1157, 0, x_1155);
lean_ctor_set_uint8(x_1157, sizeof(void*)*1, x_1156);
x_1158 = lean_array_get_size(x_535);
x_1159 = lean_array_push(x_535, x_1157);
if (lean_is_scalar(x_32)) {
 x_1160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1160 = x_32;
 lean_ctor_set_tag(x_1160, 1);
}
lean_ctor_set(x_1160, 0, x_1158);
lean_ctor_set(x_1160, 1, x_1159);
x_1161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1161, 0, x_1160);
lean_ctor_set(x_1161, 1, x_1154);
return x_1161;
}
}
}
}
}
}
block_1048:
{
if (lean_obj_tag(x_553) == 0)
{
uint8_t x_555; 
x_555 = !lean_is_exclusive(x_553);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_658; lean_object* x_659; lean_object* x_867; 
x_556 = lean_ctor_get(x_553, 0);
x_557 = lean_ctor_get(x_551, 3);
lean_inc(x_557);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 lean_ctor_release(x_551, 2);
 lean_ctor_release(x_551, 3);
 x_558 = x_551;
} else {
 lean_dec_ref(x_551);
 x_558 = lean_box(0);
}
x_867 = lean_io_remove_file(x_21, x_554);
if (lean_obj_tag(x_867) == 0)
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_867, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_867, 1);
lean_inc(x_869);
lean_dec(x_867);
if (lean_is_scalar(x_552)) {
 x_870 = lean_alloc_ctor(1, 1, 0);
} else {
 x_870 = x_552;
}
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_553, 0, x_870);
x_658 = x_553;
x_659 = x_869;
goto block_866;
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; 
x_871 = lean_ctor_get(x_867, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_867, 1);
lean_inc(x_872);
lean_dec(x_867);
if (lean_is_scalar(x_552)) {
 x_873 = lean_alloc_ctor(0, 1, 0);
} else {
 x_873 = x_552;
 lean_ctor_set_tag(x_873, 0);
}
lean_ctor_set(x_873, 0, x_871);
lean_ctor_set(x_553, 0, x_873);
x_658 = x_553;
x_659 = x_872;
goto block_866;
}
block_657:
{
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_ctor_get(x_1, 7);
lean_inc(x_562);
lean_dec(x_1);
x_563 = l_Lake_elabConfigFile(x_6, x_557, x_562, x_8, x_561, x_560);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; uint8_t x_566; 
x_565 = lean_ctor_get(x_563, 1);
lean_inc(x_565);
lean_dec(x_563);
x_566 = !lean_is_exclusive(x_564);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_567 = lean_ctor_get(x_564, 0);
x_568 = lean_ctor_get(x_564, 1);
lean_inc(x_567);
x_569 = lean_write_module(x_567, x_21, x_565);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; 
x_570 = lean_ctor_get(x_569, 1);
lean_inc(x_570);
lean_dec(x_569);
x_571 = lean_io_prim_handle_unlock(x_556, x_570);
lean_dec(x_556);
if (lean_obj_tag(x_571) == 0)
{
uint8_t x_572; 
x_572 = !lean_is_exclusive(x_571);
if (x_572 == 0)
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_571, 0);
lean_dec(x_573);
lean_ctor_set(x_571, 0, x_564);
return x_571;
}
else
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_571, 1);
lean_inc(x_574);
lean_dec(x_571);
x_575 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_575, 0, x_564);
lean_ctor_set(x_575, 1, x_574);
return x_575;
}
}
else
{
uint8_t x_576; 
lean_dec(x_567);
x_576 = !lean_is_exclusive(x_571);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; uint8_t x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_577 = lean_ctor_get(x_571, 0);
x_578 = lean_io_error_to_string(x_577);
x_579 = 3;
x_580 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_580, 0, x_578);
lean_ctor_set_uint8(x_580, sizeof(void*)*1, x_579);
x_581 = lean_array_get_size(x_568);
x_582 = lean_array_push(x_568, x_580);
lean_ctor_set_tag(x_564, 1);
lean_ctor_set(x_564, 1, x_582);
lean_ctor_set(x_564, 0, x_581);
lean_ctor_set_tag(x_571, 0);
lean_ctor_set(x_571, 0, x_564);
return x_571;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_583 = lean_ctor_get(x_571, 0);
x_584 = lean_ctor_get(x_571, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_571);
x_585 = lean_io_error_to_string(x_583);
x_586 = 3;
x_587 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set_uint8(x_587, sizeof(void*)*1, x_586);
x_588 = lean_array_get_size(x_568);
x_589 = lean_array_push(x_568, x_587);
lean_ctor_set_tag(x_564, 1);
lean_ctor_set(x_564, 1, x_589);
lean_ctor_set(x_564, 0, x_588);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_564);
lean_ctor_set(x_590, 1, x_584);
return x_590;
}
}
}
else
{
uint8_t x_591; 
lean_dec(x_567);
lean_dec(x_556);
x_591 = !lean_is_exclusive(x_569);
if (x_591 == 0)
{
lean_object* x_592; lean_object* x_593; uint8_t x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_592 = lean_ctor_get(x_569, 0);
x_593 = lean_io_error_to_string(x_592);
x_594 = 3;
x_595 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_595, 0, x_593);
lean_ctor_set_uint8(x_595, sizeof(void*)*1, x_594);
x_596 = lean_array_get_size(x_568);
x_597 = lean_array_push(x_568, x_595);
lean_ctor_set_tag(x_564, 1);
lean_ctor_set(x_564, 1, x_597);
lean_ctor_set(x_564, 0, x_596);
lean_ctor_set_tag(x_569, 0);
lean_ctor_set(x_569, 0, x_564);
return x_569;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_598 = lean_ctor_get(x_569, 0);
x_599 = lean_ctor_get(x_569, 1);
lean_inc(x_599);
lean_inc(x_598);
lean_dec(x_569);
x_600 = lean_io_error_to_string(x_598);
x_601 = 3;
x_602 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set_uint8(x_602, sizeof(void*)*1, x_601);
x_603 = lean_array_get_size(x_568);
x_604 = lean_array_push(x_568, x_602);
lean_ctor_set_tag(x_564, 1);
lean_ctor_set(x_564, 1, x_604);
lean_ctor_set(x_564, 0, x_603);
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_564);
lean_ctor_set(x_605, 1, x_599);
return x_605;
}
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_564, 0);
x_607 = lean_ctor_get(x_564, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_564);
lean_inc(x_606);
x_608 = lean_write_module(x_606, x_21, x_565);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; 
x_609 = lean_ctor_get(x_608, 1);
lean_inc(x_609);
lean_dec(x_608);
x_610 = lean_io_prim_handle_unlock(x_556, x_609);
lean_dec(x_556);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_611 = lean_ctor_get(x_610, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_612 = x_610;
} else {
 lean_dec_ref(x_610);
 x_612 = lean_box(0);
}
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_606);
lean_ctor_set(x_613, 1, x_607);
if (lean_is_scalar(x_612)) {
 x_614 = lean_alloc_ctor(0, 2, 0);
} else {
 x_614 = x_612;
}
lean_ctor_set(x_614, 0, x_613);
lean_ctor_set(x_614, 1, x_611);
return x_614;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; uint8_t x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_606);
x_615 = lean_ctor_get(x_610, 0);
lean_inc(x_615);
x_616 = lean_ctor_get(x_610, 1);
lean_inc(x_616);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_617 = x_610;
} else {
 lean_dec_ref(x_610);
 x_617 = lean_box(0);
}
x_618 = lean_io_error_to_string(x_615);
x_619 = 3;
x_620 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set_uint8(x_620, sizeof(void*)*1, x_619);
x_621 = lean_array_get_size(x_607);
x_622 = lean_array_push(x_607, x_620);
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
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; uint8_t x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_606);
lean_dec(x_556);
x_625 = lean_ctor_get(x_608, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_608, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_627 = x_608;
} else {
 lean_dec_ref(x_608);
 x_627 = lean_box(0);
}
x_628 = lean_io_error_to_string(x_625);
x_629 = 3;
x_630 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set_uint8(x_630, sizeof(void*)*1, x_629);
x_631 = lean_array_get_size(x_607);
x_632 = lean_array_push(x_607, x_630);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
if (lean_is_scalar(x_627)) {
 x_634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_634 = x_627;
 lean_ctor_set_tag(x_634, 0);
}
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_626);
return x_634;
}
}
}
else
{
uint8_t x_635; 
lean_dec(x_556);
lean_dec(x_21);
x_635 = !lean_is_exclusive(x_563);
if (x_635 == 0)
{
lean_object* x_636; uint8_t x_637; 
x_636 = lean_ctor_get(x_563, 0);
lean_dec(x_636);
x_637 = !lean_is_exclusive(x_564);
if (x_637 == 0)
{
return x_563;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_564, 0);
x_639 = lean_ctor_get(x_564, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_564);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
lean_ctor_set(x_563, 0, x_640);
return x_563;
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_641 = lean_ctor_get(x_563, 1);
lean_inc(x_641);
lean_dec(x_563);
x_642 = lean_ctor_get(x_564, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_564, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_644 = x_564;
} else {
 lean_dec_ref(x_564);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(1, 2, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_642);
lean_ctor_set(x_645, 1, x_643);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_641);
return x_646;
}
}
}
else
{
uint8_t x_647; 
lean_dec(x_556);
lean_dec(x_21);
x_647 = !lean_is_exclusive(x_563);
if (x_647 == 0)
{
return x_563;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_563, 0);
x_649 = lean_ctor_get(x_563, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_563);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
else
{
uint8_t x_651; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_651 = !lean_is_exclusive(x_559);
if (x_651 == 0)
{
lean_object* x_652; 
x_652 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_652, 0, x_559);
lean_ctor_set(x_652, 1, x_560);
return x_652;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_653 = lean_ctor_get(x_559, 0);
x_654 = lean_ctor_get(x_559, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_559);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_653);
lean_ctor_set(x_655, 1, x_654);
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_560);
return x_656;
}
}
}
block_866:
{
lean_object* x_660; 
x_660 = lean_ctor_get(x_658, 0);
lean_inc(x_660);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
lean_dec(x_660);
if (lean_obj_tag(x_661) == 11)
{
uint8_t x_662; 
lean_dec(x_661);
lean_dec(x_24);
x_662 = !lean_is_exclusive(x_658);
if (x_662 == 0)
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_663 = lean_ctor_get(x_658, 1);
x_664 = lean_ctor_get(x_658, 0);
lean_dec(x_664);
x_665 = lean_ctor_get(x_1, 0);
lean_inc(x_665);
x_666 = l_Lake_Env_leanGithash(x_665);
lean_dec(x_665);
x_667 = l_System_Platform_target;
lean_inc(x_557);
if (lean_is_scalar(x_558)) {
 x_668 = lean_alloc_ctor(0, 4, 0);
} else {
 x_668 = x_558;
}
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_666);
lean_ctor_set(x_668, 2, x_30);
lean_ctor_set(x_668, 3, x_557);
x_669 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_668);
x_670 = lean_unsigned_to_nat(80u);
x_671 = l_Lean_Json_pretty(x_669, x_670);
x_672 = l_IO_FS_Handle_putStrLn(x_556, x_671, x_659);
if (lean_obj_tag(x_672) == 0)
{
lean_object* x_673; lean_object* x_674; 
x_673 = lean_ctor_get(x_672, 1);
lean_inc(x_673);
lean_dec(x_672);
x_674 = lean_io_prim_handle_truncate(x_556, x_673);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
lean_ctor_set(x_658, 0, x_675);
x_559 = x_658;
x_560 = x_676;
goto block_657;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; uint8_t x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_677 = lean_ctor_get(x_674, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_674, 1);
lean_inc(x_678);
lean_dec(x_674);
x_679 = lean_io_error_to_string(x_677);
x_680 = 3;
x_681 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_681, 0, x_679);
lean_ctor_set_uint8(x_681, sizeof(void*)*1, x_680);
x_682 = lean_array_get_size(x_663);
x_683 = lean_array_push(x_663, x_681);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_683);
lean_ctor_set(x_658, 0, x_682);
x_559 = x_658;
x_560 = x_678;
goto block_657;
}
}
else
{
uint8_t x_684; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_684 = !lean_is_exclusive(x_672);
if (x_684 == 0)
{
lean_object* x_685; lean_object* x_686; uint8_t x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_685 = lean_ctor_get(x_672, 0);
x_686 = lean_io_error_to_string(x_685);
x_687 = 3;
x_688 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set_uint8(x_688, sizeof(void*)*1, x_687);
x_689 = lean_array_get_size(x_663);
x_690 = lean_array_push(x_663, x_688);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_690);
lean_ctor_set(x_658, 0, x_689);
lean_ctor_set_tag(x_672, 0);
lean_ctor_set(x_672, 0, x_658);
return x_672;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_691 = lean_ctor_get(x_672, 0);
x_692 = lean_ctor_get(x_672, 1);
lean_inc(x_692);
lean_inc(x_691);
lean_dec(x_672);
x_693 = lean_io_error_to_string(x_691);
x_694 = 3;
x_695 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_695, 0, x_693);
lean_ctor_set_uint8(x_695, sizeof(void*)*1, x_694);
x_696 = lean_array_get_size(x_663);
x_697 = lean_array_push(x_663, x_695);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_697);
lean_ctor_set(x_658, 0, x_696);
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_658);
lean_ctor_set(x_698, 1, x_692);
return x_698;
}
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_699 = lean_ctor_get(x_658, 1);
lean_inc(x_699);
lean_dec(x_658);
x_700 = lean_ctor_get(x_1, 0);
lean_inc(x_700);
x_701 = l_Lake_Env_leanGithash(x_700);
lean_dec(x_700);
x_702 = l_System_Platform_target;
lean_inc(x_557);
if (lean_is_scalar(x_558)) {
 x_703 = lean_alloc_ctor(0, 4, 0);
} else {
 x_703 = x_558;
}
lean_ctor_set(x_703, 0, x_702);
lean_ctor_set(x_703, 1, x_701);
lean_ctor_set(x_703, 2, x_30);
lean_ctor_set(x_703, 3, x_557);
x_704 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_703);
x_705 = lean_unsigned_to_nat(80u);
x_706 = l_Lean_Json_pretty(x_704, x_705);
x_707 = l_IO_FS_Handle_putStrLn(x_556, x_706, x_659);
if (lean_obj_tag(x_707) == 0)
{
lean_object* x_708; lean_object* x_709; 
x_708 = lean_ctor_get(x_707, 1);
lean_inc(x_708);
lean_dec(x_707);
x_709 = lean_io_prim_handle_truncate(x_556, x_708);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec(x_709);
x_712 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_712, 0, x_710);
lean_ctor_set(x_712, 1, x_699);
x_559 = x_712;
x_560 = x_711;
goto block_657;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; uint8_t x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_713 = lean_ctor_get(x_709, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_709, 1);
lean_inc(x_714);
lean_dec(x_709);
x_715 = lean_io_error_to_string(x_713);
x_716 = 3;
x_717 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set_uint8(x_717, sizeof(void*)*1, x_716);
x_718 = lean_array_get_size(x_699);
x_719 = lean_array_push(x_699, x_717);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
x_559 = x_720;
x_560 = x_714;
goto block_657;
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_721 = lean_ctor_get(x_707, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_707, 1);
lean_inc(x_722);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_723 = x_707;
} else {
 lean_dec_ref(x_707);
 x_723 = lean_box(0);
}
x_724 = lean_io_error_to_string(x_721);
x_725 = 3;
x_726 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_726, 0, x_724);
lean_ctor_set_uint8(x_726, sizeof(void*)*1, x_725);
x_727 = lean_array_get_size(x_699);
x_728 = lean_array_push(x_699, x_726);
x_729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_729, 0, x_727);
lean_ctor_set(x_729, 1, x_728);
if (lean_is_scalar(x_723)) {
 x_730 = lean_alloc_ctor(0, 2, 0);
} else {
 x_730 = x_723;
 lean_ctor_set_tag(x_730, 0);
}
lean_ctor_set(x_730, 0, x_729);
lean_ctor_set(x_730, 1, x_722);
return x_730;
}
}
}
else
{
uint8_t x_731; 
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_731 = !lean_is_exclusive(x_658);
if (x_731 == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; uint8_t x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_732 = lean_ctor_get(x_658, 1);
x_733 = lean_ctor_get(x_658, 0);
lean_dec(x_733);
x_734 = lean_io_error_to_string(x_661);
x_735 = 3;
x_736 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_736, 0, x_734);
lean_ctor_set_uint8(x_736, sizeof(void*)*1, x_735);
x_737 = lean_array_get_size(x_732);
x_738 = lean_array_push(x_732, x_736);
x_739 = lean_io_prim_handle_unlock(x_556, x_659);
lean_dec(x_556);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; lean_object* x_741; 
x_740 = lean_ctor_get(x_739, 1);
lean_inc(x_740);
lean_dec(x_739);
x_741 = lean_io_remove_file(x_24, x_740);
lean_dec(x_24);
if (lean_obj_tag(x_741) == 0)
{
uint8_t x_742; 
x_742 = !lean_is_exclusive(x_741);
if (x_742 == 0)
{
lean_object* x_743; 
x_743 = lean_ctor_get(x_741, 0);
lean_dec(x_743);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_738);
lean_ctor_set(x_658, 0, x_737);
lean_ctor_set(x_741, 0, x_658);
return x_741;
}
else
{
lean_object* x_744; lean_object* x_745; 
x_744 = lean_ctor_get(x_741, 1);
lean_inc(x_744);
lean_dec(x_741);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_738);
lean_ctor_set(x_658, 0, x_737);
x_745 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_745, 0, x_658);
lean_ctor_set(x_745, 1, x_744);
return x_745;
}
}
else
{
uint8_t x_746; 
x_746 = !lean_is_exclusive(x_741);
if (x_746 == 0)
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_747 = lean_ctor_get(x_741, 0);
x_748 = lean_io_error_to_string(x_747);
x_749 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set_uint8(x_749, sizeof(void*)*1, x_735);
x_750 = lean_array_push(x_738, x_749);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_750);
lean_ctor_set(x_658, 0, x_737);
lean_ctor_set_tag(x_741, 0);
lean_ctor_set(x_741, 0, x_658);
return x_741;
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_751 = lean_ctor_get(x_741, 0);
x_752 = lean_ctor_get(x_741, 1);
lean_inc(x_752);
lean_inc(x_751);
lean_dec(x_741);
x_753 = lean_io_error_to_string(x_751);
x_754 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_754, 0, x_753);
lean_ctor_set_uint8(x_754, sizeof(void*)*1, x_735);
x_755 = lean_array_push(x_738, x_754);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_755);
lean_ctor_set(x_658, 0, x_737);
x_756 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_756, 0, x_658);
lean_ctor_set(x_756, 1, x_752);
return x_756;
}
}
}
else
{
uint8_t x_757; 
lean_dec(x_24);
x_757 = !lean_is_exclusive(x_739);
if (x_757 == 0)
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_758 = lean_ctor_get(x_739, 0);
x_759 = lean_io_error_to_string(x_758);
x_760 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set_uint8(x_760, sizeof(void*)*1, x_735);
x_761 = lean_array_push(x_738, x_760);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_761);
lean_ctor_set(x_658, 0, x_737);
lean_ctor_set_tag(x_739, 0);
lean_ctor_set(x_739, 0, x_658);
return x_739;
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; 
x_762 = lean_ctor_get(x_739, 0);
x_763 = lean_ctor_get(x_739, 1);
lean_inc(x_763);
lean_inc(x_762);
lean_dec(x_739);
x_764 = lean_io_error_to_string(x_762);
x_765 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_765, 0, x_764);
lean_ctor_set_uint8(x_765, sizeof(void*)*1, x_735);
x_766 = lean_array_push(x_738, x_765);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_766);
lean_ctor_set(x_658, 0, x_737);
x_767 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_767, 0, x_658);
lean_ctor_set(x_767, 1, x_763);
return x_767;
}
}
}
else
{
lean_object* x_768; lean_object* x_769; uint8_t x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_768 = lean_ctor_get(x_658, 1);
lean_inc(x_768);
lean_dec(x_658);
x_769 = lean_io_error_to_string(x_661);
x_770 = 3;
x_771 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_771, 0, x_769);
lean_ctor_set_uint8(x_771, sizeof(void*)*1, x_770);
x_772 = lean_array_get_size(x_768);
x_773 = lean_array_push(x_768, x_771);
x_774 = lean_io_prim_handle_unlock(x_556, x_659);
lean_dec(x_556);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; 
x_775 = lean_ctor_get(x_774, 1);
lean_inc(x_775);
lean_dec(x_774);
x_776 = lean_io_remove_file(x_24, x_775);
lean_dec(x_24);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_777 = lean_ctor_get(x_776, 1);
lean_inc(x_777);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_778 = x_776;
} else {
 lean_dec_ref(x_776);
 x_778 = lean_box(0);
}
x_779 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_779, 0, x_772);
lean_ctor_set(x_779, 1, x_773);
if (lean_is_scalar(x_778)) {
 x_780 = lean_alloc_ctor(0, 2, 0);
} else {
 x_780 = x_778;
}
lean_ctor_set(x_780, 0, x_779);
lean_ctor_set(x_780, 1, x_777);
return x_780;
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_781 = lean_ctor_get(x_776, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_776, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_783 = x_776;
} else {
 lean_dec_ref(x_776);
 x_783 = lean_box(0);
}
x_784 = lean_io_error_to_string(x_781);
x_785 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set_uint8(x_785, sizeof(void*)*1, x_770);
x_786 = lean_array_push(x_773, x_785);
x_787 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_787, 0, x_772);
lean_ctor_set(x_787, 1, x_786);
if (lean_is_scalar(x_783)) {
 x_788 = lean_alloc_ctor(0, 2, 0);
} else {
 x_788 = x_783;
 lean_ctor_set_tag(x_788, 0);
}
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_782);
return x_788;
}
}
else
{
lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
lean_dec(x_24);
x_789 = lean_ctor_get(x_774, 0);
lean_inc(x_789);
x_790 = lean_ctor_get(x_774, 1);
lean_inc(x_790);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_791 = x_774;
} else {
 lean_dec_ref(x_774);
 x_791 = lean_box(0);
}
x_792 = lean_io_error_to_string(x_789);
x_793 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set_uint8(x_793, sizeof(void*)*1, x_770);
x_794 = lean_array_push(x_773, x_793);
x_795 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_795, 0, x_772);
lean_ctor_set(x_795, 1, x_794);
if (lean_is_scalar(x_791)) {
 x_796 = lean_alloc_ctor(0, 2, 0);
} else {
 x_796 = x_791;
 lean_ctor_set_tag(x_796, 0);
}
lean_ctor_set(x_796, 0, x_795);
lean_ctor_set(x_796, 1, x_790);
return x_796;
}
}
}
}
else
{
uint8_t x_797; 
lean_dec(x_660);
lean_dec(x_24);
x_797 = !lean_is_exclusive(x_658);
if (x_797 == 0)
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_798 = lean_ctor_get(x_658, 1);
x_799 = lean_ctor_get(x_658, 0);
lean_dec(x_799);
x_800 = lean_ctor_get(x_1, 0);
lean_inc(x_800);
x_801 = l_Lake_Env_leanGithash(x_800);
lean_dec(x_800);
x_802 = l_System_Platform_target;
lean_inc(x_557);
if (lean_is_scalar(x_558)) {
 x_803 = lean_alloc_ctor(0, 4, 0);
} else {
 x_803 = x_558;
}
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_801);
lean_ctor_set(x_803, 2, x_30);
lean_ctor_set(x_803, 3, x_557);
x_804 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_803);
x_805 = lean_unsigned_to_nat(80u);
x_806 = l_Lean_Json_pretty(x_804, x_805);
x_807 = l_IO_FS_Handle_putStrLn(x_556, x_806, x_659);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; 
x_808 = lean_ctor_get(x_807, 1);
lean_inc(x_808);
lean_dec(x_807);
x_809 = lean_io_prim_handle_truncate(x_556, x_808);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_ctor_get(x_809, 0);
lean_inc(x_810);
x_811 = lean_ctor_get(x_809, 1);
lean_inc(x_811);
lean_dec(x_809);
lean_ctor_set(x_658, 0, x_810);
x_559 = x_658;
x_560 = x_811;
goto block_657;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; uint8_t x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_812 = lean_ctor_get(x_809, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_809, 1);
lean_inc(x_813);
lean_dec(x_809);
x_814 = lean_io_error_to_string(x_812);
x_815 = 3;
x_816 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_816, 0, x_814);
lean_ctor_set_uint8(x_816, sizeof(void*)*1, x_815);
x_817 = lean_array_get_size(x_798);
x_818 = lean_array_push(x_798, x_816);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_818);
lean_ctor_set(x_658, 0, x_817);
x_559 = x_658;
x_560 = x_813;
goto block_657;
}
}
else
{
uint8_t x_819; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_819 = !lean_is_exclusive(x_807);
if (x_819 == 0)
{
lean_object* x_820; lean_object* x_821; uint8_t x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_820 = lean_ctor_get(x_807, 0);
x_821 = lean_io_error_to_string(x_820);
x_822 = 3;
x_823 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set_uint8(x_823, sizeof(void*)*1, x_822);
x_824 = lean_array_get_size(x_798);
x_825 = lean_array_push(x_798, x_823);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_825);
lean_ctor_set(x_658, 0, x_824);
lean_ctor_set_tag(x_807, 0);
lean_ctor_set(x_807, 0, x_658);
return x_807;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; uint8_t x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_826 = lean_ctor_get(x_807, 0);
x_827 = lean_ctor_get(x_807, 1);
lean_inc(x_827);
lean_inc(x_826);
lean_dec(x_807);
x_828 = lean_io_error_to_string(x_826);
x_829 = 3;
x_830 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_830, 0, x_828);
lean_ctor_set_uint8(x_830, sizeof(void*)*1, x_829);
x_831 = lean_array_get_size(x_798);
x_832 = lean_array_push(x_798, x_830);
lean_ctor_set_tag(x_658, 1);
lean_ctor_set(x_658, 1, x_832);
lean_ctor_set(x_658, 0, x_831);
x_833 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_833, 0, x_658);
lean_ctor_set(x_833, 1, x_827);
return x_833;
}
}
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
x_834 = lean_ctor_get(x_658, 1);
lean_inc(x_834);
lean_dec(x_658);
x_835 = lean_ctor_get(x_1, 0);
lean_inc(x_835);
x_836 = l_Lake_Env_leanGithash(x_835);
lean_dec(x_835);
x_837 = l_System_Platform_target;
lean_inc(x_557);
if (lean_is_scalar(x_558)) {
 x_838 = lean_alloc_ctor(0, 4, 0);
} else {
 x_838 = x_558;
}
lean_ctor_set(x_838, 0, x_837);
lean_ctor_set(x_838, 1, x_836);
lean_ctor_set(x_838, 2, x_30);
lean_ctor_set(x_838, 3, x_557);
x_839 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_838);
x_840 = lean_unsigned_to_nat(80u);
x_841 = l_Lean_Json_pretty(x_839, x_840);
x_842 = l_IO_FS_Handle_putStrLn(x_556, x_841, x_659);
if (lean_obj_tag(x_842) == 0)
{
lean_object* x_843; lean_object* x_844; 
x_843 = lean_ctor_get(x_842, 1);
lean_inc(x_843);
lean_dec(x_842);
x_844 = lean_io_prim_handle_truncate(x_556, x_843);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_844, 1);
lean_inc(x_846);
lean_dec(x_844);
x_847 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_847, 0, x_845);
lean_ctor_set(x_847, 1, x_834);
x_559 = x_847;
x_560 = x_846;
goto block_657;
}
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; uint8_t x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_848 = lean_ctor_get(x_844, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_844, 1);
lean_inc(x_849);
lean_dec(x_844);
x_850 = lean_io_error_to_string(x_848);
x_851 = 3;
x_852 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_852, 0, x_850);
lean_ctor_set_uint8(x_852, sizeof(void*)*1, x_851);
x_853 = lean_array_get_size(x_834);
x_854 = lean_array_push(x_834, x_852);
x_855 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_855, 0, x_853);
lean_ctor_set(x_855, 1, x_854);
x_559 = x_855;
x_560 = x_849;
goto block_657;
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; uint8_t x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_856 = lean_ctor_get(x_842, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_842, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_842)) {
 lean_ctor_release(x_842, 0);
 lean_ctor_release(x_842, 1);
 x_858 = x_842;
} else {
 lean_dec_ref(x_842);
 x_858 = lean_box(0);
}
x_859 = lean_io_error_to_string(x_856);
x_860 = 3;
x_861 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_861, 0, x_859);
lean_ctor_set_uint8(x_861, sizeof(void*)*1, x_860);
x_862 = lean_array_get_size(x_834);
x_863 = lean_array_push(x_834, x_861);
x_864 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_864, 0, x_862);
lean_ctor_set(x_864, 1, x_863);
if (lean_is_scalar(x_858)) {
 x_865 = lean_alloc_ctor(0, 2, 0);
} else {
 x_865 = x_858;
 lean_ctor_set_tag(x_865, 0);
}
lean_ctor_set(x_865, 0, x_864);
lean_ctor_set(x_865, 1, x_857);
return x_865;
}
}
}
}
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_932; lean_object* x_933; lean_object* x_1033; 
x_874 = lean_ctor_get(x_553, 0);
x_875 = lean_ctor_get(x_553, 1);
lean_inc(x_875);
lean_inc(x_874);
lean_dec(x_553);
x_876 = lean_ctor_get(x_551, 3);
lean_inc(x_876);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 lean_ctor_release(x_551, 2);
 lean_ctor_release(x_551, 3);
 x_877 = x_551;
} else {
 lean_dec_ref(x_551);
 x_877 = lean_box(0);
}
x_1033 = lean_io_remove_file(x_21, x_554);
if (lean_obj_tag(x_1033) == 0)
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1034 = lean_ctor_get(x_1033, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1033, 1);
lean_inc(x_1035);
lean_dec(x_1033);
if (lean_is_scalar(x_552)) {
 x_1036 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1036 = x_552;
}
lean_ctor_set(x_1036, 0, x_1034);
x_1037 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1037, 0, x_1036);
lean_ctor_set(x_1037, 1, x_875);
x_932 = x_1037;
x_933 = x_1035;
goto block_1032;
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1038 = lean_ctor_get(x_1033, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1033, 1);
lean_inc(x_1039);
lean_dec(x_1033);
if (lean_is_scalar(x_552)) {
 x_1040 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1040 = x_552;
 lean_ctor_set_tag(x_1040, 0);
}
lean_ctor_set(x_1040, 0, x_1038);
x_1041 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1041, 0, x_1040);
lean_ctor_set(x_1041, 1, x_875);
x_932 = x_1041;
x_933 = x_1039;
goto block_1032;
}
block_931:
{
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; 
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_ctor_get(x_1, 7);
lean_inc(x_881);
lean_dec(x_1);
x_882 = l_Lake_elabConfigFile(x_6, x_876, x_881, x_8, x_880, x_879);
if (lean_obj_tag(x_882) == 0)
{
lean_object* x_883; 
x_883 = lean_ctor_get(x_882, 0);
lean_inc(x_883);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
x_884 = lean_ctor_get(x_882, 1);
lean_inc(x_884);
lean_dec(x_882);
x_885 = lean_ctor_get(x_883, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_883, 1);
lean_inc(x_886);
if (lean_is_exclusive(x_883)) {
 lean_ctor_release(x_883, 0);
 lean_ctor_release(x_883, 1);
 x_887 = x_883;
} else {
 lean_dec_ref(x_883);
 x_887 = lean_box(0);
}
lean_inc(x_885);
x_888 = lean_write_module(x_885, x_21, x_884);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; 
x_889 = lean_ctor_get(x_888, 1);
lean_inc(x_889);
lean_dec(x_888);
x_890 = lean_io_prim_handle_unlock(x_874, x_889);
lean_dec(x_874);
if (lean_obj_tag(x_890) == 0)
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_891 = lean_ctor_get(x_890, 1);
lean_inc(x_891);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_892 = x_890;
} else {
 lean_dec_ref(x_890);
 x_892 = lean_box(0);
}
if (lean_is_scalar(x_887)) {
 x_893 = lean_alloc_ctor(0, 2, 0);
} else {
 x_893 = x_887;
}
lean_ctor_set(x_893, 0, x_885);
lean_ctor_set(x_893, 1, x_886);
if (lean_is_scalar(x_892)) {
 x_894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_894 = x_892;
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_891);
return x_894;
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; uint8_t x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
lean_dec(x_885);
x_895 = lean_ctor_get(x_890, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_890, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_890)) {
 lean_ctor_release(x_890, 0);
 lean_ctor_release(x_890, 1);
 x_897 = x_890;
} else {
 lean_dec_ref(x_890);
 x_897 = lean_box(0);
}
x_898 = lean_io_error_to_string(x_895);
x_899 = 3;
x_900 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_900, 0, x_898);
lean_ctor_set_uint8(x_900, sizeof(void*)*1, x_899);
x_901 = lean_array_get_size(x_886);
x_902 = lean_array_push(x_886, x_900);
if (lean_is_scalar(x_887)) {
 x_903 = lean_alloc_ctor(1, 2, 0);
} else {
 x_903 = x_887;
 lean_ctor_set_tag(x_903, 1);
}
lean_ctor_set(x_903, 0, x_901);
lean_ctor_set(x_903, 1, x_902);
if (lean_is_scalar(x_897)) {
 x_904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_904 = x_897;
 lean_ctor_set_tag(x_904, 0);
}
lean_ctor_set(x_904, 0, x_903);
lean_ctor_set(x_904, 1, x_896);
return x_904;
}
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; uint8_t x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec(x_885);
lean_dec(x_874);
x_905 = lean_ctor_get(x_888, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_888, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_907 = x_888;
} else {
 lean_dec_ref(x_888);
 x_907 = lean_box(0);
}
x_908 = lean_io_error_to_string(x_905);
x_909 = 3;
x_910 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_910, 0, x_908);
lean_ctor_set_uint8(x_910, sizeof(void*)*1, x_909);
x_911 = lean_array_get_size(x_886);
x_912 = lean_array_push(x_886, x_910);
if (lean_is_scalar(x_887)) {
 x_913 = lean_alloc_ctor(1, 2, 0);
} else {
 x_913 = x_887;
 lean_ctor_set_tag(x_913, 1);
}
lean_ctor_set(x_913, 0, x_911);
lean_ctor_set(x_913, 1, x_912);
if (lean_is_scalar(x_907)) {
 x_914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_914 = x_907;
 lean_ctor_set_tag(x_914, 0);
}
lean_ctor_set(x_914, 0, x_913);
lean_ctor_set(x_914, 1, x_906);
return x_914;
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_874);
lean_dec(x_21);
x_915 = lean_ctor_get(x_882, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 x_916 = x_882;
} else {
 lean_dec_ref(x_882);
 x_916 = lean_box(0);
}
x_917 = lean_ctor_get(x_883, 0);
lean_inc(x_917);
x_918 = lean_ctor_get(x_883, 1);
lean_inc(x_918);
if (lean_is_exclusive(x_883)) {
 lean_ctor_release(x_883, 0);
 lean_ctor_release(x_883, 1);
 x_919 = x_883;
} else {
 lean_dec_ref(x_883);
 x_919 = lean_box(0);
}
if (lean_is_scalar(x_919)) {
 x_920 = lean_alloc_ctor(1, 2, 0);
} else {
 x_920 = x_919;
}
lean_ctor_set(x_920, 0, x_917);
lean_ctor_set(x_920, 1, x_918);
if (lean_is_scalar(x_916)) {
 x_921 = lean_alloc_ctor(0, 2, 0);
} else {
 x_921 = x_916;
}
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set(x_921, 1, x_915);
return x_921;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_874);
lean_dec(x_21);
x_922 = lean_ctor_get(x_882, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_882, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_882)) {
 lean_ctor_release(x_882, 0);
 lean_ctor_release(x_882, 1);
 x_924 = x_882;
} else {
 lean_dec_ref(x_882);
 x_924 = lean_box(0);
}
if (lean_is_scalar(x_924)) {
 x_925 = lean_alloc_ctor(1, 2, 0);
} else {
 x_925 = x_924;
}
lean_ctor_set(x_925, 0, x_922);
lean_ctor_set(x_925, 1, x_923);
return x_925;
}
}
else
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
lean_dec(x_876);
lean_dec(x_874);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_926 = lean_ctor_get(x_878, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_878, 1);
lean_inc(x_927);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_928 = x_878;
} else {
 lean_dec_ref(x_878);
 x_928 = lean_box(0);
}
if (lean_is_scalar(x_928)) {
 x_929 = lean_alloc_ctor(1, 2, 0);
} else {
 x_929 = x_928;
}
lean_ctor_set(x_929, 0, x_926);
lean_ctor_set(x_929, 1, x_927);
x_930 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_879);
return x_930;
}
}
block_1032:
{
lean_object* x_934; 
x_934 = lean_ctor_get(x_932, 0);
lean_inc(x_934);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; 
x_935 = lean_ctor_get(x_934, 0);
lean_inc(x_935);
lean_dec(x_934);
if (lean_obj_tag(x_935) == 11)
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; 
lean_dec(x_935);
lean_dec(x_24);
x_936 = lean_ctor_get(x_932, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_932)) {
 lean_ctor_release(x_932, 0);
 lean_ctor_release(x_932, 1);
 x_937 = x_932;
} else {
 lean_dec_ref(x_932);
 x_937 = lean_box(0);
}
x_938 = lean_ctor_get(x_1, 0);
lean_inc(x_938);
x_939 = l_Lake_Env_leanGithash(x_938);
lean_dec(x_938);
x_940 = l_System_Platform_target;
lean_inc(x_876);
if (lean_is_scalar(x_877)) {
 x_941 = lean_alloc_ctor(0, 4, 0);
} else {
 x_941 = x_877;
}
lean_ctor_set(x_941, 0, x_940);
lean_ctor_set(x_941, 1, x_939);
lean_ctor_set(x_941, 2, x_30);
lean_ctor_set(x_941, 3, x_876);
x_942 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_941);
x_943 = lean_unsigned_to_nat(80u);
x_944 = l_Lean_Json_pretty(x_942, x_943);
x_945 = l_IO_FS_Handle_putStrLn(x_874, x_944, x_933);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; lean_object* x_947; 
x_946 = lean_ctor_get(x_945, 1);
lean_inc(x_946);
lean_dec(x_945);
x_947 = lean_io_prim_handle_truncate(x_874, x_946);
if (lean_obj_tag(x_947) == 0)
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; 
x_948 = lean_ctor_get(x_947, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_947, 1);
lean_inc(x_949);
lean_dec(x_947);
if (lean_is_scalar(x_937)) {
 x_950 = lean_alloc_ctor(0, 2, 0);
} else {
 x_950 = x_937;
}
lean_ctor_set(x_950, 0, x_948);
lean_ctor_set(x_950, 1, x_936);
x_878 = x_950;
x_879 = x_949;
goto block_931;
}
else
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; uint8_t x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_951 = lean_ctor_get(x_947, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_947, 1);
lean_inc(x_952);
lean_dec(x_947);
x_953 = lean_io_error_to_string(x_951);
x_954 = 3;
x_955 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_955, 0, x_953);
lean_ctor_set_uint8(x_955, sizeof(void*)*1, x_954);
x_956 = lean_array_get_size(x_936);
x_957 = lean_array_push(x_936, x_955);
if (lean_is_scalar(x_937)) {
 x_958 = lean_alloc_ctor(1, 2, 0);
} else {
 x_958 = x_937;
 lean_ctor_set_tag(x_958, 1);
}
lean_ctor_set(x_958, 0, x_956);
lean_ctor_set(x_958, 1, x_957);
x_878 = x_958;
x_879 = x_952;
goto block_931;
}
}
else
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; uint8_t x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
lean_dec(x_876);
lean_dec(x_874);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_959 = lean_ctor_get(x_945, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_945, 1);
lean_inc(x_960);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_961 = x_945;
} else {
 lean_dec_ref(x_945);
 x_961 = lean_box(0);
}
x_962 = lean_io_error_to_string(x_959);
x_963 = 3;
x_964 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_964, 0, x_962);
lean_ctor_set_uint8(x_964, sizeof(void*)*1, x_963);
x_965 = lean_array_get_size(x_936);
x_966 = lean_array_push(x_936, x_964);
if (lean_is_scalar(x_937)) {
 x_967 = lean_alloc_ctor(1, 2, 0);
} else {
 x_967 = x_937;
 lean_ctor_set_tag(x_967, 1);
}
lean_ctor_set(x_967, 0, x_965);
lean_ctor_set(x_967, 1, x_966);
if (lean_is_scalar(x_961)) {
 x_968 = lean_alloc_ctor(0, 2, 0);
} else {
 x_968 = x_961;
 lean_ctor_set_tag(x_968, 0);
}
lean_ctor_set(x_968, 0, x_967);
lean_ctor_set(x_968, 1, x_960);
return x_968;
}
}
else
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; uint8_t x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
lean_dec(x_877);
lean_dec(x_876);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_969 = lean_ctor_get(x_932, 1);
lean_inc(x_969);
if (lean_is_exclusive(x_932)) {
 lean_ctor_release(x_932, 0);
 lean_ctor_release(x_932, 1);
 x_970 = x_932;
} else {
 lean_dec_ref(x_932);
 x_970 = lean_box(0);
}
x_971 = lean_io_error_to_string(x_935);
x_972 = 3;
x_973 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_973, 0, x_971);
lean_ctor_set_uint8(x_973, sizeof(void*)*1, x_972);
x_974 = lean_array_get_size(x_969);
x_975 = lean_array_push(x_969, x_973);
x_976 = lean_io_prim_handle_unlock(x_874, x_933);
lean_dec(x_874);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; 
x_977 = lean_ctor_get(x_976, 1);
lean_inc(x_977);
lean_dec(x_976);
x_978 = lean_io_remove_file(x_24, x_977);
lean_dec(x_24);
if (lean_obj_tag(x_978) == 0)
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_979 = lean_ctor_get(x_978, 1);
lean_inc(x_979);
if (lean_is_exclusive(x_978)) {
 lean_ctor_release(x_978, 0);
 lean_ctor_release(x_978, 1);
 x_980 = x_978;
} else {
 lean_dec_ref(x_978);
 x_980 = lean_box(0);
}
if (lean_is_scalar(x_970)) {
 x_981 = lean_alloc_ctor(1, 2, 0);
} else {
 x_981 = x_970;
 lean_ctor_set_tag(x_981, 1);
}
lean_ctor_set(x_981, 0, x_974);
lean_ctor_set(x_981, 1, x_975);
if (lean_is_scalar(x_980)) {
 x_982 = lean_alloc_ctor(0, 2, 0);
} else {
 x_982 = x_980;
}
lean_ctor_set(x_982, 0, x_981);
lean_ctor_set(x_982, 1, x_979);
return x_982;
}
else
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_983 = lean_ctor_get(x_978, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_978, 1);
lean_inc(x_984);
if (lean_is_exclusive(x_978)) {
 lean_ctor_release(x_978, 0);
 lean_ctor_release(x_978, 1);
 x_985 = x_978;
} else {
 lean_dec_ref(x_978);
 x_985 = lean_box(0);
}
x_986 = lean_io_error_to_string(x_983);
x_987 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set_uint8(x_987, sizeof(void*)*1, x_972);
x_988 = lean_array_push(x_975, x_987);
if (lean_is_scalar(x_970)) {
 x_989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_989 = x_970;
 lean_ctor_set_tag(x_989, 1);
}
lean_ctor_set(x_989, 0, x_974);
lean_ctor_set(x_989, 1, x_988);
if (lean_is_scalar(x_985)) {
 x_990 = lean_alloc_ctor(0, 2, 0);
} else {
 x_990 = x_985;
 lean_ctor_set_tag(x_990, 0);
}
lean_ctor_set(x_990, 0, x_989);
lean_ctor_set(x_990, 1, x_984);
return x_990;
}
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
lean_dec(x_24);
x_991 = lean_ctor_get(x_976, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_976, 1);
lean_inc(x_992);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_993 = x_976;
} else {
 lean_dec_ref(x_976);
 x_993 = lean_box(0);
}
x_994 = lean_io_error_to_string(x_991);
x_995 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_995, 0, x_994);
lean_ctor_set_uint8(x_995, sizeof(void*)*1, x_972);
x_996 = lean_array_push(x_975, x_995);
if (lean_is_scalar(x_970)) {
 x_997 = lean_alloc_ctor(1, 2, 0);
} else {
 x_997 = x_970;
 lean_ctor_set_tag(x_997, 1);
}
lean_ctor_set(x_997, 0, x_974);
lean_ctor_set(x_997, 1, x_996);
if (lean_is_scalar(x_993)) {
 x_998 = lean_alloc_ctor(0, 2, 0);
} else {
 x_998 = x_993;
 lean_ctor_set_tag(x_998, 0);
}
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_992);
return x_998;
}
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
lean_dec(x_934);
lean_dec(x_24);
x_999 = lean_ctor_get(x_932, 1);
lean_inc(x_999);
if (lean_is_exclusive(x_932)) {
 lean_ctor_release(x_932, 0);
 lean_ctor_release(x_932, 1);
 x_1000 = x_932;
} else {
 lean_dec_ref(x_932);
 x_1000 = lean_box(0);
}
x_1001 = lean_ctor_get(x_1, 0);
lean_inc(x_1001);
x_1002 = l_Lake_Env_leanGithash(x_1001);
lean_dec(x_1001);
x_1003 = l_System_Platform_target;
lean_inc(x_876);
if (lean_is_scalar(x_877)) {
 x_1004 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1004 = x_877;
}
lean_ctor_set(x_1004, 0, x_1003);
lean_ctor_set(x_1004, 1, x_1002);
lean_ctor_set(x_1004, 2, x_30);
lean_ctor_set(x_1004, 3, x_876);
x_1005 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_1004);
x_1006 = lean_unsigned_to_nat(80u);
x_1007 = l_Lean_Json_pretty(x_1005, x_1006);
x_1008 = l_IO_FS_Handle_putStrLn(x_874, x_1007, x_933);
if (lean_obj_tag(x_1008) == 0)
{
lean_object* x_1009; lean_object* x_1010; 
x_1009 = lean_ctor_get(x_1008, 1);
lean_inc(x_1009);
lean_dec(x_1008);
x_1010 = lean_io_prim_handle_truncate(x_874, x_1009);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_1010, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_1010, 1);
lean_inc(x_1012);
lean_dec(x_1010);
if (lean_is_scalar(x_1000)) {
 x_1013 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1013 = x_1000;
}
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_999);
x_878 = x_1013;
x_879 = x_1012;
goto block_931;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; uint8_t x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1014 = lean_ctor_get(x_1010, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_1010, 1);
lean_inc(x_1015);
lean_dec(x_1010);
x_1016 = lean_io_error_to_string(x_1014);
x_1017 = 3;
x_1018 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1018, 0, x_1016);
lean_ctor_set_uint8(x_1018, sizeof(void*)*1, x_1017);
x_1019 = lean_array_get_size(x_999);
x_1020 = lean_array_push(x_999, x_1018);
if (lean_is_scalar(x_1000)) {
 x_1021 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1021 = x_1000;
 lean_ctor_set_tag(x_1021, 1);
}
lean_ctor_set(x_1021, 0, x_1019);
lean_ctor_set(x_1021, 1, x_1020);
x_878 = x_1021;
x_879 = x_1015;
goto block_931;
}
}
else
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; uint8_t x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; 
lean_dec(x_876);
lean_dec(x_874);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1022 = lean_ctor_get(x_1008, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1008, 1);
lean_inc(x_1023);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 lean_ctor_release(x_1008, 1);
 x_1024 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1024 = lean_box(0);
}
x_1025 = lean_io_error_to_string(x_1022);
x_1026 = 3;
x_1027 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1027, 0, x_1025);
lean_ctor_set_uint8(x_1027, sizeof(void*)*1, x_1026);
x_1028 = lean_array_get_size(x_999);
x_1029 = lean_array_push(x_999, x_1027);
if (lean_is_scalar(x_1000)) {
 x_1030 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1030 = x_1000;
 lean_ctor_set_tag(x_1030, 1);
}
lean_ctor_set(x_1030, 0, x_1028);
lean_ctor_set(x_1030, 1, x_1029);
if (lean_is_scalar(x_1024)) {
 x_1031 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1031 = x_1024;
 lean_ctor_set_tag(x_1031, 0);
}
lean_ctor_set(x_1031, 0, x_1030);
lean_ctor_set(x_1031, 1, x_1023);
return x_1031;
}
}
}
}
}
else
{
uint8_t x_1042; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1042 = !lean_is_exclusive(x_553);
if (x_1042 == 0)
{
lean_object* x_1043; 
x_1043 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1043, 0, x_553);
lean_ctor_set(x_1043, 1, x_554);
return x_1043;
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1044 = lean_ctor_get(x_553, 0);
x_1045 = lean_ctor_get(x_553, 1);
lean_inc(x_1045);
lean_inc(x_1044);
lean_dec(x_553);
x_1046 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1046, 0, x_1044);
lean_ctor_set(x_1046, 1, x_1045);
x_1047 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_554);
return x_1047;
}
}
}
block_1100:
{
lean_object* x_1053; lean_object* x_1054; uint8_t x_1062; lean_object* x_1063; 
lean_dec(x_1052);
x_1062 = 1;
x_1063 = lean_io_prim_handle_mk(x_27, x_1062, x_1051);
lean_dec(x_27);
if (lean_obj_tag(x_1063) == 0)
{
lean_object* x_1064; lean_object* x_1065; uint8_t x_1066; lean_object* x_1067; 
x_1064 = lean_ctor_get(x_1063, 0);
lean_inc(x_1064);
x_1065 = lean_ctor_get(x_1063, 1);
lean_inc(x_1065);
lean_dec(x_1063);
x_1066 = 1;
x_1067 = lean_io_prim_handle_try_lock(x_1064, x_1066, x_1065);
if (lean_obj_tag(x_1067) == 0)
{
lean_object* x_1068; uint8_t x_1069; 
x_1068 = lean_ctor_get(x_1067, 0);
lean_inc(x_1068);
x_1069 = lean_unbox(x_1068);
lean_dec(x_1068);
if (x_1069 == 0)
{
lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_1064);
lean_dec(x_531);
x_1070 = lean_ctor_get(x_1067, 1);
lean_inc(x_1070);
lean_dec(x_1067);
x_1071 = lean_io_prim_handle_unlock(x_529, x_1070);
lean_dec(x_529);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1072; lean_object* x_1073; 
x_1072 = lean_ctor_get(x_1071, 1);
lean_inc(x_1072);
lean_dec(x_1071);
x_1073 = l_Lake_importConfigFile___closed__12;
x_1053 = x_1073;
x_1054 = x_1072;
goto block_1061;
}
else
{
lean_object* x_1074; lean_object* x_1075; 
x_1074 = lean_ctor_get(x_1071, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1071, 1);
lean_inc(x_1075);
lean_dec(x_1071);
x_1053 = x_1074;
x_1054 = x_1075;
goto block_1061;
}
}
else
{
lean_object* x_1076; lean_object* x_1077; 
x_1076 = lean_ctor_get(x_1067, 1);
lean_inc(x_1076);
lean_dec(x_1067);
x_1077 = lean_io_prim_handle_unlock(x_529, x_1076);
lean_dec(x_529);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; uint8_t x_1079; lean_object* x_1080; 
x_1078 = lean_ctor_get(x_1077, 1);
lean_inc(x_1078);
lean_dec(x_1077);
x_1079 = 3;
x_1080 = lean_io_prim_handle_mk(x_24, x_1079, x_1078);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1080, 1);
lean_inc(x_1082);
lean_dec(x_1080);
x_1083 = lean_io_prim_handle_lock(x_1081, x_1066, x_1082);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; 
x_1084 = lean_ctor_get(x_1083, 1);
lean_inc(x_1084);
lean_dec(x_1083);
x_1085 = lean_io_prim_handle_unlock(x_1064, x_1084);
lean_dec(x_1064);
if (lean_obj_tag(x_1085) == 0)
{
lean_object* x_1086; lean_object* x_1087; 
lean_dec(x_536);
x_1086 = lean_ctor_get(x_1085, 1);
lean_inc(x_1086);
lean_dec(x_1085);
if (lean_is_scalar(x_531)) {
 x_1087 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1087 = x_531;
}
lean_ctor_set(x_1087, 0, x_1081);
lean_ctor_set(x_1087, 1, x_535);
x_553 = x_1087;
x_554 = x_1086;
goto block_1048;
}
else
{
lean_object* x_1088; lean_object* x_1089; 
lean_dec(x_1081);
lean_dec(x_531);
x_1088 = lean_ctor_get(x_1085, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1085, 1);
lean_inc(x_1089);
lean_dec(x_1085);
x_1053 = x_1088;
x_1054 = x_1089;
goto block_1061;
}
}
else
{
lean_object* x_1090; lean_object* x_1091; 
lean_dec(x_1081);
lean_dec(x_1064);
lean_dec(x_531);
x_1090 = lean_ctor_get(x_1083, 0);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1083, 1);
lean_inc(x_1091);
lean_dec(x_1083);
x_1053 = x_1090;
x_1054 = x_1091;
goto block_1061;
}
}
else
{
lean_object* x_1092; lean_object* x_1093; 
lean_dec(x_1064);
lean_dec(x_531);
x_1092 = lean_ctor_get(x_1080, 0);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1080, 1);
lean_inc(x_1093);
lean_dec(x_1080);
x_1053 = x_1092;
x_1054 = x_1093;
goto block_1061;
}
}
else
{
lean_object* x_1094; lean_object* x_1095; 
lean_dec(x_1064);
lean_dec(x_531);
x_1094 = lean_ctor_get(x_1077, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1077, 1);
lean_inc(x_1095);
lean_dec(x_1077);
x_1053 = x_1094;
x_1054 = x_1095;
goto block_1061;
}
}
}
else
{
lean_object* x_1096; lean_object* x_1097; 
lean_dec(x_1064);
lean_dec(x_531);
lean_dec(x_529);
x_1096 = lean_ctor_get(x_1067, 0);
lean_inc(x_1096);
x_1097 = lean_ctor_get(x_1067, 1);
lean_inc(x_1097);
lean_dec(x_1067);
x_1053 = x_1096;
x_1054 = x_1097;
goto block_1061;
}
}
else
{
lean_object* x_1098; lean_object* x_1099; 
lean_dec(x_531);
lean_dec(x_529);
x_1098 = lean_ctor_get(x_1063, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1063, 1);
lean_inc(x_1099);
lean_dec(x_1063);
x_1053 = x_1098;
x_1054 = x_1099;
goto block_1061;
}
block_1061:
{
lean_object* x_1055; uint8_t x_1056; lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1055 = lean_io_error_to_string(x_1053);
x_1056 = 3;
x_1057 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1057, 0, x_1055);
lean_ctor_set_uint8(x_1057, sizeof(void*)*1, x_1056);
x_1058 = lean_array_get_size(x_535);
x_1059 = lean_array_push(x_535, x_1057);
if (lean_is_scalar(x_536)) {
 x_1060 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1060 = x_536;
 lean_ctor_set_tag(x_1060, 1);
}
lean_ctor_set(x_1060, 0, x_1058);
lean_ctor_set(x_1060, 1, x_1059);
x_553 = x_1060;
x_554 = x_1054;
goto block_1048;
}
}
}
}
}
else
{
uint8_t x_1162; 
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1162 = !lean_is_exclusive(x_532);
if (x_1162 == 0)
{
lean_object* x_1163; 
x_1163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1163, 0, x_532);
lean_ctor_set(x_1163, 1, x_533);
return x_1163;
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1164 = lean_ctor_get(x_532, 0);
x_1165 = lean_ctor_get(x_532, 1);
lean_inc(x_1165);
lean_inc(x_1164);
lean_dec(x_532);
x_1166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1166, 0, x_1164);
lean_ctor_set(x_1166, 1, x_1165);
x_1167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1167, 0, x_1166);
lean_ctor_set(x_1167, 1, x_533);
return x_1167;
}
}
}
}
else
{
uint8_t x_1262; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1262 = !lean_is_exclusive(x_527);
if (x_1262 == 0)
{
lean_object* x_1263; 
x_1263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1263, 0, x_527);
lean_ctor_set(x_1263, 1, x_528);
return x_1263;
}
else
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1264 = lean_ctor_get(x_527, 0);
x_1265 = lean_ctor_get(x_527, 1);
lean_inc(x_1265);
lean_inc(x_1264);
lean_dec(x_527);
x_1266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1266, 0, x_1264);
lean_ctor_set(x_1266, 1, x_1265);
x_1267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1267, 0, x_1266);
lean_ctor_set(x_1267, 1, x_528);
return x_1267;
}
}
}
block_2018:
{
lean_object* x_1271; 
x_1271 = lean_ctor_get(x_1269, 0);
lean_inc(x_1271);
if (lean_obj_tag(x_1271) == 0)
{
lean_object* x_1272; 
x_1272 = lean_ctor_get(x_1271, 0);
lean_inc(x_1272);
lean_dec(x_1271);
if (lean_obj_tag(x_1272) == 0)
{
uint8_t x_1273; 
lean_dec(x_1272);
x_1273 = !lean_is_exclusive(x_1269);
if (x_1273 == 0)
{
lean_object* x_1274; lean_object* x_1275; uint8_t x_1276; lean_object* x_1277; 
x_1274 = lean_ctor_get(x_1269, 1);
x_1275 = lean_ctor_get(x_1269, 0);
lean_dec(x_1275);
x_1276 = 0;
x_1277 = lean_io_prim_handle_mk(x_24, x_1276, x_1270);
if (lean_obj_tag(x_1277) == 0)
{
lean_object* x_1278; lean_object* x_1279; 
x_1278 = lean_ctor_get(x_1277, 0);
lean_inc(x_1278);
x_1279 = lean_ctor_get(x_1277, 1);
lean_inc(x_1279);
lean_dec(x_1277);
lean_ctor_set(x_1269, 0, x_1278);
x_527 = x_1269;
x_528 = x_1279;
goto block_1268;
}
else
{
lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; uint8_t x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; 
x_1280 = lean_ctor_get(x_1277, 0);
lean_inc(x_1280);
x_1281 = lean_ctor_get(x_1277, 1);
lean_inc(x_1281);
lean_dec(x_1277);
x_1282 = lean_io_error_to_string(x_1280);
x_1283 = 3;
x_1284 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1284, 0, x_1282);
lean_ctor_set_uint8(x_1284, sizeof(void*)*1, x_1283);
x_1285 = lean_array_get_size(x_1274);
x_1286 = lean_array_push(x_1274, x_1284);
lean_ctor_set_tag(x_1269, 1);
lean_ctor_set(x_1269, 1, x_1286);
lean_ctor_set(x_1269, 0, x_1285);
x_527 = x_1269;
x_528 = x_1281;
goto block_1268;
}
}
else
{
lean_object* x_1287; uint8_t x_1288; lean_object* x_1289; 
x_1287 = lean_ctor_get(x_1269, 1);
lean_inc(x_1287);
lean_dec(x_1269);
x_1288 = 0;
x_1289 = lean_io_prim_handle_mk(x_24, x_1288, x_1270);
if (lean_obj_tag(x_1289) == 0)
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
x_1290 = lean_ctor_get(x_1289, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1289, 1);
lean_inc(x_1291);
lean_dec(x_1289);
x_1292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1292, 0, x_1290);
lean_ctor_set(x_1292, 1, x_1287);
x_527 = x_1292;
x_528 = x_1291;
goto block_1268;
}
else
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; uint8_t x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
x_1293 = lean_ctor_get(x_1289, 0);
lean_inc(x_1293);
x_1294 = lean_ctor_get(x_1289, 1);
lean_inc(x_1294);
lean_dec(x_1289);
x_1295 = lean_io_error_to_string(x_1293);
x_1296 = 3;
x_1297 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1297, 0, x_1295);
lean_ctor_set_uint8(x_1297, sizeof(void*)*1, x_1296);
x_1298 = lean_array_get_size(x_1287);
x_1299 = lean_array_push(x_1287, x_1297);
x_1300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1300, 0, x_1298);
lean_ctor_set(x_1300, 1, x_1299);
x_527 = x_1300;
x_528 = x_1294;
goto block_1268;
}
}
}
else
{
uint8_t x_1301; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1301 = !lean_is_exclusive(x_1269);
if (x_1301 == 0)
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; uint8_t x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
x_1302 = lean_ctor_get(x_1269, 1);
x_1303 = lean_ctor_get(x_1269, 0);
lean_dec(x_1303);
x_1304 = lean_io_error_to_string(x_1272);
x_1305 = 3;
x_1306 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1306, 0, x_1304);
lean_ctor_set_uint8(x_1306, sizeof(void*)*1, x_1305);
x_1307 = lean_array_get_size(x_1302);
x_1308 = lean_array_push(x_1302, x_1306);
lean_ctor_set_tag(x_1269, 1);
lean_ctor_set(x_1269, 1, x_1308);
lean_ctor_set(x_1269, 0, x_1307);
x_1309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1309, 0, x_1269);
lean_ctor_set(x_1309, 1, x_1270);
return x_1309;
}
else
{
lean_object* x_1310; lean_object* x_1311; uint8_t x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; lean_object* x_1317; 
x_1310 = lean_ctor_get(x_1269, 1);
lean_inc(x_1310);
lean_dec(x_1269);
x_1311 = lean_io_error_to_string(x_1272);
x_1312 = 3;
x_1313 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1313, 0, x_1311);
lean_ctor_set_uint8(x_1313, sizeof(void*)*1, x_1312);
x_1314 = lean_array_get_size(x_1310);
x_1315 = lean_array_push(x_1310, x_1313);
x_1316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1316, 0, x_1314);
lean_ctor_set(x_1316, 1, x_1315);
x_1317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1317, 0, x_1316);
lean_ctor_set(x_1317, 1, x_1270);
return x_1317;
}
}
}
else
{
uint8_t x_1318; 
lean_dec(x_32);
lean_dec(x_27);
lean_dec(x_16);
x_1318 = !lean_is_exclusive(x_1269);
if (x_1318 == 0)
{
lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; uint8_t x_1816; lean_object* x_1817; 
x_1319 = lean_ctor_get(x_1269, 1);
x_1320 = lean_ctor_get(x_1269, 0);
lean_dec(x_1320);
x_1321 = lean_ctor_get(x_1271, 0);
lean_inc(x_1321);
if (lean_is_exclusive(x_1271)) {
 lean_ctor_release(x_1271, 0);
 x_1322 = x_1271;
} else {
 lean_dec_ref(x_1271);
 x_1322 = lean_box(0);
}
x_1816 = 1;
x_1817 = lean_io_prim_handle_lock(x_1321, x_1816, x_1270);
if (lean_obj_tag(x_1817) == 0)
{
lean_object* x_1818; lean_object* x_1819; 
x_1818 = lean_ctor_get(x_1817, 0);
lean_inc(x_1818);
x_1819 = lean_ctor_get(x_1817, 1);
lean_inc(x_1819);
lean_dec(x_1817);
lean_ctor_set(x_1269, 0, x_1818);
x_1323 = x_1269;
x_1324 = x_1819;
goto block_1815;
}
else
{
lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; uint8_t x_1823; lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; 
x_1820 = lean_ctor_get(x_1817, 0);
lean_inc(x_1820);
x_1821 = lean_ctor_get(x_1817, 1);
lean_inc(x_1821);
lean_dec(x_1817);
x_1822 = lean_io_error_to_string(x_1820);
x_1823 = 3;
x_1824 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1824, 0, x_1822);
lean_ctor_set_uint8(x_1824, sizeof(void*)*1, x_1823);
x_1825 = lean_array_get_size(x_1319);
x_1826 = lean_array_push(x_1319, x_1824);
lean_ctor_set_tag(x_1269, 1);
lean_ctor_set(x_1269, 1, x_1826);
lean_ctor_set(x_1269, 0, x_1825);
x_1323 = x_1269;
x_1324 = x_1821;
goto block_1815;
}
block_1815:
{
if (lean_obj_tag(x_1323) == 0)
{
uint8_t x_1325; 
x_1325 = !lean_is_exclusive(x_1323);
if (x_1325 == 0)
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1427; lean_object* x_1428; lean_object* x_1636; 
x_1326 = lean_ctor_get(x_1323, 0);
lean_dec(x_1326);
x_1327 = lean_ctor_get(x_1, 6);
lean_inc(x_1327);
x_1636 = lean_io_remove_file(x_21, x_1324);
if (lean_obj_tag(x_1636) == 0)
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; 
x_1637 = lean_ctor_get(x_1636, 0);
lean_inc(x_1637);
x_1638 = lean_ctor_get(x_1636, 1);
lean_inc(x_1638);
lean_dec(x_1636);
if (lean_is_scalar(x_1322)) {
 x_1639 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1639 = x_1322;
}
lean_ctor_set(x_1639, 0, x_1637);
lean_ctor_set(x_1323, 0, x_1639);
x_1427 = x_1323;
x_1428 = x_1638;
goto block_1635;
}
else
{
lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; 
x_1640 = lean_ctor_get(x_1636, 0);
lean_inc(x_1640);
x_1641 = lean_ctor_get(x_1636, 1);
lean_inc(x_1641);
lean_dec(x_1636);
if (lean_is_scalar(x_1322)) {
 x_1642 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1642 = x_1322;
 lean_ctor_set_tag(x_1642, 0);
}
lean_ctor_set(x_1642, 0, x_1640);
lean_ctor_set(x_1323, 0, x_1642);
x_1427 = x_1323;
x_1428 = x_1641;
goto block_1635;
}
block_1426:
{
if (lean_obj_tag(x_1328) == 0)
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; 
x_1330 = lean_ctor_get(x_1328, 1);
lean_inc(x_1330);
lean_dec(x_1328);
x_1331 = lean_ctor_get(x_1, 7);
lean_inc(x_1331);
lean_dec(x_1);
x_1332 = l_Lake_elabConfigFile(x_6, x_1327, x_1331, x_8, x_1330, x_1329);
if (lean_obj_tag(x_1332) == 0)
{
lean_object* x_1333; 
x_1333 = lean_ctor_get(x_1332, 0);
lean_inc(x_1333);
if (lean_obj_tag(x_1333) == 0)
{
lean_object* x_1334; uint8_t x_1335; 
x_1334 = lean_ctor_get(x_1332, 1);
lean_inc(x_1334);
lean_dec(x_1332);
x_1335 = !lean_is_exclusive(x_1333);
if (x_1335 == 0)
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
x_1336 = lean_ctor_get(x_1333, 0);
x_1337 = lean_ctor_get(x_1333, 1);
lean_inc(x_1336);
x_1338 = lean_write_module(x_1336, x_21, x_1334);
if (lean_obj_tag(x_1338) == 0)
{
lean_object* x_1339; lean_object* x_1340; 
x_1339 = lean_ctor_get(x_1338, 1);
lean_inc(x_1339);
lean_dec(x_1338);
x_1340 = lean_io_prim_handle_unlock(x_1321, x_1339);
lean_dec(x_1321);
if (lean_obj_tag(x_1340) == 0)
{
uint8_t x_1341; 
x_1341 = !lean_is_exclusive(x_1340);
if (x_1341 == 0)
{
lean_object* x_1342; 
x_1342 = lean_ctor_get(x_1340, 0);
lean_dec(x_1342);
lean_ctor_set(x_1340, 0, x_1333);
return x_1340;
}
else
{
lean_object* x_1343; lean_object* x_1344; 
x_1343 = lean_ctor_get(x_1340, 1);
lean_inc(x_1343);
lean_dec(x_1340);
x_1344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1344, 0, x_1333);
lean_ctor_set(x_1344, 1, x_1343);
return x_1344;
}
}
else
{
uint8_t x_1345; 
lean_dec(x_1336);
x_1345 = !lean_is_exclusive(x_1340);
if (x_1345 == 0)
{
lean_object* x_1346; lean_object* x_1347; uint8_t x_1348; lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; 
x_1346 = lean_ctor_get(x_1340, 0);
x_1347 = lean_io_error_to_string(x_1346);
x_1348 = 3;
x_1349 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1349, 0, x_1347);
lean_ctor_set_uint8(x_1349, sizeof(void*)*1, x_1348);
x_1350 = lean_array_get_size(x_1337);
x_1351 = lean_array_push(x_1337, x_1349);
lean_ctor_set_tag(x_1333, 1);
lean_ctor_set(x_1333, 1, x_1351);
lean_ctor_set(x_1333, 0, x_1350);
lean_ctor_set_tag(x_1340, 0);
lean_ctor_set(x_1340, 0, x_1333);
return x_1340;
}
else
{
lean_object* x_1352; lean_object* x_1353; lean_object* x_1354; uint8_t x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; 
x_1352 = lean_ctor_get(x_1340, 0);
x_1353 = lean_ctor_get(x_1340, 1);
lean_inc(x_1353);
lean_inc(x_1352);
lean_dec(x_1340);
x_1354 = lean_io_error_to_string(x_1352);
x_1355 = 3;
x_1356 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1356, 0, x_1354);
lean_ctor_set_uint8(x_1356, sizeof(void*)*1, x_1355);
x_1357 = lean_array_get_size(x_1337);
x_1358 = lean_array_push(x_1337, x_1356);
lean_ctor_set_tag(x_1333, 1);
lean_ctor_set(x_1333, 1, x_1358);
lean_ctor_set(x_1333, 0, x_1357);
x_1359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1359, 0, x_1333);
lean_ctor_set(x_1359, 1, x_1353);
return x_1359;
}
}
}
else
{
uint8_t x_1360; 
lean_dec(x_1336);
lean_dec(x_1321);
x_1360 = !lean_is_exclusive(x_1338);
if (x_1360 == 0)
{
lean_object* x_1361; lean_object* x_1362; uint8_t x_1363; lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; 
x_1361 = lean_ctor_get(x_1338, 0);
x_1362 = lean_io_error_to_string(x_1361);
x_1363 = 3;
x_1364 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1364, 0, x_1362);
lean_ctor_set_uint8(x_1364, sizeof(void*)*1, x_1363);
x_1365 = lean_array_get_size(x_1337);
x_1366 = lean_array_push(x_1337, x_1364);
lean_ctor_set_tag(x_1333, 1);
lean_ctor_set(x_1333, 1, x_1366);
lean_ctor_set(x_1333, 0, x_1365);
lean_ctor_set_tag(x_1338, 0);
lean_ctor_set(x_1338, 0, x_1333);
return x_1338;
}
else
{
lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; uint8_t x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
x_1367 = lean_ctor_get(x_1338, 0);
x_1368 = lean_ctor_get(x_1338, 1);
lean_inc(x_1368);
lean_inc(x_1367);
lean_dec(x_1338);
x_1369 = lean_io_error_to_string(x_1367);
x_1370 = 3;
x_1371 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1371, 0, x_1369);
lean_ctor_set_uint8(x_1371, sizeof(void*)*1, x_1370);
x_1372 = lean_array_get_size(x_1337);
x_1373 = lean_array_push(x_1337, x_1371);
lean_ctor_set_tag(x_1333, 1);
lean_ctor_set(x_1333, 1, x_1373);
lean_ctor_set(x_1333, 0, x_1372);
x_1374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1374, 0, x_1333);
lean_ctor_set(x_1374, 1, x_1368);
return x_1374;
}
}
}
else
{
lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
x_1375 = lean_ctor_get(x_1333, 0);
x_1376 = lean_ctor_get(x_1333, 1);
lean_inc(x_1376);
lean_inc(x_1375);
lean_dec(x_1333);
lean_inc(x_1375);
x_1377 = lean_write_module(x_1375, x_21, x_1334);
if (lean_obj_tag(x_1377) == 0)
{
lean_object* x_1378; lean_object* x_1379; 
x_1378 = lean_ctor_get(x_1377, 1);
lean_inc(x_1378);
lean_dec(x_1377);
x_1379 = lean_io_prim_handle_unlock(x_1321, x_1378);
lean_dec(x_1321);
if (lean_obj_tag(x_1379) == 0)
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
x_1380 = lean_ctor_get(x_1379, 1);
lean_inc(x_1380);
if (lean_is_exclusive(x_1379)) {
 lean_ctor_release(x_1379, 0);
 lean_ctor_release(x_1379, 1);
 x_1381 = x_1379;
} else {
 lean_dec_ref(x_1379);
 x_1381 = lean_box(0);
}
x_1382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1382, 0, x_1375);
lean_ctor_set(x_1382, 1, x_1376);
if (lean_is_scalar(x_1381)) {
 x_1383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1383 = x_1381;
}
lean_ctor_set(x_1383, 0, x_1382);
lean_ctor_set(x_1383, 1, x_1380);
return x_1383;
}
else
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; uint8_t x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
lean_dec(x_1375);
x_1384 = lean_ctor_get(x_1379, 0);
lean_inc(x_1384);
x_1385 = lean_ctor_get(x_1379, 1);
lean_inc(x_1385);
if (lean_is_exclusive(x_1379)) {
 lean_ctor_release(x_1379, 0);
 lean_ctor_release(x_1379, 1);
 x_1386 = x_1379;
} else {
 lean_dec_ref(x_1379);
 x_1386 = lean_box(0);
}
x_1387 = lean_io_error_to_string(x_1384);
x_1388 = 3;
x_1389 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1389, 0, x_1387);
lean_ctor_set_uint8(x_1389, sizeof(void*)*1, x_1388);
x_1390 = lean_array_get_size(x_1376);
x_1391 = lean_array_push(x_1376, x_1389);
x_1392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1392, 0, x_1390);
lean_ctor_set(x_1392, 1, x_1391);
if (lean_is_scalar(x_1386)) {
 x_1393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1393 = x_1386;
 lean_ctor_set_tag(x_1393, 0);
}
lean_ctor_set(x_1393, 0, x_1392);
lean_ctor_set(x_1393, 1, x_1385);
return x_1393;
}
}
else
{
lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; uint8_t x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
lean_dec(x_1375);
lean_dec(x_1321);
x_1394 = lean_ctor_get(x_1377, 0);
lean_inc(x_1394);
x_1395 = lean_ctor_get(x_1377, 1);
lean_inc(x_1395);
if (lean_is_exclusive(x_1377)) {
 lean_ctor_release(x_1377, 0);
 lean_ctor_release(x_1377, 1);
 x_1396 = x_1377;
} else {
 lean_dec_ref(x_1377);
 x_1396 = lean_box(0);
}
x_1397 = lean_io_error_to_string(x_1394);
x_1398 = 3;
x_1399 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1399, 0, x_1397);
lean_ctor_set_uint8(x_1399, sizeof(void*)*1, x_1398);
x_1400 = lean_array_get_size(x_1376);
x_1401 = lean_array_push(x_1376, x_1399);
x_1402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1402, 0, x_1400);
lean_ctor_set(x_1402, 1, x_1401);
if (lean_is_scalar(x_1396)) {
 x_1403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1403 = x_1396;
 lean_ctor_set_tag(x_1403, 0);
}
lean_ctor_set(x_1403, 0, x_1402);
lean_ctor_set(x_1403, 1, x_1395);
return x_1403;
}
}
}
else
{
uint8_t x_1404; 
lean_dec(x_1321);
lean_dec(x_21);
x_1404 = !lean_is_exclusive(x_1332);
if (x_1404 == 0)
{
lean_object* x_1405; uint8_t x_1406; 
x_1405 = lean_ctor_get(x_1332, 0);
lean_dec(x_1405);
x_1406 = !lean_is_exclusive(x_1333);
if (x_1406 == 0)
{
return x_1332;
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; 
x_1407 = lean_ctor_get(x_1333, 0);
x_1408 = lean_ctor_get(x_1333, 1);
lean_inc(x_1408);
lean_inc(x_1407);
lean_dec(x_1333);
x_1409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1409, 0, x_1407);
lean_ctor_set(x_1409, 1, x_1408);
lean_ctor_set(x_1332, 0, x_1409);
return x_1332;
}
}
else
{
lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; lean_object* x_1415; 
x_1410 = lean_ctor_get(x_1332, 1);
lean_inc(x_1410);
lean_dec(x_1332);
x_1411 = lean_ctor_get(x_1333, 0);
lean_inc(x_1411);
x_1412 = lean_ctor_get(x_1333, 1);
lean_inc(x_1412);
if (lean_is_exclusive(x_1333)) {
 lean_ctor_release(x_1333, 0);
 lean_ctor_release(x_1333, 1);
 x_1413 = x_1333;
} else {
 lean_dec_ref(x_1333);
 x_1413 = lean_box(0);
}
if (lean_is_scalar(x_1413)) {
 x_1414 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1414 = x_1413;
}
lean_ctor_set(x_1414, 0, x_1411);
lean_ctor_set(x_1414, 1, x_1412);
x_1415 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1415, 0, x_1414);
lean_ctor_set(x_1415, 1, x_1410);
return x_1415;
}
}
}
else
{
uint8_t x_1416; 
lean_dec(x_1321);
lean_dec(x_21);
x_1416 = !lean_is_exclusive(x_1332);
if (x_1416 == 0)
{
return x_1332;
}
else
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; 
x_1417 = lean_ctor_get(x_1332, 0);
x_1418 = lean_ctor_get(x_1332, 1);
lean_inc(x_1418);
lean_inc(x_1417);
lean_dec(x_1332);
x_1419 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1419, 0, x_1417);
lean_ctor_set(x_1419, 1, x_1418);
return x_1419;
}
}
}
else
{
uint8_t x_1420; 
lean_dec(x_1327);
lean_dec(x_1321);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1420 = !lean_is_exclusive(x_1328);
if (x_1420 == 0)
{
lean_object* x_1421; 
x_1421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1421, 0, x_1328);
lean_ctor_set(x_1421, 1, x_1329);
return x_1421;
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; 
x_1422 = lean_ctor_get(x_1328, 0);
x_1423 = lean_ctor_get(x_1328, 1);
lean_inc(x_1423);
lean_inc(x_1422);
lean_dec(x_1328);
x_1424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1424, 0, x_1422);
lean_ctor_set(x_1424, 1, x_1423);
x_1425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1425, 0, x_1424);
lean_ctor_set(x_1425, 1, x_1329);
return x_1425;
}
}
}
block_1635:
{
lean_object* x_1429; 
x_1429 = lean_ctor_get(x_1427, 0);
lean_inc(x_1429);
if (lean_obj_tag(x_1429) == 0)
{
lean_object* x_1430; 
x_1430 = lean_ctor_get(x_1429, 0);
lean_inc(x_1430);
lean_dec(x_1429);
if (lean_obj_tag(x_1430) == 11)
{
uint8_t x_1431; 
lean_dec(x_1430);
lean_dec(x_24);
x_1431 = !lean_is_exclusive(x_1427);
if (x_1431 == 0)
{
lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; 
x_1432 = lean_ctor_get(x_1427, 1);
x_1433 = lean_ctor_get(x_1427, 0);
lean_dec(x_1433);
x_1434 = lean_ctor_get(x_1, 0);
lean_inc(x_1434);
x_1435 = l_Lake_Env_leanGithash(x_1434);
lean_dec(x_1434);
x_1436 = l_System_Platform_target;
lean_inc(x_1327);
x_1437 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1437, 0, x_1436);
lean_ctor_set(x_1437, 1, x_1435);
lean_ctor_set(x_1437, 2, x_30);
lean_ctor_set(x_1437, 3, x_1327);
x_1438 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_1437);
x_1439 = lean_unsigned_to_nat(80u);
x_1440 = l_Lean_Json_pretty(x_1438, x_1439);
x_1441 = l_IO_FS_Handle_putStrLn(x_1321, x_1440, x_1428);
if (lean_obj_tag(x_1441) == 0)
{
lean_object* x_1442; lean_object* x_1443; 
x_1442 = lean_ctor_get(x_1441, 1);
lean_inc(x_1442);
lean_dec(x_1441);
x_1443 = lean_io_prim_handle_truncate(x_1321, x_1442);
if (lean_obj_tag(x_1443) == 0)
{
lean_object* x_1444; lean_object* x_1445; 
x_1444 = lean_ctor_get(x_1443, 0);
lean_inc(x_1444);
x_1445 = lean_ctor_get(x_1443, 1);
lean_inc(x_1445);
lean_dec(x_1443);
lean_ctor_set(x_1427, 0, x_1444);
x_1328 = x_1427;
x_1329 = x_1445;
goto block_1426;
}
else
{
lean_object* x_1446; lean_object* x_1447; lean_object* x_1448; uint8_t x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; 
x_1446 = lean_ctor_get(x_1443, 0);
lean_inc(x_1446);
x_1447 = lean_ctor_get(x_1443, 1);
lean_inc(x_1447);
lean_dec(x_1443);
x_1448 = lean_io_error_to_string(x_1446);
x_1449 = 3;
x_1450 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1450, 0, x_1448);
lean_ctor_set_uint8(x_1450, sizeof(void*)*1, x_1449);
x_1451 = lean_array_get_size(x_1432);
x_1452 = lean_array_push(x_1432, x_1450);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1452);
lean_ctor_set(x_1427, 0, x_1451);
x_1328 = x_1427;
x_1329 = x_1447;
goto block_1426;
}
}
else
{
uint8_t x_1453; 
lean_dec(x_1327);
lean_dec(x_1321);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1453 = !lean_is_exclusive(x_1441);
if (x_1453 == 0)
{
lean_object* x_1454; lean_object* x_1455; uint8_t x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; 
x_1454 = lean_ctor_get(x_1441, 0);
x_1455 = lean_io_error_to_string(x_1454);
x_1456 = 3;
x_1457 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1457, 0, x_1455);
lean_ctor_set_uint8(x_1457, sizeof(void*)*1, x_1456);
x_1458 = lean_array_get_size(x_1432);
x_1459 = lean_array_push(x_1432, x_1457);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1459);
lean_ctor_set(x_1427, 0, x_1458);
lean_ctor_set_tag(x_1441, 0);
lean_ctor_set(x_1441, 0, x_1427);
return x_1441;
}
else
{
lean_object* x_1460; lean_object* x_1461; lean_object* x_1462; uint8_t x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; 
x_1460 = lean_ctor_get(x_1441, 0);
x_1461 = lean_ctor_get(x_1441, 1);
lean_inc(x_1461);
lean_inc(x_1460);
lean_dec(x_1441);
x_1462 = lean_io_error_to_string(x_1460);
x_1463 = 3;
x_1464 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1464, 0, x_1462);
lean_ctor_set_uint8(x_1464, sizeof(void*)*1, x_1463);
x_1465 = lean_array_get_size(x_1432);
x_1466 = lean_array_push(x_1432, x_1464);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1466);
lean_ctor_set(x_1427, 0, x_1465);
x_1467 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1467, 0, x_1427);
lean_ctor_set(x_1467, 1, x_1461);
return x_1467;
}
}
}
else
{
lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; 
x_1468 = lean_ctor_get(x_1427, 1);
lean_inc(x_1468);
lean_dec(x_1427);
x_1469 = lean_ctor_get(x_1, 0);
lean_inc(x_1469);
x_1470 = l_Lake_Env_leanGithash(x_1469);
lean_dec(x_1469);
x_1471 = l_System_Platform_target;
lean_inc(x_1327);
x_1472 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1472, 0, x_1471);
lean_ctor_set(x_1472, 1, x_1470);
lean_ctor_set(x_1472, 2, x_30);
lean_ctor_set(x_1472, 3, x_1327);
x_1473 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_1472);
x_1474 = lean_unsigned_to_nat(80u);
x_1475 = l_Lean_Json_pretty(x_1473, x_1474);
x_1476 = l_IO_FS_Handle_putStrLn(x_1321, x_1475, x_1428);
if (lean_obj_tag(x_1476) == 0)
{
lean_object* x_1477; lean_object* x_1478; 
x_1477 = lean_ctor_get(x_1476, 1);
lean_inc(x_1477);
lean_dec(x_1476);
x_1478 = lean_io_prim_handle_truncate(x_1321, x_1477);
if (lean_obj_tag(x_1478) == 0)
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; 
x_1479 = lean_ctor_get(x_1478, 0);
lean_inc(x_1479);
x_1480 = lean_ctor_get(x_1478, 1);
lean_inc(x_1480);
lean_dec(x_1478);
x_1481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1481, 0, x_1479);
lean_ctor_set(x_1481, 1, x_1468);
x_1328 = x_1481;
x_1329 = x_1480;
goto block_1426;
}
else
{
lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; uint8_t x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; 
x_1482 = lean_ctor_get(x_1478, 0);
lean_inc(x_1482);
x_1483 = lean_ctor_get(x_1478, 1);
lean_inc(x_1483);
lean_dec(x_1478);
x_1484 = lean_io_error_to_string(x_1482);
x_1485 = 3;
x_1486 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1486, 0, x_1484);
lean_ctor_set_uint8(x_1486, sizeof(void*)*1, x_1485);
x_1487 = lean_array_get_size(x_1468);
x_1488 = lean_array_push(x_1468, x_1486);
x_1489 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1489, 0, x_1487);
lean_ctor_set(x_1489, 1, x_1488);
x_1328 = x_1489;
x_1329 = x_1483;
goto block_1426;
}
}
else
{
lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; uint8_t x_1494; lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; lean_object* x_1499; 
lean_dec(x_1327);
lean_dec(x_1321);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1490 = lean_ctor_get(x_1476, 0);
lean_inc(x_1490);
x_1491 = lean_ctor_get(x_1476, 1);
lean_inc(x_1491);
if (lean_is_exclusive(x_1476)) {
 lean_ctor_release(x_1476, 0);
 lean_ctor_release(x_1476, 1);
 x_1492 = x_1476;
} else {
 lean_dec_ref(x_1476);
 x_1492 = lean_box(0);
}
x_1493 = lean_io_error_to_string(x_1490);
x_1494 = 3;
x_1495 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1495, 0, x_1493);
lean_ctor_set_uint8(x_1495, sizeof(void*)*1, x_1494);
x_1496 = lean_array_get_size(x_1468);
x_1497 = lean_array_push(x_1468, x_1495);
x_1498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1498, 0, x_1496);
lean_ctor_set(x_1498, 1, x_1497);
if (lean_is_scalar(x_1492)) {
 x_1499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1499 = x_1492;
 lean_ctor_set_tag(x_1499, 0);
}
lean_ctor_set(x_1499, 0, x_1498);
lean_ctor_set(x_1499, 1, x_1491);
return x_1499;
}
}
}
else
{
uint8_t x_1500; 
lean_dec(x_1327);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1500 = !lean_is_exclusive(x_1427);
if (x_1500 == 0)
{
lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; uint8_t x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; 
x_1501 = lean_ctor_get(x_1427, 1);
x_1502 = lean_ctor_get(x_1427, 0);
lean_dec(x_1502);
x_1503 = lean_io_error_to_string(x_1430);
x_1504 = 3;
x_1505 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1505, 0, x_1503);
lean_ctor_set_uint8(x_1505, sizeof(void*)*1, x_1504);
x_1506 = lean_array_get_size(x_1501);
x_1507 = lean_array_push(x_1501, x_1505);
x_1508 = lean_io_prim_handle_unlock(x_1321, x_1428);
lean_dec(x_1321);
if (lean_obj_tag(x_1508) == 0)
{
lean_object* x_1509; lean_object* x_1510; 
x_1509 = lean_ctor_get(x_1508, 1);
lean_inc(x_1509);
lean_dec(x_1508);
x_1510 = lean_io_remove_file(x_24, x_1509);
lean_dec(x_24);
if (lean_obj_tag(x_1510) == 0)
{
uint8_t x_1511; 
x_1511 = !lean_is_exclusive(x_1510);
if (x_1511 == 0)
{
lean_object* x_1512; 
x_1512 = lean_ctor_get(x_1510, 0);
lean_dec(x_1512);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1507);
lean_ctor_set(x_1427, 0, x_1506);
lean_ctor_set(x_1510, 0, x_1427);
return x_1510;
}
else
{
lean_object* x_1513; lean_object* x_1514; 
x_1513 = lean_ctor_get(x_1510, 1);
lean_inc(x_1513);
lean_dec(x_1510);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1507);
lean_ctor_set(x_1427, 0, x_1506);
x_1514 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1514, 0, x_1427);
lean_ctor_set(x_1514, 1, x_1513);
return x_1514;
}
}
else
{
uint8_t x_1515; 
x_1515 = !lean_is_exclusive(x_1510);
if (x_1515 == 0)
{
lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; 
x_1516 = lean_ctor_get(x_1510, 0);
x_1517 = lean_io_error_to_string(x_1516);
x_1518 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1518, 0, x_1517);
lean_ctor_set_uint8(x_1518, sizeof(void*)*1, x_1504);
x_1519 = lean_array_push(x_1507, x_1518);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1519);
lean_ctor_set(x_1427, 0, x_1506);
lean_ctor_set_tag(x_1510, 0);
lean_ctor_set(x_1510, 0, x_1427);
return x_1510;
}
else
{
lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; 
x_1520 = lean_ctor_get(x_1510, 0);
x_1521 = lean_ctor_get(x_1510, 1);
lean_inc(x_1521);
lean_inc(x_1520);
lean_dec(x_1510);
x_1522 = lean_io_error_to_string(x_1520);
x_1523 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1523, 0, x_1522);
lean_ctor_set_uint8(x_1523, sizeof(void*)*1, x_1504);
x_1524 = lean_array_push(x_1507, x_1523);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1524);
lean_ctor_set(x_1427, 0, x_1506);
x_1525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1525, 0, x_1427);
lean_ctor_set(x_1525, 1, x_1521);
return x_1525;
}
}
}
else
{
uint8_t x_1526; 
lean_dec(x_24);
x_1526 = !lean_is_exclusive(x_1508);
if (x_1526 == 0)
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; 
x_1527 = lean_ctor_get(x_1508, 0);
x_1528 = lean_io_error_to_string(x_1527);
x_1529 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1529, 0, x_1528);
lean_ctor_set_uint8(x_1529, sizeof(void*)*1, x_1504);
x_1530 = lean_array_push(x_1507, x_1529);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1530);
lean_ctor_set(x_1427, 0, x_1506);
lean_ctor_set_tag(x_1508, 0);
lean_ctor_set(x_1508, 0, x_1427);
return x_1508;
}
else
{
lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; 
x_1531 = lean_ctor_get(x_1508, 0);
x_1532 = lean_ctor_get(x_1508, 1);
lean_inc(x_1532);
lean_inc(x_1531);
lean_dec(x_1508);
x_1533 = lean_io_error_to_string(x_1531);
x_1534 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1534, 0, x_1533);
lean_ctor_set_uint8(x_1534, sizeof(void*)*1, x_1504);
x_1535 = lean_array_push(x_1507, x_1534);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1535);
lean_ctor_set(x_1427, 0, x_1506);
x_1536 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1536, 0, x_1427);
lean_ctor_set(x_1536, 1, x_1532);
return x_1536;
}
}
}
else
{
lean_object* x_1537; lean_object* x_1538; uint8_t x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; 
x_1537 = lean_ctor_get(x_1427, 1);
lean_inc(x_1537);
lean_dec(x_1427);
x_1538 = lean_io_error_to_string(x_1430);
x_1539 = 3;
x_1540 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1540, 0, x_1538);
lean_ctor_set_uint8(x_1540, sizeof(void*)*1, x_1539);
x_1541 = lean_array_get_size(x_1537);
x_1542 = lean_array_push(x_1537, x_1540);
x_1543 = lean_io_prim_handle_unlock(x_1321, x_1428);
lean_dec(x_1321);
if (lean_obj_tag(x_1543) == 0)
{
lean_object* x_1544; lean_object* x_1545; 
x_1544 = lean_ctor_get(x_1543, 1);
lean_inc(x_1544);
lean_dec(x_1543);
x_1545 = lean_io_remove_file(x_24, x_1544);
lean_dec(x_24);
if (lean_obj_tag(x_1545) == 0)
{
lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; 
x_1546 = lean_ctor_get(x_1545, 1);
lean_inc(x_1546);
if (lean_is_exclusive(x_1545)) {
 lean_ctor_release(x_1545, 0);
 lean_ctor_release(x_1545, 1);
 x_1547 = x_1545;
} else {
 lean_dec_ref(x_1545);
 x_1547 = lean_box(0);
}
x_1548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1548, 0, x_1541);
lean_ctor_set(x_1548, 1, x_1542);
if (lean_is_scalar(x_1547)) {
 x_1549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1549 = x_1547;
}
lean_ctor_set(x_1549, 0, x_1548);
lean_ctor_set(x_1549, 1, x_1546);
return x_1549;
}
else
{
lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; 
x_1550 = lean_ctor_get(x_1545, 0);
lean_inc(x_1550);
x_1551 = lean_ctor_get(x_1545, 1);
lean_inc(x_1551);
if (lean_is_exclusive(x_1545)) {
 lean_ctor_release(x_1545, 0);
 lean_ctor_release(x_1545, 1);
 x_1552 = x_1545;
} else {
 lean_dec_ref(x_1545);
 x_1552 = lean_box(0);
}
x_1553 = lean_io_error_to_string(x_1550);
x_1554 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1554, 0, x_1553);
lean_ctor_set_uint8(x_1554, sizeof(void*)*1, x_1539);
x_1555 = lean_array_push(x_1542, x_1554);
x_1556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1556, 0, x_1541);
lean_ctor_set(x_1556, 1, x_1555);
if (lean_is_scalar(x_1552)) {
 x_1557 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1557 = x_1552;
 lean_ctor_set_tag(x_1557, 0);
}
lean_ctor_set(x_1557, 0, x_1556);
lean_ctor_set(x_1557, 1, x_1551);
return x_1557;
}
}
else
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; 
lean_dec(x_24);
x_1558 = lean_ctor_get(x_1543, 0);
lean_inc(x_1558);
x_1559 = lean_ctor_get(x_1543, 1);
lean_inc(x_1559);
if (lean_is_exclusive(x_1543)) {
 lean_ctor_release(x_1543, 0);
 lean_ctor_release(x_1543, 1);
 x_1560 = x_1543;
} else {
 lean_dec_ref(x_1543);
 x_1560 = lean_box(0);
}
x_1561 = lean_io_error_to_string(x_1558);
x_1562 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1562, 0, x_1561);
lean_ctor_set_uint8(x_1562, sizeof(void*)*1, x_1539);
x_1563 = lean_array_push(x_1542, x_1562);
x_1564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1564, 0, x_1541);
lean_ctor_set(x_1564, 1, x_1563);
if (lean_is_scalar(x_1560)) {
 x_1565 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1565 = x_1560;
 lean_ctor_set_tag(x_1565, 0);
}
lean_ctor_set(x_1565, 0, x_1564);
lean_ctor_set(x_1565, 1, x_1559);
return x_1565;
}
}
}
}
else
{
uint8_t x_1566; 
lean_dec(x_1429);
lean_dec(x_24);
x_1566 = !lean_is_exclusive(x_1427);
if (x_1566 == 0)
{
lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; 
x_1567 = lean_ctor_get(x_1427, 1);
x_1568 = lean_ctor_get(x_1427, 0);
lean_dec(x_1568);
x_1569 = lean_ctor_get(x_1, 0);
lean_inc(x_1569);
x_1570 = l_Lake_Env_leanGithash(x_1569);
lean_dec(x_1569);
x_1571 = l_System_Platform_target;
lean_inc(x_1327);
x_1572 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1572, 0, x_1571);
lean_ctor_set(x_1572, 1, x_1570);
lean_ctor_set(x_1572, 2, x_30);
lean_ctor_set(x_1572, 3, x_1327);
x_1573 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_1572);
x_1574 = lean_unsigned_to_nat(80u);
x_1575 = l_Lean_Json_pretty(x_1573, x_1574);
x_1576 = l_IO_FS_Handle_putStrLn(x_1321, x_1575, x_1428);
if (lean_obj_tag(x_1576) == 0)
{
lean_object* x_1577; lean_object* x_1578; 
x_1577 = lean_ctor_get(x_1576, 1);
lean_inc(x_1577);
lean_dec(x_1576);
x_1578 = lean_io_prim_handle_truncate(x_1321, x_1577);
if (lean_obj_tag(x_1578) == 0)
{
lean_object* x_1579; lean_object* x_1580; 
x_1579 = lean_ctor_get(x_1578, 0);
lean_inc(x_1579);
x_1580 = lean_ctor_get(x_1578, 1);
lean_inc(x_1580);
lean_dec(x_1578);
lean_ctor_set(x_1427, 0, x_1579);
x_1328 = x_1427;
x_1329 = x_1580;
goto block_1426;
}
else
{
lean_object* x_1581; lean_object* x_1582; lean_object* x_1583; uint8_t x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; 
x_1581 = lean_ctor_get(x_1578, 0);
lean_inc(x_1581);
x_1582 = lean_ctor_get(x_1578, 1);
lean_inc(x_1582);
lean_dec(x_1578);
x_1583 = lean_io_error_to_string(x_1581);
x_1584 = 3;
x_1585 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1585, 0, x_1583);
lean_ctor_set_uint8(x_1585, sizeof(void*)*1, x_1584);
x_1586 = lean_array_get_size(x_1567);
x_1587 = lean_array_push(x_1567, x_1585);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1587);
lean_ctor_set(x_1427, 0, x_1586);
x_1328 = x_1427;
x_1329 = x_1582;
goto block_1426;
}
}
else
{
uint8_t x_1588; 
lean_dec(x_1327);
lean_dec(x_1321);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1588 = !lean_is_exclusive(x_1576);
if (x_1588 == 0)
{
lean_object* x_1589; lean_object* x_1590; uint8_t x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; 
x_1589 = lean_ctor_get(x_1576, 0);
x_1590 = lean_io_error_to_string(x_1589);
x_1591 = 3;
x_1592 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1592, 0, x_1590);
lean_ctor_set_uint8(x_1592, sizeof(void*)*1, x_1591);
x_1593 = lean_array_get_size(x_1567);
x_1594 = lean_array_push(x_1567, x_1592);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1594);
lean_ctor_set(x_1427, 0, x_1593);
lean_ctor_set_tag(x_1576, 0);
lean_ctor_set(x_1576, 0, x_1427);
return x_1576;
}
else
{
lean_object* x_1595; lean_object* x_1596; lean_object* x_1597; uint8_t x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; 
x_1595 = lean_ctor_get(x_1576, 0);
x_1596 = lean_ctor_get(x_1576, 1);
lean_inc(x_1596);
lean_inc(x_1595);
lean_dec(x_1576);
x_1597 = lean_io_error_to_string(x_1595);
x_1598 = 3;
x_1599 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1599, 0, x_1597);
lean_ctor_set_uint8(x_1599, sizeof(void*)*1, x_1598);
x_1600 = lean_array_get_size(x_1567);
x_1601 = lean_array_push(x_1567, x_1599);
lean_ctor_set_tag(x_1427, 1);
lean_ctor_set(x_1427, 1, x_1601);
lean_ctor_set(x_1427, 0, x_1600);
x_1602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1602, 0, x_1427);
lean_ctor_set(x_1602, 1, x_1596);
return x_1602;
}
}
}
else
{
lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; 
x_1603 = lean_ctor_get(x_1427, 1);
lean_inc(x_1603);
lean_dec(x_1427);
x_1604 = lean_ctor_get(x_1, 0);
lean_inc(x_1604);
x_1605 = l_Lake_Env_leanGithash(x_1604);
lean_dec(x_1604);
x_1606 = l_System_Platform_target;
lean_inc(x_1327);
x_1607 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1607, 0, x_1606);
lean_ctor_set(x_1607, 1, x_1605);
lean_ctor_set(x_1607, 2, x_30);
lean_ctor_set(x_1607, 3, x_1327);
x_1608 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_1607);
x_1609 = lean_unsigned_to_nat(80u);
x_1610 = l_Lean_Json_pretty(x_1608, x_1609);
x_1611 = l_IO_FS_Handle_putStrLn(x_1321, x_1610, x_1428);
if (lean_obj_tag(x_1611) == 0)
{
lean_object* x_1612; lean_object* x_1613; 
x_1612 = lean_ctor_get(x_1611, 1);
lean_inc(x_1612);
lean_dec(x_1611);
x_1613 = lean_io_prim_handle_truncate(x_1321, x_1612);
if (lean_obj_tag(x_1613) == 0)
{
lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; 
x_1614 = lean_ctor_get(x_1613, 0);
lean_inc(x_1614);
x_1615 = lean_ctor_get(x_1613, 1);
lean_inc(x_1615);
lean_dec(x_1613);
x_1616 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1616, 0, x_1614);
lean_ctor_set(x_1616, 1, x_1603);
x_1328 = x_1616;
x_1329 = x_1615;
goto block_1426;
}
else
{
lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; uint8_t x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; 
x_1617 = lean_ctor_get(x_1613, 0);
lean_inc(x_1617);
x_1618 = lean_ctor_get(x_1613, 1);
lean_inc(x_1618);
lean_dec(x_1613);
x_1619 = lean_io_error_to_string(x_1617);
x_1620 = 3;
x_1621 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1621, 0, x_1619);
lean_ctor_set_uint8(x_1621, sizeof(void*)*1, x_1620);
x_1622 = lean_array_get_size(x_1603);
x_1623 = lean_array_push(x_1603, x_1621);
x_1624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1624, 0, x_1622);
lean_ctor_set(x_1624, 1, x_1623);
x_1328 = x_1624;
x_1329 = x_1618;
goto block_1426;
}
}
else
{
lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; uint8_t x_1629; lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; lean_object* x_1634; 
lean_dec(x_1327);
lean_dec(x_1321);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1625 = lean_ctor_get(x_1611, 0);
lean_inc(x_1625);
x_1626 = lean_ctor_get(x_1611, 1);
lean_inc(x_1626);
if (lean_is_exclusive(x_1611)) {
 lean_ctor_release(x_1611, 0);
 lean_ctor_release(x_1611, 1);
 x_1627 = x_1611;
} else {
 lean_dec_ref(x_1611);
 x_1627 = lean_box(0);
}
x_1628 = lean_io_error_to_string(x_1625);
x_1629 = 3;
x_1630 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1630, 0, x_1628);
lean_ctor_set_uint8(x_1630, sizeof(void*)*1, x_1629);
x_1631 = lean_array_get_size(x_1603);
x_1632 = lean_array_push(x_1603, x_1630);
x_1633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1633, 0, x_1631);
lean_ctor_set(x_1633, 1, x_1632);
if (lean_is_scalar(x_1627)) {
 x_1634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1634 = x_1627;
 lean_ctor_set_tag(x_1634, 0);
}
lean_ctor_set(x_1634, 0, x_1633);
lean_ctor_set(x_1634, 1, x_1626);
return x_1634;
}
}
}
}
}
else
{
lean_object* x_1643; lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1699; lean_object* x_1700; lean_object* x_1800; 
x_1643 = lean_ctor_get(x_1323, 1);
lean_inc(x_1643);
lean_dec(x_1323);
x_1644 = lean_ctor_get(x_1, 6);
lean_inc(x_1644);
x_1800 = lean_io_remove_file(x_21, x_1324);
if (lean_obj_tag(x_1800) == 0)
{
lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; 
x_1801 = lean_ctor_get(x_1800, 0);
lean_inc(x_1801);
x_1802 = lean_ctor_get(x_1800, 1);
lean_inc(x_1802);
lean_dec(x_1800);
if (lean_is_scalar(x_1322)) {
 x_1803 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1803 = x_1322;
}
lean_ctor_set(x_1803, 0, x_1801);
x_1804 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1804, 0, x_1803);
lean_ctor_set(x_1804, 1, x_1643);
x_1699 = x_1804;
x_1700 = x_1802;
goto block_1799;
}
else
{
lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; lean_object* x_1808; 
x_1805 = lean_ctor_get(x_1800, 0);
lean_inc(x_1805);
x_1806 = lean_ctor_get(x_1800, 1);
lean_inc(x_1806);
lean_dec(x_1800);
if (lean_is_scalar(x_1322)) {
 x_1807 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1807 = x_1322;
 lean_ctor_set_tag(x_1807, 0);
}
lean_ctor_set(x_1807, 0, x_1805);
x_1808 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1808, 0, x_1807);
lean_ctor_set(x_1808, 1, x_1643);
x_1699 = x_1808;
x_1700 = x_1806;
goto block_1799;
}
block_1698:
{
if (lean_obj_tag(x_1645) == 0)
{
lean_object* x_1647; lean_object* x_1648; lean_object* x_1649; 
x_1647 = lean_ctor_get(x_1645, 1);
lean_inc(x_1647);
lean_dec(x_1645);
x_1648 = lean_ctor_get(x_1, 7);
lean_inc(x_1648);
lean_dec(x_1);
x_1649 = l_Lake_elabConfigFile(x_6, x_1644, x_1648, x_8, x_1647, x_1646);
if (lean_obj_tag(x_1649) == 0)
{
lean_object* x_1650; 
x_1650 = lean_ctor_get(x_1649, 0);
lean_inc(x_1650);
if (lean_obj_tag(x_1650) == 0)
{
lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; 
x_1651 = lean_ctor_get(x_1649, 1);
lean_inc(x_1651);
lean_dec(x_1649);
x_1652 = lean_ctor_get(x_1650, 0);
lean_inc(x_1652);
x_1653 = lean_ctor_get(x_1650, 1);
lean_inc(x_1653);
if (lean_is_exclusive(x_1650)) {
 lean_ctor_release(x_1650, 0);
 lean_ctor_release(x_1650, 1);
 x_1654 = x_1650;
} else {
 lean_dec_ref(x_1650);
 x_1654 = lean_box(0);
}
lean_inc(x_1652);
x_1655 = lean_write_module(x_1652, x_21, x_1651);
if (lean_obj_tag(x_1655) == 0)
{
lean_object* x_1656; lean_object* x_1657; 
x_1656 = lean_ctor_get(x_1655, 1);
lean_inc(x_1656);
lean_dec(x_1655);
x_1657 = lean_io_prim_handle_unlock(x_1321, x_1656);
lean_dec(x_1321);
if (lean_obj_tag(x_1657) == 0)
{
lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; 
x_1658 = lean_ctor_get(x_1657, 1);
lean_inc(x_1658);
if (lean_is_exclusive(x_1657)) {
 lean_ctor_release(x_1657, 0);
 lean_ctor_release(x_1657, 1);
 x_1659 = x_1657;
} else {
 lean_dec_ref(x_1657);
 x_1659 = lean_box(0);
}
if (lean_is_scalar(x_1654)) {
 x_1660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1660 = x_1654;
}
lean_ctor_set(x_1660, 0, x_1652);
lean_ctor_set(x_1660, 1, x_1653);
if (lean_is_scalar(x_1659)) {
 x_1661 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1661 = x_1659;
}
lean_ctor_set(x_1661, 0, x_1660);
lean_ctor_set(x_1661, 1, x_1658);
return x_1661;
}
else
{
lean_object* x_1662; lean_object* x_1663; lean_object* x_1664; lean_object* x_1665; uint8_t x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; 
lean_dec(x_1652);
x_1662 = lean_ctor_get(x_1657, 0);
lean_inc(x_1662);
x_1663 = lean_ctor_get(x_1657, 1);
lean_inc(x_1663);
if (lean_is_exclusive(x_1657)) {
 lean_ctor_release(x_1657, 0);
 lean_ctor_release(x_1657, 1);
 x_1664 = x_1657;
} else {
 lean_dec_ref(x_1657);
 x_1664 = lean_box(0);
}
x_1665 = lean_io_error_to_string(x_1662);
x_1666 = 3;
x_1667 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1667, 0, x_1665);
lean_ctor_set_uint8(x_1667, sizeof(void*)*1, x_1666);
x_1668 = lean_array_get_size(x_1653);
x_1669 = lean_array_push(x_1653, x_1667);
if (lean_is_scalar(x_1654)) {
 x_1670 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1670 = x_1654;
 lean_ctor_set_tag(x_1670, 1);
}
lean_ctor_set(x_1670, 0, x_1668);
lean_ctor_set(x_1670, 1, x_1669);
if (lean_is_scalar(x_1664)) {
 x_1671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1671 = x_1664;
 lean_ctor_set_tag(x_1671, 0);
}
lean_ctor_set(x_1671, 0, x_1670);
lean_ctor_set(x_1671, 1, x_1663);
return x_1671;
}
}
else
{
lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; uint8_t x_1676; lean_object* x_1677; lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; 
lean_dec(x_1652);
lean_dec(x_1321);
x_1672 = lean_ctor_get(x_1655, 0);
lean_inc(x_1672);
x_1673 = lean_ctor_get(x_1655, 1);
lean_inc(x_1673);
if (lean_is_exclusive(x_1655)) {
 lean_ctor_release(x_1655, 0);
 lean_ctor_release(x_1655, 1);
 x_1674 = x_1655;
} else {
 lean_dec_ref(x_1655);
 x_1674 = lean_box(0);
}
x_1675 = lean_io_error_to_string(x_1672);
x_1676 = 3;
x_1677 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1677, 0, x_1675);
lean_ctor_set_uint8(x_1677, sizeof(void*)*1, x_1676);
x_1678 = lean_array_get_size(x_1653);
x_1679 = lean_array_push(x_1653, x_1677);
if (lean_is_scalar(x_1654)) {
 x_1680 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1680 = x_1654;
 lean_ctor_set_tag(x_1680, 1);
}
lean_ctor_set(x_1680, 0, x_1678);
lean_ctor_set(x_1680, 1, x_1679);
if (lean_is_scalar(x_1674)) {
 x_1681 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1681 = x_1674;
 lean_ctor_set_tag(x_1681, 0);
}
lean_ctor_set(x_1681, 0, x_1680);
lean_ctor_set(x_1681, 1, x_1673);
return x_1681;
}
}
else
{
lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; 
lean_dec(x_1321);
lean_dec(x_21);
x_1682 = lean_ctor_get(x_1649, 1);
lean_inc(x_1682);
if (lean_is_exclusive(x_1649)) {
 lean_ctor_release(x_1649, 0);
 lean_ctor_release(x_1649, 1);
 x_1683 = x_1649;
} else {
 lean_dec_ref(x_1649);
 x_1683 = lean_box(0);
}
x_1684 = lean_ctor_get(x_1650, 0);
lean_inc(x_1684);
x_1685 = lean_ctor_get(x_1650, 1);
lean_inc(x_1685);
if (lean_is_exclusive(x_1650)) {
 lean_ctor_release(x_1650, 0);
 lean_ctor_release(x_1650, 1);
 x_1686 = x_1650;
} else {
 lean_dec_ref(x_1650);
 x_1686 = lean_box(0);
}
if (lean_is_scalar(x_1686)) {
 x_1687 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1687 = x_1686;
}
lean_ctor_set(x_1687, 0, x_1684);
lean_ctor_set(x_1687, 1, x_1685);
if (lean_is_scalar(x_1683)) {
 x_1688 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1688 = x_1683;
}
lean_ctor_set(x_1688, 0, x_1687);
lean_ctor_set(x_1688, 1, x_1682);
return x_1688;
}
}
else
{
lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; 
lean_dec(x_1321);
lean_dec(x_21);
x_1689 = lean_ctor_get(x_1649, 0);
lean_inc(x_1689);
x_1690 = lean_ctor_get(x_1649, 1);
lean_inc(x_1690);
if (lean_is_exclusive(x_1649)) {
 lean_ctor_release(x_1649, 0);
 lean_ctor_release(x_1649, 1);
 x_1691 = x_1649;
} else {
 lean_dec_ref(x_1649);
 x_1691 = lean_box(0);
}
if (lean_is_scalar(x_1691)) {
 x_1692 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1692 = x_1691;
}
lean_ctor_set(x_1692, 0, x_1689);
lean_ctor_set(x_1692, 1, x_1690);
return x_1692;
}
}
else
{
lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; 
lean_dec(x_1644);
lean_dec(x_1321);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1693 = lean_ctor_get(x_1645, 0);
lean_inc(x_1693);
x_1694 = lean_ctor_get(x_1645, 1);
lean_inc(x_1694);
if (lean_is_exclusive(x_1645)) {
 lean_ctor_release(x_1645, 0);
 lean_ctor_release(x_1645, 1);
 x_1695 = x_1645;
} else {
 lean_dec_ref(x_1645);
 x_1695 = lean_box(0);
}
if (lean_is_scalar(x_1695)) {
 x_1696 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1696 = x_1695;
}
lean_ctor_set(x_1696, 0, x_1693);
lean_ctor_set(x_1696, 1, x_1694);
x_1697 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1697, 0, x_1696);
lean_ctor_set(x_1697, 1, x_1646);
return x_1697;
}
}
block_1799:
{
lean_object* x_1701; 
x_1701 = lean_ctor_get(x_1699, 0);
lean_inc(x_1701);
if (lean_obj_tag(x_1701) == 0)
{
lean_object* x_1702; 
x_1702 = lean_ctor_get(x_1701, 0);
lean_inc(x_1702);
lean_dec(x_1701);
if (lean_obj_tag(x_1702) == 11)
{
lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; 
lean_dec(x_1702);
lean_dec(x_24);
x_1703 = lean_ctor_get(x_1699, 1);
lean_inc(x_1703);
if (lean_is_exclusive(x_1699)) {
 lean_ctor_release(x_1699, 0);
 lean_ctor_release(x_1699, 1);
 x_1704 = x_1699;
} else {
 lean_dec_ref(x_1699);
 x_1704 = lean_box(0);
}
x_1705 = lean_ctor_get(x_1, 0);
lean_inc(x_1705);
x_1706 = l_Lake_Env_leanGithash(x_1705);
lean_dec(x_1705);
x_1707 = l_System_Platform_target;
lean_inc(x_1644);
x_1708 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1708, 0, x_1707);
lean_ctor_set(x_1708, 1, x_1706);
lean_ctor_set(x_1708, 2, x_30);
lean_ctor_set(x_1708, 3, x_1644);
x_1709 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_1708);
x_1710 = lean_unsigned_to_nat(80u);
x_1711 = l_Lean_Json_pretty(x_1709, x_1710);
x_1712 = l_IO_FS_Handle_putStrLn(x_1321, x_1711, x_1700);
if (lean_obj_tag(x_1712) == 0)
{
lean_object* x_1713; lean_object* x_1714; 
x_1713 = lean_ctor_get(x_1712, 1);
lean_inc(x_1713);
lean_dec(x_1712);
x_1714 = lean_io_prim_handle_truncate(x_1321, x_1713);
if (lean_obj_tag(x_1714) == 0)
{
lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; 
x_1715 = lean_ctor_get(x_1714, 0);
lean_inc(x_1715);
x_1716 = lean_ctor_get(x_1714, 1);
lean_inc(x_1716);
lean_dec(x_1714);
if (lean_is_scalar(x_1704)) {
 x_1717 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1717 = x_1704;
}
lean_ctor_set(x_1717, 0, x_1715);
lean_ctor_set(x_1717, 1, x_1703);
x_1645 = x_1717;
x_1646 = x_1716;
goto block_1698;
}
else
{
lean_object* x_1718; lean_object* x_1719; lean_object* x_1720; uint8_t x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; 
x_1718 = lean_ctor_get(x_1714, 0);
lean_inc(x_1718);
x_1719 = lean_ctor_get(x_1714, 1);
lean_inc(x_1719);
lean_dec(x_1714);
x_1720 = lean_io_error_to_string(x_1718);
x_1721 = 3;
x_1722 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1722, 0, x_1720);
lean_ctor_set_uint8(x_1722, sizeof(void*)*1, x_1721);
x_1723 = lean_array_get_size(x_1703);
x_1724 = lean_array_push(x_1703, x_1722);
if (lean_is_scalar(x_1704)) {
 x_1725 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1725 = x_1704;
 lean_ctor_set_tag(x_1725, 1);
}
lean_ctor_set(x_1725, 0, x_1723);
lean_ctor_set(x_1725, 1, x_1724);
x_1645 = x_1725;
x_1646 = x_1719;
goto block_1698;
}
}
else
{
lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; uint8_t x_1730; lean_object* x_1731; lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; 
lean_dec(x_1644);
lean_dec(x_1321);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1726 = lean_ctor_get(x_1712, 0);
lean_inc(x_1726);
x_1727 = lean_ctor_get(x_1712, 1);
lean_inc(x_1727);
if (lean_is_exclusive(x_1712)) {
 lean_ctor_release(x_1712, 0);
 lean_ctor_release(x_1712, 1);
 x_1728 = x_1712;
} else {
 lean_dec_ref(x_1712);
 x_1728 = lean_box(0);
}
x_1729 = lean_io_error_to_string(x_1726);
x_1730 = 3;
x_1731 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1731, 0, x_1729);
lean_ctor_set_uint8(x_1731, sizeof(void*)*1, x_1730);
x_1732 = lean_array_get_size(x_1703);
x_1733 = lean_array_push(x_1703, x_1731);
if (lean_is_scalar(x_1704)) {
 x_1734 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1734 = x_1704;
 lean_ctor_set_tag(x_1734, 1);
}
lean_ctor_set(x_1734, 0, x_1732);
lean_ctor_set(x_1734, 1, x_1733);
if (lean_is_scalar(x_1728)) {
 x_1735 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1735 = x_1728;
 lean_ctor_set_tag(x_1735, 0);
}
lean_ctor_set(x_1735, 0, x_1734);
lean_ctor_set(x_1735, 1, x_1727);
return x_1735;
}
}
else
{
lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; uint8_t x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; 
lean_dec(x_1644);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1736 = lean_ctor_get(x_1699, 1);
lean_inc(x_1736);
if (lean_is_exclusive(x_1699)) {
 lean_ctor_release(x_1699, 0);
 lean_ctor_release(x_1699, 1);
 x_1737 = x_1699;
} else {
 lean_dec_ref(x_1699);
 x_1737 = lean_box(0);
}
x_1738 = lean_io_error_to_string(x_1702);
x_1739 = 3;
x_1740 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1740, 0, x_1738);
lean_ctor_set_uint8(x_1740, sizeof(void*)*1, x_1739);
x_1741 = lean_array_get_size(x_1736);
x_1742 = lean_array_push(x_1736, x_1740);
x_1743 = lean_io_prim_handle_unlock(x_1321, x_1700);
lean_dec(x_1321);
if (lean_obj_tag(x_1743) == 0)
{
lean_object* x_1744; lean_object* x_1745; 
x_1744 = lean_ctor_get(x_1743, 1);
lean_inc(x_1744);
lean_dec(x_1743);
x_1745 = lean_io_remove_file(x_24, x_1744);
lean_dec(x_24);
if (lean_obj_tag(x_1745) == 0)
{
lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; 
x_1746 = lean_ctor_get(x_1745, 1);
lean_inc(x_1746);
if (lean_is_exclusive(x_1745)) {
 lean_ctor_release(x_1745, 0);
 lean_ctor_release(x_1745, 1);
 x_1747 = x_1745;
} else {
 lean_dec_ref(x_1745);
 x_1747 = lean_box(0);
}
if (lean_is_scalar(x_1737)) {
 x_1748 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1748 = x_1737;
 lean_ctor_set_tag(x_1748, 1);
}
lean_ctor_set(x_1748, 0, x_1741);
lean_ctor_set(x_1748, 1, x_1742);
if (lean_is_scalar(x_1747)) {
 x_1749 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1749 = x_1747;
}
lean_ctor_set(x_1749, 0, x_1748);
lean_ctor_set(x_1749, 1, x_1746);
return x_1749;
}
else
{
lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; 
x_1750 = lean_ctor_get(x_1745, 0);
lean_inc(x_1750);
x_1751 = lean_ctor_get(x_1745, 1);
lean_inc(x_1751);
if (lean_is_exclusive(x_1745)) {
 lean_ctor_release(x_1745, 0);
 lean_ctor_release(x_1745, 1);
 x_1752 = x_1745;
} else {
 lean_dec_ref(x_1745);
 x_1752 = lean_box(0);
}
x_1753 = lean_io_error_to_string(x_1750);
x_1754 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1754, 0, x_1753);
lean_ctor_set_uint8(x_1754, sizeof(void*)*1, x_1739);
x_1755 = lean_array_push(x_1742, x_1754);
if (lean_is_scalar(x_1737)) {
 x_1756 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1756 = x_1737;
 lean_ctor_set_tag(x_1756, 1);
}
lean_ctor_set(x_1756, 0, x_1741);
lean_ctor_set(x_1756, 1, x_1755);
if (lean_is_scalar(x_1752)) {
 x_1757 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1757 = x_1752;
 lean_ctor_set_tag(x_1757, 0);
}
lean_ctor_set(x_1757, 0, x_1756);
lean_ctor_set(x_1757, 1, x_1751);
return x_1757;
}
}
else
{
lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; 
lean_dec(x_24);
x_1758 = lean_ctor_get(x_1743, 0);
lean_inc(x_1758);
x_1759 = lean_ctor_get(x_1743, 1);
lean_inc(x_1759);
if (lean_is_exclusive(x_1743)) {
 lean_ctor_release(x_1743, 0);
 lean_ctor_release(x_1743, 1);
 x_1760 = x_1743;
} else {
 lean_dec_ref(x_1743);
 x_1760 = lean_box(0);
}
x_1761 = lean_io_error_to_string(x_1758);
x_1762 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1762, 0, x_1761);
lean_ctor_set_uint8(x_1762, sizeof(void*)*1, x_1739);
x_1763 = lean_array_push(x_1742, x_1762);
if (lean_is_scalar(x_1737)) {
 x_1764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1764 = x_1737;
 lean_ctor_set_tag(x_1764, 1);
}
lean_ctor_set(x_1764, 0, x_1741);
lean_ctor_set(x_1764, 1, x_1763);
if (lean_is_scalar(x_1760)) {
 x_1765 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1765 = x_1760;
 lean_ctor_set_tag(x_1765, 0);
}
lean_ctor_set(x_1765, 0, x_1764);
lean_ctor_set(x_1765, 1, x_1759);
return x_1765;
}
}
}
else
{
lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; 
lean_dec(x_1701);
lean_dec(x_24);
x_1766 = lean_ctor_get(x_1699, 1);
lean_inc(x_1766);
if (lean_is_exclusive(x_1699)) {
 lean_ctor_release(x_1699, 0);
 lean_ctor_release(x_1699, 1);
 x_1767 = x_1699;
} else {
 lean_dec_ref(x_1699);
 x_1767 = lean_box(0);
}
x_1768 = lean_ctor_get(x_1, 0);
lean_inc(x_1768);
x_1769 = l_Lake_Env_leanGithash(x_1768);
lean_dec(x_1768);
x_1770 = l_System_Platform_target;
lean_inc(x_1644);
x_1771 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1771, 0, x_1770);
lean_ctor_set(x_1771, 1, x_1769);
lean_ctor_set(x_1771, 2, x_30);
lean_ctor_set(x_1771, 3, x_1644);
x_1772 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_1771);
x_1773 = lean_unsigned_to_nat(80u);
x_1774 = l_Lean_Json_pretty(x_1772, x_1773);
x_1775 = l_IO_FS_Handle_putStrLn(x_1321, x_1774, x_1700);
if (lean_obj_tag(x_1775) == 0)
{
lean_object* x_1776; lean_object* x_1777; 
x_1776 = lean_ctor_get(x_1775, 1);
lean_inc(x_1776);
lean_dec(x_1775);
x_1777 = lean_io_prim_handle_truncate(x_1321, x_1776);
if (lean_obj_tag(x_1777) == 0)
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; 
x_1778 = lean_ctor_get(x_1777, 0);
lean_inc(x_1778);
x_1779 = lean_ctor_get(x_1777, 1);
lean_inc(x_1779);
lean_dec(x_1777);
if (lean_is_scalar(x_1767)) {
 x_1780 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1780 = x_1767;
}
lean_ctor_set(x_1780, 0, x_1778);
lean_ctor_set(x_1780, 1, x_1766);
x_1645 = x_1780;
x_1646 = x_1779;
goto block_1698;
}
else
{
lean_object* x_1781; lean_object* x_1782; lean_object* x_1783; uint8_t x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; 
x_1781 = lean_ctor_get(x_1777, 0);
lean_inc(x_1781);
x_1782 = lean_ctor_get(x_1777, 1);
lean_inc(x_1782);
lean_dec(x_1777);
x_1783 = lean_io_error_to_string(x_1781);
x_1784 = 3;
x_1785 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1785, 0, x_1783);
lean_ctor_set_uint8(x_1785, sizeof(void*)*1, x_1784);
x_1786 = lean_array_get_size(x_1766);
x_1787 = lean_array_push(x_1766, x_1785);
if (lean_is_scalar(x_1767)) {
 x_1788 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1788 = x_1767;
 lean_ctor_set_tag(x_1788, 1);
}
lean_ctor_set(x_1788, 0, x_1786);
lean_ctor_set(x_1788, 1, x_1787);
x_1645 = x_1788;
x_1646 = x_1782;
goto block_1698;
}
}
else
{
lean_object* x_1789; lean_object* x_1790; lean_object* x_1791; lean_object* x_1792; uint8_t x_1793; lean_object* x_1794; lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; 
lean_dec(x_1644);
lean_dec(x_1321);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1789 = lean_ctor_get(x_1775, 0);
lean_inc(x_1789);
x_1790 = lean_ctor_get(x_1775, 1);
lean_inc(x_1790);
if (lean_is_exclusive(x_1775)) {
 lean_ctor_release(x_1775, 0);
 lean_ctor_release(x_1775, 1);
 x_1791 = x_1775;
} else {
 lean_dec_ref(x_1775);
 x_1791 = lean_box(0);
}
x_1792 = lean_io_error_to_string(x_1789);
x_1793 = 3;
x_1794 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1794, 0, x_1792);
lean_ctor_set_uint8(x_1794, sizeof(void*)*1, x_1793);
x_1795 = lean_array_get_size(x_1766);
x_1796 = lean_array_push(x_1766, x_1794);
if (lean_is_scalar(x_1767)) {
 x_1797 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1797 = x_1767;
 lean_ctor_set_tag(x_1797, 1);
}
lean_ctor_set(x_1797, 0, x_1795);
lean_ctor_set(x_1797, 1, x_1796);
if (lean_is_scalar(x_1791)) {
 x_1798 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1798 = x_1791;
 lean_ctor_set_tag(x_1798, 0);
}
lean_ctor_set(x_1798, 0, x_1797);
lean_ctor_set(x_1798, 1, x_1790);
return x_1798;
}
}
}
}
}
else
{
uint8_t x_1809; 
lean_dec(x_1322);
lean_dec(x_1321);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1809 = !lean_is_exclusive(x_1323);
if (x_1809 == 0)
{
lean_object* x_1810; 
x_1810 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1810, 0, x_1323);
lean_ctor_set(x_1810, 1, x_1324);
return x_1810;
}
else
{
lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; 
x_1811 = lean_ctor_get(x_1323, 0);
x_1812 = lean_ctor_get(x_1323, 1);
lean_inc(x_1812);
lean_inc(x_1811);
lean_dec(x_1323);
x_1813 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1813, 0, x_1811);
lean_ctor_set(x_1813, 1, x_1812);
x_1814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1814, 0, x_1813);
lean_ctor_set(x_1814, 1, x_1324);
return x_1814;
}
}
}
}
else
{
lean_object* x_1827; lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; uint8_t x_2005; lean_object* x_2006; 
x_1827 = lean_ctor_get(x_1269, 1);
lean_inc(x_1827);
lean_dec(x_1269);
x_1828 = lean_ctor_get(x_1271, 0);
lean_inc(x_1828);
if (lean_is_exclusive(x_1271)) {
 lean_ctor_release(x_1271, 0);
 x_1829 = x_1271;
} else {
 lean_dec_ref(x_1271);
 x_1829 = lean_box(0);
}
x_2005 = 1;
x_2006 = lean_io_prim_handle_lock(x_1828, x_2005, x_1270);
if (lean_obj_tag(x_2006) == 0)
{
lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; 
x_2007 = lean_ctor_get(x_2006, 0);
lean_inc(x_2007);
x_2008 = lean_ctor_get(x_2006, 1);
lean_inc(x_2008);
lean_dec(x_2006);
x_2009 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2009, 0, x_2007);
lean_ctor_set(x_2009, 1, x_1827);
x_1830 = x_2009;
x_1831 = x_2008;
goto block_2004;
}
else
{
lean_object* x_2010; lean_object* x_2011; lean_object* x_2012; uint8_t x_2013; lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; lean_object* x_2017; 
x_2010 = lean_ctor_get(x_2006, 0);
lean_inc(x_2010);
x_2011 = lean_ctor_get(x_2006, 1);
lean_inc(x_2011);
lean_dec(x_2006);
x_2012 = lean_io_error_to_string(x_2010);
x_2013 = 3;
x_2014 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2014, 0, x_2012);
lean_ctor_set_uint8(x_2014, sizeof(void*)*1, x_2013);
x_2015 = lean_array_get_size(x_1827);
x_2016 = lean_array_push(x_1827, x_2014);
x_2017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2017, 0, x_2015);
lean_ctor_set(x_2017, 1, x_2016);
x_1830 = x_2017;
x_1831 = x_2011;
goto block_2004;
}
block_2004:
{
if (lean_obj_tag(x_1830) == 0)
{
lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1889; lean_object* x_1890; lean_object* x_1990; 
x_1832 = lean_ctor_get(x_1830, 1);
lean_inc(x_1832);
if (lean_is_exclusive(x_1830)) {
 lean_ctor_release(x_1830, 0);
 lean_ctor_release(x_1830, 1);
 x_1833 = x_1830;
} else {
 lean_dec_ref(x_1830);
 x_1833 = lean_box(0);
}
x_1834 = lean_ctor_get(x_1, 6);
lean_inc(x_1834);
x_1990 = lean_io_remove_file(x_21, x_1831);
if (lean_obj_tag(x_1990) == 0)
{
lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; 
x_1991 = lean_ctor_get(x_1990, 0);
lean_inc(x_1991);
x_1992 = lean_ctor_get(x_1990, 1);
lean_inc(x_1992);
lean_dec(x_1990);
if (lean_is_scalar(x_1829)) {
 x_1993 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1993 = x_1829;
}
lean_ctor_set(x_1993, 0, x_1991);
if (lean_is_scalar(x_1833)) {
 x_1994 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1994 = x_1833;
}
lean_ctor_set(x_1994, 0, x_1993);
lean_ctor_set(x_1994, 1, x_1832);
x_1889 = x_1994;
x_1890 = x_1992;
goto block_1989;
}
else
{
lean_object* x_1995; lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; 
x_1995 = lean_ctor_get(x_1990, 0);
lean_inc(x_1995);
x_1996 = lean_ctor_get(x_1990, 1);
lean_inc(x_1996);
lean_dec(x_1990);
if (lean_is_scalar(x_1829)) {
 x_1997 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1997 = x_1829;
 lean_ctor_set_tag(x_1997, 0);
}
lean_ctor_set(x_1997, 0, x_1995);
if (lean_is_scalar(x_1833)) {
 x_1998 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1998 = x_1833;
}
lean_ctor_set(x_1998, 0, x_1997);
lean_ctor_set(x_1998, 1, x_1832);
x_1889 = x_1998;
x_1890 = x_1996;
goto block_1989;
}
block_1888:
{
if (lean_obj_tag(x_1835) == 0)
{
lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; 
x_1837 = lean_ctor_get(x_1835, 1);
lean_inc(x_1837);
lean_dec(x_1835);
x_1838 = lean_ctor_get(x_1, 7);
lean_inc(x_1838);
lean_dec(x_1);
x_1839 = l_Lake_elabConfigFile(x_6, x_1834, x_1838, x_8, x_1837, x_1836);
if (lean_obj_tag(x_1839) == 0)
{
lean_object* x_1840; 
x_1840 = lean_ctor_get(x_1839, 0);
lean_inc(x_1840);
if (lean_obj_tag(x_1840) == 0)
{
lean_object* x_1841; lean_object* x_1842; lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; 
x_1841 = lean_ctor_get(x_1839, 1);
lean_inc(x_1841);
lean_dec(x_1839);
x_1842 = lean_ctor_get(x_1840, 0);
lean_inc(x_1842);
x_1843 = lean_ctor_get(x_1840, 1);
lean_inc(x_1843);
if (lean_is_exclusive(x_1840)) {
 lean_ctor_release(x_1840, 0);
 lean_ctor_release(x_1840, 1);
 x_1844 = x_1840;
} else {
 lean_dec_ref(x_1840);
 x_1844 = lean_box(0);
}
lean_inc(x_1842);
x_1845 = lean_write_module(x_1842, x_21, x_1841);
if (lean_obj_tag(x_1845) == 0)
{
lean_object* x_1846; lean_object* x_1847; 
x_1846 = lean_ctor_get(x_1845, 1);
lean_inc(x_1846);
lean_dec(x_1845);
x_1847 = lean_io_prim_handle_unlock(x_1828, x_1846);
lean_dec(x_1828);
if (lean_obj_tag(x_1847) == 0)
{
lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; 
x_1848 = lean_ctor_get(x_1847, 1);
lean_inc(x_1848);
if (lean_is_exclusive(x_1847)) {
 lean_ctor_release(x_1847, 0);
 lean_ctor_release(x_1847, 1);
 x_1849 = x_1847;
} else {
 lean_dec_ref(x_1847);
 x_1849 = lean_box(0);
}
if (lean_is_scalar(x_1844)) {
 x_1850 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1850 = x_1844;
}
lean_ctor_set(x_1850, 0, x_1842);
lean_ctor_set(x_1850, 1, x_1843);
if (lean_is_scalar(x_1849)) {
 x_1851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1851 = x_1849;
}
lean_ctor_set(x_1851, 0, x_1850);
lean_ctor_set(x_1851, 1, x_1848);
return x_1851;
}
else
{
lean_object* x_1852; lean_object* x_1853; lean_object* x_1854; lean_object* x_1855; uint8_t x_1856; lean_object* x_1857; lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; 
lean_dec(x_1842);
x_1852 = lean_ctor_get(x_1847, 0);
lean_inc(x_1852);
x_1853 = lean_ctor_get(x_1847, 1);
lean_inc(x_1853);
if (lean_is_exclusive(x_1847)) {
 lean_ctor_release(x_1847, 0);
 lean_ctor_release(x_1847, 1);
 x_1854 = x_1847;
} else {
 lean_dec_ref(x_1847);
 x_1854 = lean_box(0);
}
x_1855 = lean_io_error_to_string(x_1852);
x_1856 = 3;
x_1857 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1857, 0, x_1855);
lean_ctor_set_uint8(x_1857, sizeof(void*)*1, x_1856);
x_1858 = lean_array_get_size(x_1843);
x_1859 = lean_array_push(x_1843, x_1857);
if (lean_is_scalar(x_1844)) {
 x_1860 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1860 = x_1844;
 lean_ctor_set_tag(x_1860, 1);
}
lean_ctor_set(x_1860, 0, x_1858);
lean_ctor_set(x_1860, 1, x_1859);
if (lean_is_scalar(x_1854)) {
 x_1861 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1861 = x_1854;
 lean_ctor_set_tag(x_1861, 0);
}
lean_ctor_set(x_1861, 0, x_1860);
lean_ctor_set(x_1861, 1, x_1853);
return x_1861;
}
}
else
{
lean_object* x_1862; lean_object* x_1863; lean_object* x_1864; lean_object* x_1865; uint8_t x_1866; lean_object* x_1867; lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; 
lean_dec(x_1842);
lean_dec(x_1828);
x_1862 = lean_ctor_get(x_1845, 0);
lean_inc(x_1862);
x_1863 = lean_ctor_get(x_1845, 1);
lean_inc(x_1863);
if (lean_is_exclusive(x_1845)) {
 lean_ctor_release(x_1845, 0);
 lean_ctor_release(x_1845, 1);
 x_1864 = x_1845;
} else {
 lean_dec_ref(x_1845);
 x_1864 = lean_box(0);
}
x_1865 = lean_io_error_to_string(x_1862);
x_1866 = 3;
x_1867 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1867, 0, x_1865);
lean_ctor_set_uint8(x_1867, sizeof(void*)*1, x_1866);
x_1868 = lean_array_get_size(x_1843);
x_1869 = lean_array_push(x_1843, x_1867);
if (lean_is_scalar(x_1844)) {
 x_1870 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1870 = x_1844;
 lean_ctor_set_tag(x_1870, 1);
}
lean_ctor_set(x_1870, 0, x_1868);
lean_ctor_set(x_1870, 1, x_1869);
if (lean_is_scalar(x_1864)) {
 x_1871 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1871 = x_1864;
 lean_ctor_set_tag(x_1871, 0);
}
lean_ctor_set(x_1871, 0, x_1870);
lean_ctor_set(x_1871, 1, x_1863);
return x_1871;
}
}
else
{
lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; 
lean_dec(x_1828);
lean_dec(x_21);
x_1872 = lean_ctor_get(x_1839, 1);
lean_inc(x_1872);
if (lean_is_exclusive(x_1839)) {
 lean_ctor_release(x_1839, 0);
 lean_ctor_release(x_1839, 1);
 x_1873 = x_1839;
} else {
 lean_dec_ref(x_1839);
 x_1873 = lean_box(0);
}
x_1874 = lean_ctor_get(x_1840, 0);
lean_inc(x_1874);
x_1875 = lean_ctor_get(x_1840, 1);
lean_inc(x_1875);
if (lean_is_exclusive(x_1840)) {
 lean_ctor_release(x_1840, 0);
 lean_ctor_release(x_1840, 1);
 x_1876 = x_1840;
} else {
 lean_dec_ref(x_1840);
 x_1876 = lean_box(0);
}
if (lean_is_scalar(x_1876)) {
 x_1877 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1877 = x_1876;
}
lean_ctor_set(x_1877, 0, x_1874);
lean_ctor_set(x_1877, 1, x_1875);
if (lean_is_scalar(x_1873)) {
 x_1878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1878 = x_1873;
}
lean_ctor_set(x_1878, 0, x_1877);
lean_ctor_set(x_1878, 1, x_1872);
return x_1878;
}
}
else
{
lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; 
lean_dec(x_1828);
lean_dec(x_21);
x_1879 = lean_ctor_get(x_1839, 0);
lean_inc(x_1879);
x_1880 = lean_ctor_get(x_1839, 1);
lean_inc(x_1880);
if (lean_is_exclusive(x_1839)) {
 lean_ctor_release(x_1839, 0);
 lean_ctor_release(x_1839, 1);
 x_1881 = x_1839;
} else {
 lean_dec_ref(x_1839);
 x_1881 = lean_box(0);
}
if (lean_is_scalar(x_1881)) {
 x_1882 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1882 = x_1881;
}
lean_ctor_set(x_1882, 0, x_1879);
lean_ctor_set(x_1882, 1, x_1880);
return x_1882;
}
}
else
{
lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; 
lean_dec(x_1834);
lean_dec(x_1828);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1883 = lean_ctor_get(x_1835, 0);
lean_inc(x_1883);
x_1884 = lean_ctor_get(x_1835, 1);
lean_inc(x_1884);
if (lean_is_exclusive(x_1835)) {
 lean_ctor_release(x_1835, 0);
 lean_ctor_release(x_1835, 1);
 x_1885 = x_1835;
} else {
 lean_dec_ref(x_1835);
 x_1885 = lean_box(0);
}
if (lean_is_scalar(x_1885)) {
 x_1886 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1886 = x_1885;
}
lean_ctor_set(x_1886, 0, x_1883);
lean_ctor_set(x_1886, 1, x_1884);
x_1887 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1887, 0, x_1886);
lean_ctor_set(x_1887, 1, x_1836);
return x_1887;
}
}
block_1989:
{
lean_object* x_1891; 
x_1891 = lean_ctor_get(x_1889, 0);
lean_inc(x_1891);
if (lean_obj_tag(x_1891) == 0)
{
lean_object* x_1892; 
x_1892 = lean_ctor_get(x_1891, 0);
lean_inc(x_1892);
lean_dec(x_1891);
if (lean_obj_tag(x_1892) == 11)
{
lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; 
lean_dec(x_1892);
lean_dec(x_24);
x_1893 = lean_ctor_get(x_1889, 1);
lean_inc(x_1893);
if (lean_is_exclusive(x_1889)) {
 lean_ctor_release(x_1889, 0);
 lean_ctor_release(x_1889, 1);
 x_1894 = x_1889;
} else {
 lean_dec_ref(x_1889);
 x_1894 = lean_box(0);
}
x_1895 = lean_ctor_get(x_1, 0);
lean_inc(x_1895);
x_1896 = l_Lake_Env_leanGithash(x_1895);
lean_dec(x_1895);
x_1897 = l_System_Platform_target;
lean_inc(x_1834);
x_1898 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1898, 0, x_1897);
lean_ctor_set(x_1898, 1, x_1896);
lean_ctor_set(x_1898, 2, x_30);
lean_ctor_set(x_1898, 3, x_1834);
x_1899 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_1898);
x_1900 = lean_unsigned_to_nat(80u);
x_1901 = l_Lean_Json_pretty(x_1899, x_1900);
x_1902 = l_IO_FS_Handle_putStrLn(x_1828, x_1901, x_1890);
if (lean_obj_tag(x_1902) == 0)
{
lean_object* x_1903; lean_object* x_1904; 
x_1903 = lean_ctor_get(x_1902, 1);
lean_inc(x_1903);
lean_dec(x_1902);
x_1904 = lean_io_prim_handle_truncate(x_1828, x_1903);
if (lean_obj_tag(x_1904) == 0)
{
lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; 
x_1905 = lean_ctor_get(x_1904, 0);
lean_inc(x_1905);
x_1906 = lean_ctor_get(x_1904, 1);
lean_inc(x_1906);
lean_dec(x_1904);
if (lean_is_scalar(x_1894)) {
 x_1907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1907 = x_1894;
}
lean_ctor_set(x_1907, 0, x_1905);
lean_ctor_set(x_1907, 1, x_1893);
x_1835 = x_1907;
x_1836 = x_1906;
goto block_1888;
}
else
{
lean_object* x_1908; lean_object* x_1909; lean_object* x_1910; uint8_t x_1911; lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; 
x_1908 = lean_ctor_get(x_1904, 0);
lean_inc(x_1908);
x_1909 = lean_ctor_get(x_1904, 1);
lean_inc(x_1909);
lean_dec(x_1904);
x_1910 = lean_io_error_to_string(x_1908);
x_1911 = 3;
x_1912 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1912, 0, x_1910);
lean_ctor_set_uint8(x_1912, sizeof(void*)*1, x_1911);
x_1913 = lean_array_get_size(x_1893);
x_1914 = lean_array_push(x_1893, x_1912);
if (lean_is_scalar(x_1894)) {
 x_1915 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1915 = x_1894;
 lean_ctor_set_tag(x_1915, 1);
}
lean_ctor_set(x_1915, 0, x_1913);
lean_ctor_set(x_1915, 1, x_1914);
x_1835 = x_1915;
x_1836 = x_1909;
goto block_1888;
}
}
else
{
lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; uint8_t x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; 
lean_dec(x_1834);
lean_dec(x_1828);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1916 = lean_ctor_get(x_1902, 0);
lean_inc(x_1916);
x_1917 = lean_ctor_get(x_1902, 1);
lean_inc(x_1917);
if (lean_is_exclusive(x_1902)) {
 lean_ctor_release(x_1902, 0);
 lean_ctor_release(x_1902, 1);
 x_1918 = x_1902;
} else {
 lean_dec_ref(x_1902);
 x_1918 = lean_box(0);
}
x_1919 = lean_io_error_to_string(x_1916);
x_1920 = 3;
x_1921 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1921, 0, x_1919);
lean_ctor_set_uint8(x_1921, sizeof(void*)*1, x_1920);
x_1922 = lean_array_get_size(x_1893);
x_1923 = lean_array_push(x_1893, x_1921);
if (lean_is_scalar(x_1894)) {
 x_1924 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1924 = x_1894;
 lean_ctor_set_tag(x_1924, 1);
}
lean_ctor_set(x_1924, 0, x_1922);
lean_ctor_set(x_1924, 1, x_1923);
if (lean_is_scalar(x_1918)) {
 x_1925 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1925 = x_1918;
 lean_ctor_set_tag(x_1925, 0);
}
lean_ctor_set(x_1925, 0, x_1924);
lean_ctor_set(x_1925, 1, x_1917);
return x_1925;
}
}
else
{
lean_object* x_1926; lean_object* x_1927; lean_object* x_1928; uint8_t x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; lean_object* x_1933; 
lean_dec(x_1834);
lean_dec(x_30);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1926 = lean_ctor_get(x_1889, 1);
lean_inc(x_1926);
if (lean_is_exclusive(x_1889)) {
 lean_ctor_release(x_1889, 0);
 lean_ctor_release(x_1889, 1);
 x_1927 = x_1889;
} else {
 lean_dec_ref(x_1889);
 x_1927 = lean_box(0);
}
x_1928 = lean_io_error_to_string(x_1892);
x_1929 = 3;
x_1930 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1930, 0, x_1928);
lean_ctor_set_uint8(x_1930, sizeof(void*)*1, x_1929);
x_1931 = lean_array_get_size(x_1926);
x_1932 = lean_array_push(x_1926, x_1930);
x_1933 = lean_io_prim_handle_unlock(x_1828, x_1890);
lean_dec(x_1828);
if (lean_obj_tag(x_1933) == 0)
{
lean_object* x_1934; lean_object* x_1935; 
x_1934 = lean_ctor_get(x_1933, 1);
lean_inc(x_1934);
lean_dec(x_1933);
x_1935 = lean_io_remove_file(x_24, x_1934);
lean_dec(x_24);
if (lean_obj_tag(x_1935) == 0)
{
lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; 
x_1936 = lean_ctor_get(x_1935, 1);
lean_inc(x_1936);
if (lean_is_exclusive(x_1935)) {
 lean_ctor_release(x_1935, 0);
 lean_ctor_release(x_1935, 1);
 x_1937 = x_1935;
} else {
 lean_dec_ref(x_1935);
 x_1937 = lean_box(0);
}
if (lean_is_scalar(x_1927)) {
 x_1938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1938 = x_1927;
 lean_ctor_set_tag(x_1938, 1);
}
lean_ctor_set(x_1938, 0, x_1931);
lean_ctor_set(x_1938, 1, x_1932);
if (lean_is_scalar(x_1937)) {
 x_1939 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1939 = x_1937;
}
lean_ctor_set(x_1939, 0, x_1938);
lean_ctor_set(x_1939, 1, x_1936);
return x_1939;
}
else
{
lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; 
x_1940 = lean_ctor_get(x_1935, 0);
lean_inc(x_1940);
x_1941 = lean_ctor_get(x_1935, 1);
lean_inc(x_1941);
if (lean_is_exclusive(x_1935)) {
 lean_ctor_release(x_1935, 0);
 lean_ctor_release(x_1935, 1);
 x_1942 = x_1935;
} else {
 lean_dec_ref(x_1935);
 x_1942 = lean_box(0);
}
x_1943 = lean_io_error_to_string(x_1940);
x_1944 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1944, 0, x_1943);
lean_ctor_set_uint8(x_1944, sizeof(void*)*1, x_1929);
x_1945 = lean_array_push(x_1932, x_1944);
if (lean_is_scalar(x_1927)) {
 x_1946 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1946 = x_1927;
 lean_ctor_set_tag(x_1946, 1);
}
lean_ctor_set(x_1946, 0, x_1931);
lean_ctor_set(x_1946, 1, x_1945);
if (lean_is_scalar(x_1942)) {
 x_1947 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1947 = x_1942;
 lean_ctor_set_tag(x_1947, 0);
}
lean_ctor_set(x_1947, 0, x_1946);
lean_ctor_set(x_1947, 1, x_1941);
return x_1947;
}
}
else
{
lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; 
lean_dec(x_24);
x_1948 = lean_ctor_get(x_1933, 0);
lean_inc(x_1948);
x_1949 = lean_ctor_get(x_1933, 1);
lean_inc(x_1949);
if (lean_is_exclusive(x_1933)) {
 lean_ctor_release(x_1933, 0);
 lean_ctor_release(x_1933, 1);
 x_1950 = x_1933;
} else {
 lean_dec_ref(x_1933);
 x_1950 = lean_box(0);
}
x_1951 = lean_io_error_to_string(x_1948);
x_1952 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1952, 0, x_1951);
lean_ctor_set_uint8(x_1952, sizeof(void*)*1, x_1929);
x_1953 = lean_array_push(x_1932, x_1952);
if (lean_is_scalar(x_1927)) {
 x_1954 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1954 = x_1927;
 lean_ctor_set_tag(x_1954, 1);
}
lean_ctor_set(x_1954, 0, x_1931);
lean_ctor_set(x_1954, 1, x_1953);
if (lean_is_scalar(x_1950)) {
 x_1955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1955 = x_1950;
 lean_ctor_set_tag(x_1955, 0);
}
lean_ctor_set(x_1955, 0, x_1954);
lean_ctor_set(x_1955, 1, x_1949);
return x_1955;
}
}
}
else
{
lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; 
lean_dec(x_1891);
lean_dec(x_24);
x_1956 = lean_ctor_get(x_1889, 1);
lean_inc(x_1956);
if (lean_is_exclusive(x_1889)) {
 lean_ctor_release(x_1889, 0);
 lean_ctor_release(x_1889, 1);
 x_1957 = x_1889;
} else {
 lean_dec_ref(x_1889);
 x_1957 = lean_box(0);
}
x_1958 = lean_ctor_get(x_1, 0);
lean_inc(x_1958);
x_1959 = l_Lake_Env_leanGithash(x_1958);
lean_dec(x_1958);
x_1960 = l_System_Platform_target;
lean_inc(x_1834);
x_1961 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1961, 0, x_1960);
lean_ctor_set(x_1961, 1, x_1959);
lean_ctor_set(x_1961, 2, x_30);
lean_ctor_set(x_1961, 3, x_1834);
x_1962 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086_(x_1961);
x_1963 = lean_unsigned_to_nat(80u);
x_1964 = l_Lean_Json_pretty(x_1962, x_1963);
x_1965 = l_IO_FS_Handle_putStrLn(x_1828, x_1964, x_1890);
if (lean_obj_tag(x_1965) == 0)
{
lean_object* x_1966; lean_object* x_1967; 
x_1966 = lean_ctor_get(x_1965, 1);
lean_inc(x_1966);
lean_dec(x_1965);
x_1967 = lean_io_prim_handle_truncate(x_1828, x_1966);
if (lean_obj_tag(x_1967) == 0)
{
lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; 
x_1968 = lean_ctor_get(x_1967, 0);
lean_inc(x_1968);
x_1969 = lean_ctor_get(x_1967, 1);
lean_inc(x_1969);
lean_dec(x_1967);
if (lean_is_scalar(x_1957)) {
 x_1970 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1970 = x_1957;
}
lean_ctor_set(x_1970, 0, x_1968);
lean_ctor_set(x_1970, 1, x_1956);
x_1835 = x_1970;
x_1836 = x_1969;
goto block_1888;
}
else
{
lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; uint8_t x_1974; lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; 
x_1971 = lean_ctor_get(x_1967, 0);
lean_inc(x_1971);
x_1972 = lean_ctor_get(x_1967, 1);
lean_inc(x_1972);
lean_dec(x_1967);
x_1973 = lean_io_error_to_string(x_1971);
x_1974 = 3;
x_1975 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1975, 0, x_1973);
lean_ctor_set_uint8(x_1975, sizeof(void*)*1, x_1974);
x_1976 = lean_array_get_size(x_1956);
x_1977 = lean_array_push(x_1956, x_1975);
if (lean_is_scalar(x_1957)) {
 x_1978 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1978 = x_1957;
 lean_ctor_set_tag(x_1978, 1);
}
lean_ctor_set(x_1978, 0, x_1976);
lean_ctor_set(x_1978, 1, x_1977);
x_1835 = x_1978;
x_1836 = x_1972;
goto block_1888;
}
}
else
{
lean_object* x_1979; lean_object* x_1980; lean_object* x_1981; lean_object* x_1982; uint8_t x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; 
lean_dec(x_1834);
lean_dec(x_1828);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1979 = lean_ctor_get(x_1965, 0);
lean_inc(x_1979);
x_1980 = lean_ctor_get(x_1965, 1);
lean_inc(x_1980);
if (lean_is_exclusive(x_1965)) {
 lean_ctor_release(x_1965, 0);
 lean_ctor_release(x_1965, 1);
 x_1981 = x_1965;
} else {
 lean_dec_ref(x_1965);
 x_1981 = lean_box(0);
}
x_1982 = lean_io_error_to_string(x_1979);
x_1983 = 3;
x_1984 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1984, 0, x_1982);
lean_ctor_set_uint8(x_1984, sizeof(void*)*1, x_1983);
x_1985 = lean_array_get_size(x_1956);
x_1986 = lean_array_push(x_1956, x_1984);
if (lean_is_scalar(x_1957)) {
 x_1987 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1987 = x_1957;
 lean_ctor_set_tag(x_1987, 1);
}
lean_ctor_set(x_1987, 0, x_1985);
lean_ctor_set(x_1987, 1, x_1986);
if (lean_is_scalar(x_1981)) {
 x_1988 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1988 = x_1981;
 lean_ctor_set_tag(x_1988, 0);
}
lean_ctor_set(x_1988, 0, x_1987);
lean_ctor_set(x_1988, 1, x_1980);
return x_1988;
}
}
}
}
else
{
lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; lean_object* x_2003; 
lean_dec(x_1829);
lean_dec(x_1828);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1999 = lean_ctor_get(x_1830, 0);
lean_inc(x_1999);
x_2000 = lean_ctor_get(x_1830, 1);
lean_inc(x_2000);
if (lean_is_exclusive(x_1830)) {
 lean_ctor_release(x_1830, 0);
 lean_ctor_release(x_1830, 1);
 x_2001 = x_1830;
} else {
 lean_dec_ref(x_1830);
 x_2001 = lean_box(0);
}
if (lean_is_scalar(x_2001)) {
 x_2002 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2002 = x_2001;
}
lean_ctor_set(x_2002, 0, x_1999);
lean_ctor_set(x_2002, 1, x_2000);
x_2003 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2003, 0, x_2002);
lean_ctor_set(x_2003, 1, x_1831);
return x_2003;
}
}
}
}
}
}
else
{
uint8_t x_2109; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_2109 = !lean_is_exclusive(x_28);
if (x_2109 == 0)
{
lean_object* x_2110; 
x_2110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2110, 0, x_28);
lean_ctor_set(x_2110, 1, x_29);
return x_2110;
}
else
{
lean_object* x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; 
x_2111 = lean_ctor_get(x_28, 0);
x_2112 = lean_ctor_get(x_28, 1);
lean_inc(x_2112);
lean_inc(x_2111);
lean_dec(x_28);
x_2113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2113, 0, x_2111);
lean_ctor_set(x_2113, 1, x_2112);
x_2114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2114, 0, x_2113);
lean_ctor_set(x_2114, 1, x_29);
return x_2114;
}
}
}
}
}
}
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
l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__1 = _init_l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__1();
lean_mark_persistent(l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__1);
l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__2 = _init_l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__2();
lean_mark_persistent(l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__2);
l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__3 = _init_l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__3();
lean_mark_persistent(l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__3);
res = l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lake_importEnvCache = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_importEnvCache);
lean_dec_ref(res);
l_Lake_importModulesUsingCache___lambda__1___closed__1 = _init_l_Lake_importModulesUsingCache___lambda__1___closed__1();
lean_mark_persistent(l_Lake_importModulesUsingCache___lambda__1___closed__1);
l_Lake_importModulesUsingCache___lambda__1___closed__2 = _init_l_Lake_importModulesUsingCache___lambda__1___closed__2();
lean_mark_persistent(l_Lake_importModulesUsingCache___lambda__1___closed__2);
l_Lake_importModulesUsingCache___closed__1 = _init_l_Lake_importModulesUsingCache___closed__1();
l_Lake_importModulesUsingCache___closed__2 = _init_l_Lake_importModulesUsingCache___closed__2();
l_Lake_importModulesUsingCache___closed__3 = _init_l_Lake_importModulesUsingCache___closed__3();
l_Lake_importModulesUsingCache___closed__4 = _init_l_Lake_importModulesUsingCache___closed__4();
l_Lake_importModulesUsingCache___closed__5 = _init_l_Lake_importModulesUsingCache___closed__5();
l_Lake_processHeader___closed__1 = _init_l_Lake_processHeader___closed__1();
lean_mark_persistent(l_Lake_processHeader___closed__1);
l_Lake_configModuleName___closed__1 = _init_l_Lake_configModuleName___closed__1();
lean_mark_persistent(l_Lake_configModuleName___closed__1);
l_Lake_configModuleName___closed__2 = _init_l_Lake_configModuleName___closed__2();
lean_mark_persistent(l_Lake_configModuleName___closed__2);
l_Lake_configModuleName = _init_l_Lake_configModuleName();
lean_mark_persistent(l_Lake_configModuleName);
l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1 = _init_l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at_Lake_elabConfigFile___spec__1___lambda__1___closed__1);
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
l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___closed__1);
l_Lake_importConfigFileCore___closed__1 = _init_l_Lake_importConfigFileCore___closed__1();
lean_mark_persistent(l_Lake_importConfigFileCore___closed__1);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__1 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__1();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__1);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__2 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__2();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__2);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__3 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__3();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__3);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__4 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__4();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1086____closed__4);
l_Lake_instToJsonConfigTrace___closed__1 = _init_l_Lake_instToJsonConfigTrace___closed__1();
lean_mark_persistent(l_Lake_instToJsonConfigTrace___closed__1);
l_Lake_instToJsonConfigTrace = _init_l_Lake_instToJsonConfigTrace();
lean_mark_persistent(l_Lake_instToJsonConfigTrace);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__1);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__2 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__2();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__2);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__3 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__3();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____spec__1___closed__3);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__1 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__1();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__1);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__2 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__2();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__2);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__3);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__4 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__4();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__4);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__5 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__5();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__5);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__6 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__6();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__6);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__7 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__7();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__7);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__8 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__8();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__8);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__9 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__9();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__9);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__10 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__10();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__10);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__11 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__11();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__11);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__12 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__12();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__12);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__13 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__13();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__13);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__14 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__14();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__14);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__15 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__15();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__15);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__16 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__16();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__16);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__17 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__17();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__17);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__18 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__18();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__18);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__19 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__19();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__19);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__20 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__20();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__20);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__21 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__21();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__21);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__22 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__22();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__22);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__23 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__23();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_1166____closed__23);
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
l_Lake_importConfigFile___closed__12 = _init_l_Lake_importConfigFile___closed__12();
lean_mark_persistent(l_Lake_importConfigFile___closed__12);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
