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
lean_object* l_Lean_Json_getObj_x3f(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__40;
lean_object* lean_io_prim_handle_lock(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_readModuleData(lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__1;
lean_object* lean_io_prim_handle_unlock(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_dirExt;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__15;
static lean_object* l_Lake_elabConfigFile___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instHashableImport__lake___closed__1;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__8;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_io_remove_file(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_80____boxed(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__21;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__23;
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lake_instBEqImport__lake;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__49;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__12;
extern lean_object* l_Lean_instInhabitedEnvExtensionState;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__3;
static lean_object* l_Lake_importConfigFile___closed__10;
lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__11;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__39;
lean_object* l_Lean_mkExtNameMap(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Elab_Command_mkState(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValAs_x3f___at_Lean_JsonRpc_instFromJsonMessage___spec__3(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__9;
static lean_object* l_Lake_instToJsonConfigTrace___closed__1;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(lean_object*);
static lean_object* l_Lake_configModuleName___closed__2;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lake_importConfigFile___closed__4;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_elabConfigFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__52;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__11;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__12;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__14;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__19;
static lean_object* l_Lake_importConfigFile___closed__6;
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__12;
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_headerToImports(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__22;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__29;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__17;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_optsExt;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__6___at_Lake_importModulesUsingCache___spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__19;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__21;
static lean_object* l_Lake_importConfigFileCore___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache(lean_object*, lean_object*, uint32_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__15;
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_foldM___at___private_Lake_Load_Manifest_0__Lake_fromJsonPackageEntryV6____x40_Lake_Load_Manifest___hyg_115____spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__10;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__24;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__51;
lean_object* lean_io_prim_handle_try_lock(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_elabConfigFile___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lake_importModulesUsingCache___spec__10___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__13;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__2;
lean_object* l_IO_FS_Handle_putStrLn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_elabConfigFile___closed__2;
static lean_object* l_Lake_instBEqImport__lake___closed__1;
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121_(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__43;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_elabConfigFile___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_getObjValD(lean_object*, lean_object*);
static uint64_t l_Lake_importModulesUsingCache___closed__4;
lean_object* l_Lean_instInhabitedPersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__1;
static lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__3;
lean_object* lean_uint64_to_nat(uint64_t);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__11;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__32;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_elabConfigFile___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__34;
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__2___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__9;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__3;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__23;
static uint64_t l_Lake_importModulesUsingCache___closed__3;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__18;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__5;
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__3;
static lean_object* l_Lake_processHeader___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__38;
LEAN_EXPORT uint64_t l___private_Lake_Load_Lean_Elab_0__Lake_hashImport____x40_Lake_Load_Lean_Elab___hyg_80_(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setMainModule(lean_object*, lean_object*);
static lean_object* l_Lake_instFromJsonConfigTrace___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__27;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_elabConfigFile___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__1;
static lean_object* l_Lake_importConfigFile___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___private_Lean_Environment_0__Lean_setImportedEntries___spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__16;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__16;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__31;
lean_object* l_Lake_LogEntry_ofMessage(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instFromJsonConfigTrace;
lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
static lean_object* l_Lake_configModuleName___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__35;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__41;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__6;
extern lean_object* l_Lake_defaultLakeDir;
LEAN_EXPORT lean_object* l_Lake_importConfigFile(lean_object*, lean_object*, lean_object*);
static uint64_t l_Lake_importModulesUsingCache___closed__2;
LEAN_EXPORT lean_object* l_Lake_processHeader(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__2;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__53;
LEAN_EXPORT lean_object* l_Lake_processHeader___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__50;
LEAN_EXPORT lean_object* l_Lake_instToJsonConfigTrace;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__47;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__25;
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_elabConfigFile___closed__1;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__14;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_importModulesUsingCache___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lake_importModulesUsingCache___spec__6(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__37;
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_elabConfigFile___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Internal_Parsec_String_Parser_run___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____lambda__1___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_setState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__8;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__45;
lean_object* l_Lean_Elab_IO_processCommands(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_leanGithash(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__3;
static lean_object* l_Lake_importConfigFile___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__33;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importEnvCache;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__7;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__1;
uint64_t l_Lean_Name_hash___override(lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__44;
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__18;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__10;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__20;
lean_object* l_Lean_RBNode_fold___at_Lake_Env_baseVars___spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_beqImport____x40_Lake_Load_Lean_Elab___hyg_6_(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__20;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__22;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__7;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__30;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_elabConfigFile___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
static size_t l_Lake_importModulesUsingCache___closed__5;
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_elabConfigFile___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__48;
lean_object* l_Lean_Json_Parser_any(lean_object*);
static lean_object* l_Lake_importConfigFile___closed__8;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__42;
lean_object* l_List_flatMapTR_go___at___private_Lean_Util_Paths_0__Lean_toJsonLeanPaths____x40_Lean_Util_Paths___hyg_55____spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_persistentEnvExtensionsRef;
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__46;
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121____closed__2;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__9;
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_elabConfigFile___closed__3;
size_t lean_usize_add(size_t, size_t);
static uint64_t l_Lake_importModulesUsingCache___closed__1;
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore_lakeExts;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950_(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__13;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_write_module(lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__2;
LEAN_EXPORT lean_object* l_Lake_instHashableImport__lake;
lean_object* l_IO_FS_Handle_readToEnd(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFile___closed__2;
lean_object* lean_io_prim_handle_truncate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_configModuleName;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lake_importModulesUsingCache___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_importModulesUsingCache___lambda__1___closed__2;
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__5;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__4;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_parseHeader(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__26;
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__36;
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lake_importModulesUsingCache___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__54;
LEAN_EXPORT uint64_t l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(lean_object*, size_t, size_t, uint64_t);
lean_object* l_Lean_Json_pretty(lean_object*, lean_object*);
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__6;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_importModulesUsingCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lake_environment_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__2;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__2___closed__1;
static lean_object* l_Lake_importConfigFileCore_lakeExts___closed__28;
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_addToEnv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_importModulesUsingCache___spec__3(lean_object*);
size_t lean_usize_land(size_t, size_t);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__17;
static lean_object* l_Lake_importConfigFile___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_importConfigFileCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__4;
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
lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_importModulesUsingCache___lambda__1___closed__1;
x_7 = 0;
x_8 = 1;
x_9 = 2;
lean_inc(x_1);
x_10 = l_Lean_importModules(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; size_t x_29; uint64_t x_30; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lake_importModulesUsingCache___lambda__1___closed__2;
x_14 = lean_st_ref_take(x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_19 = x_15;
} else {
 lean_dec_ref(x_15);
 x_19 = lean_box(0);
}
x_20 = lean_array_get_size(x_18);
x_21 = 7;
x_22 = lean_array_get_size(x_1);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
x_25 = 32;
x_26 = 16;
x_27 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_28 = 1;
x_29 = lean_usize_sub(x_27, x_28);
if (x_24 == 0)
{
lean_dec(x_22);
x_30 = x_21;
goto block_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_22, x_22);
if (x_73 == 0)
{
lean_dec(x_22);
x_30 = x_21;
goto block_72;
}
else
{
size_t x_74; size_t x_75; uint64_t x_76; 
x_74 = 0;
x_75 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_76 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(x_1, x_74, x_75, x_21);
x_30 = x_76;
goto block_72;
}
}
block_72:
{
uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_31 = lean_uint64_shift_right(x_30, x_25);
x_32 = lean_uint64_xor(x_30, x_31);
x_33 = lean_uint64_shift_right(x_32, x_26);
x_34 = lean_uint64_xor(x_32, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_land(x_35, x_29);
x_37 = lean_array_uget(x_18, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1(x_1, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_17, x_39);
lean_dec(x_17);
lean_inc(x_11);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_11);
lean_ctor_set(x_41, 2, x_37);
x_42 = lean_array_uset(x_18, x_36, x_41);
x_43 = lean_unsigned_to_nat(4u);
x_44 = lean_nat_mul(x_40, x_43);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_nat_div(x_44, x_45);
lean_dec(x_44);
x_47 = lean_array_get_size(x_42);
x_48 = lean_nat_dec_le(x_46, x_47);
lean_dec(x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_importModulesUsingCache___spec__3(x_42);
if (lean_is_scalar(x_19)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_19;
}
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_st_ref_set(x_13, x_50, x_16);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
lean_ctor_set(x_51, 0, x_11);
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_11);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
if (lean_is_scalar(x_19)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_19;
}
lean_ctor_set(x_56, 0, x_40);
lean_ctor_set(x_56, 1, x_42);
x_57 = lean_st_ref_set(x_13, x_56, x_16);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_11);
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_11);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = lean_box(0);
x_63 = lean_array_uset(x_18, x_36, x_62);
lean_inc(x_11);
x_64 = l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(x_1, x_11, x_37);
x_65 = lean_array_uset(x_63, x_36, x_64);
if (lean_is_scalar(x_19)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_19;
}
lean_ctor_set(x_66, 0, x_17);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_st_ref_set(x_13, x_66, x_16);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
lean_ctor_set(x_67, 0, x_11);
return x_67;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_11);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_10);
if (x_77 == 0)
{
return x_10;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_10, 0);
x_79 = lean_ctor_get(x_10, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_10);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_10 = l_Lean_PersistentArray_forMAux___at_Lake_elabConfigFile___spec__3(x_1, x_9, x_6, x_7);
lean_dec(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_13;
x_6 = x_14;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_27 = x_11;
} else {
 lean_dec_ref(x_11);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_6);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_10 = lean_apply_3(x_1, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_13;
x_6 = x_14;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_27 = x_11;
} else {
 lean_dec_ref(x_11);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_6);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_elabConfigFile___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_6, x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__4(x_1, x_5, x_16, x_17, x_18, x_3, x_4);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_array_get_size(x_20);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_4);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_21, x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_21);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_3);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_4);
return x_30;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_31 = 0;
x_32 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_33 = lean_box(0);
x_34 = l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__5(x_1, x_20, x_31, x_32, x_33, x_3, x_4);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_10 = lean_apply_3(x_1, x_9, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = 1;
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_5 = x_13;
x_6 = x_14;
x_7 = x_12;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_10, 0, x_23);
return x_10;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_27 = x_11;
} else {
 lean_dec_ref(x_11);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_5);
lean_ctor_set(x_34, 1, x_6);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_7);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_elabConfigFile___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_6 = l_Lean_PersistentArray_forMAux___at_Lake_elabConfigFile___spec__3(x_1, x_5, x_3, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_7, 1);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_7, 0, x_18);
return x_6;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_le(x_15, x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_1);
x_20 = lean_box(0);
lean_ctor_set(x_7, 0, x_20);
return x_6;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_7);
lean_free_object(x_6);
x_21 = 0;
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = lean_box(0);
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__6(x_1, x_14, x_21, x_22, x_23, x_12, x_9);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_array_get_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
lean_ctor_set(x_6, 0, x_31);
return x_6;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_27, x_27);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_1);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_25);
lean_ctor_set(x_6, 0, x_34);
return x_6;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_6);
x_35 = 0;
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = lean_box(0);
x_38 = l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__6(x_1, x_26, x_35, x_36, x_37, x_25, x_9);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_39 = lean_ctor_get(x_6, 1);
lean_inc(x_39);
lean_dec(x_6);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_41 = x_7;
} else {
 lean_dec_ref(x_7);
 x_41 = lean_box(0);
}
x_42 = lean_ctor_get(x_2, 1);
x_43 = lean_array_get_size(x_42);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_43);
lean_dec(x_1);
x_46 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_41;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_40);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_39);
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_43, x_43);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_43);
lean_dec(x_1);
x_50 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_41;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_40);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_39);
return x_52;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_41);
x_53 = 0;
x_54 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_55 = lean_box(0);
x_56 = l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__6(x_1, x_42, x_53, x_54, x_55, x_40, x_39);
return x_56;
}
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_6);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_6, 0);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_7);
if (x_59 == 0)
{
return x_6;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_7, 0);
x_61 = lean_ctor_get(x_7, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_7);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
lean_ctor_set(x_6, 0, x_62);
return x_6;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_6, 1);
lean_inc(x_63);
lean_dec(x_6);
x_64 = lean_ctor_get(x_7, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_7, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_66 = x_7;
} else {
 lean_dec_ref(x_7);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_6);
if (x_69 == 0)
{
return x_6;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_6, 0);
x_71 = lean_ctor_get(x_6, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_6);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_elabConfigFile___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_PersistentArray_forM___at_Lake_elabConfigFile___spec__2(x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_elabConfigFile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*5 + 2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_LogEntry_ofMessage(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_array_push(x_2, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_array_push(x_2, x_11);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
return x_5;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_5, 0);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_5);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_3);
return x_23;
}
}
}
static lean_object* _init_l_Lake_elabConfigFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_elabConfigFile___lambda__1), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_elabConfigFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": package configuration has errors", 34, 34);
return x_1;
}
}
static lean_object* _init_l_Lake_elabConfigFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_dirExt;
return x_1;
}
}
static lean_object* _init_l_Lake_elabConfigFile___closed__4() {
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
lean_object* x_7; lean_object* x_8; lean_object* x_76; lean_object* x_77; lean_object* x_283; 
x_283 = l_IO_FS_readFile(x_4, x_6);
if (lean_obj_tag(x_283) == 0)
{
uint8_t x_284; 
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_283, 1);
lean_ctor_set(x_283, 1, x_5);
x_76 = x_283;
x_77 = x_285;
goto block_282;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_283, 0);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_283);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_5);
x_76 = x_288;
x_77 = x_287;
goto block_282;
}
}
else
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_283);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_290 = lean_ctor_get(x_283, 0);
x_291 = lean_ctor_get(x_283, 1);
x_292 = lean_io_error_to_string(x_290);
x_293 = 3;
x_294 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set_uint8(x_294, sizeof(void*)*1, x_293);
x_295 = lean_array_get_size(x_5);
x_296 = lean_array_push(x_5, x_294);
lean_ctor_set(x_283, 1, x_296);
lean_ctor_set(x_283, 0, x_295);
x_76 = x_283;
x_77 = x_291;
goto block_282;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_297 = lean_ctor_get(x_283, 0);
x_298 = lean_ctor_get(x_283, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_283);
x_299 = lean_io_error_to_string(x_297);
x_300 = 3;
x_301 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set_uint8(x_301, sizeof(void*)*1, x_300);
x_302 = lean_array_get_size(x_5);
x_303 = lean_array_push(x_5, x_301);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_76 = x_304;
x_77 = x_298;
goto block_282;
}
}
block_75:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_14 = l_Lake_elabConfigFile___closed__1;
x_15 = l_Lean_MessageLog_forM___at_Lake_elabConfigFile___spec__1(x_13, x_14, x_11, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_16, 1);
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = l_Lean_MessageLog_hasErrors(x_13);
lean_dec(x_13);
if (x_22 == 0)
{
lean_dec(x_4);
lean_ctor_set(x_16, 0, x_12);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
x_23 = l_Lake_processHeader___closed__1;
x_24 = lean_string_append(x_23, x_4);
lean_dec(x_4);
x_25 = l_Lake_elabConfigFile___closed__2;
x_26 = lean_string_append(x_24, x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_20);
x_30 = lean_array_push(x_20, x_28);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_30);
lean_ctor_set(x_16, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = l_Lean_MessageLog_hasErrors(x_13);
lean_dec(x_13);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_4);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_15, 0, x_33);
return x_15;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
x_34 = l_Lake_processHeader___closed__1;
x_35 = lean_string_append(x_34, x_4);
lean_dec(x_4);
x_36 = l_Lake_elabConfigFile___closed__2;
x_37 = lean_string_append(x_35, x_36);
x_38 = 3;
x_39 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_38);
x_40 = lean_array_get_size(x_31);
x_41 = lean_array_push(x_31, x_39);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_15, 0, x_42);
return x_15;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_15, 1);
lean_inc(x_43);
lean_dec(x_15);
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
x_46 = l_Lean_MessageLog_hasErrors(x_13);
lean_dec(x_13);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_4);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_12);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_12);
x_49 = l_Lake_processHeader___closed__1;
x_50 = lean_string_append(x_49, x_4);
lean_dec(x_4);
x_51 = l_Lake_elabConfigFile___closed__2;
x_52 = lean_string_append(x_50, x_51);
x_53 = 3;
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_53);
x_55 = lean_array_get_size(x_44);
x_56 = lean_array_push(x_44, x_54);
if (lean_is_scalar(x_45)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_45;
 lean_ctor_set_tag(x_57, 1);
}
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_43);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_15);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_15, 0);
lean_dec(x_60);
x_61 = !lean_is_exclusive(x_16);
if (x_61 == 0)
{
return x_15;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_16, 0);
x_63 = lean_ctor_get(x_16, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_16);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_15, 0, x_64);
return x_15;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_dec(x_15);
x_66 = lean_ctor_get(x_16, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_68 = x_16;
} else {
 lean_dec_ref(x_16);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_15);
if (x_71 == 0)
{
return x_15;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_15, 0);
x_73 = lean_ctor_get(x_15, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_15);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
block_282:
{
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_196; 
x_79 = lean_ctor_get(x_76, 0);
x_80 = lean_ctor_get(x_76, 1);
x_81 = 1;
lean_inc(x_4);
x_82 = l_Lean_Parser_mkInputContext(x_79, x_4, x_81);
lean_inc(x_82);
x_196 = l_Lean_Parser_parseHeader(x_82, x_77);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
lean_ctor_set(x_76, 0, x_197);
x_83 = x_76;
x_84 = x_198;
goto block_195;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_199 = lean_ctor_get(x_196, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
lean_dec(x_196);
x_201 = lean_io_error_to_string(x_199);
x_202 = 3;
x_203 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set_uint8(x_203, sizeof(void*)*1, x_202);
x_204 = lean_array_get_size(x_80);
x_205 = lean_array_push(x_80, x_203);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 1, x_205);
lean_ctor_set(x_76, 0, x_204);
x_83 = x_76;
x_84 = x_200;
goto block_195;
}
block_195:
{
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_136; 
x_88 = lean_ctor_get(x_83, 1);
x_89 = lean_ctor_get(x_83, 0);
lean_dec(x_89);
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_86, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_93 = x_86;
} else {
 lean_dec_ref(x_86);
 x_93 = lean_box(0);
}
lean_inc(x_82);
lean_inc(x_3);
x_136 = l_Lake_processHeader(x_90, x_3, x_82, x_92, x_84);
lean_dec(x_90);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
lean_ctor_set(x_83, 0, x_137);
x_94 = x_83;
x_95 = x_138;
goto block_135;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
lean_dec(x_136);
x_141 = lean_io_error_to_string(x_139);
x_142 = 3;
x_143 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set_uint8(x_143, sizeof(void*)*1, x_142);
x_144 = lean_array_get_size(x_88);
x_145 = lean_array_push(x_88, x_143);
lean_ctor_set_tag(x_83, 1);
lean_ctor_set(x_83, 1, x_145);
lean_ctor_set(x_83, 0, x_144);
x_94 = x_83;
x_95 = x_140;
goto block_135;
}
block_135:
{
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_96; 
lean_dec(x_93);
x_96 = !lean_is_exclusive(x_94);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_97 = lean_ctor_get(x_94, 0);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lake_configModuleName;
x_101 = l_Lean_Environment_setMainModule(x_98, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_1);
x_103 = l_Lake_elabConfigFile___closed__3;
x_104 = l_Lean_EnvExtension_setState___rarg(x_103, x_101, x_102);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_2);
x_106 = l_Lake_elabConfigFile___closed__4;
x_107 = l_Lean_EnvExtension_setState___rarg(x_106, x_104, x_105);
x_108 = l_Lean_Elab_Command_mkState(x_107, x_99, x_3);
x_109 = l_Lean_Elab_IO_processCommands(x_82, x_91, x_108, x_95);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_ctor_set(x_94, 0, x_110);
x_7 = x_94;
x_8 = x_111;
goto block_75;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_112 = lean_ctor_get(x_94, 0);
x_113 = lean_ctor_get(x_94, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_94);
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
x_116 = l_Lake_configModuleName;
x_117 = l_Lean_Environment_setMainModule(x_114, x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_1);
x_119 = l_Lake_elabConfigFile___closed__3;
x_120 = l_Lean_EnvExtension_setState___rarg(x_119, x_117, x_118);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_2);
x_122 = l_Lake_elabConfigFile___closed__4;
x_123 = l_Lean_EnvExtension_setState___rarg(x_122, x_120, x_121);
x_124 = l_Lean_Elab_Command_mkState(x_123, x_115, x_3);
x_125 = l_Lean_Elab_IO_processCommands(x_82, x_91, x_124, x_95);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_113);
x_7 = x_128;
x_8 = x_127;
goto block_75;
}
}
else
{
uint8_t x_129; 
lean_dec(x_91);
lean_dec(x_82);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_94);
if (x_129 == 0)
{
lean_object* x_130; 
if (lean_is_scalar(x_93)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_93;
}
lean_ctor_set(x_130, 0, x_94);
lean_ctor_set(x_130, 1, x_95);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_94, 0);
x_132 = lean_ctor_get(x_94, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_94);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_93)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_93;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_95);
return x_134;
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_177; 
x_146 = lean_ctor_get(x_83, 1);
lean_inc(x_146);
lean_dec(x_83);
x_147 = lean_ctor_get(x_85, 0);
lean_inc(x_147);
lean_dec(x_85);
x_148 = lean_ctor_get(x_86, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_86, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_150 = x_86;
} else {
 lean_dec_ref(x_86);
 x_150 = lean_box(0);
}
lean_inc(x_82);
lean_inc(x_3);
x_177 = l_Lake_processHeader(x_147, x_3, x_82, x_149, x_84);
lean_dec(x_147);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_177, 1);
lean_inc(x_179);
lean_dec(x_177);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_146);
x_151 = x_180;
x_152 = x_179;
goto block_176;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_ctor_get(x_177, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 1);
lean_inc(x_182);
lean_dec(x_177);
x_183 = lean_io_error_to_string(x_181);
x_184 = 3;
x_185 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set_uint8(x_185, sizeof(void*)*1, x_184);
x_186 = lean_array_get_size(x_146);
x_187 = lean_array_push(x_146, x_185);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_151 = x_188;
x_152 = x_182;
goto block_176;
}
block_176:
{
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_150);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_151, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_155 = x_151;
} else {
 lean_dec_ref(x_151);
 x_155 = lean_box(0);
}
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_dec(x_153);
x_158 = l_Lake_configModuleName;
x_159 = l_Lean_Environment_setMainModule(x_156, x_158);
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_1);
x_161 = l_Lake_elabConfigFile___closed__3;
x_162 = l_Lean_EnvExtension_setState___rarg(x_161, x_159, x_160);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_2);
x_164 = l_Lake_elabConfigFile___closed__4;
x_165 = l_Lean_EnvExtension_setState___rarg(x_164, x_162, x_163);
x_166 = l_Lean_Elab_Command_mkState(x_165, x_157, x_3);
x_167 = l_Lean_Elab_IO_processCommands(x_82, x_148, x_166, x_152);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
if (lean_is_scalar(x_155)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_155;
}
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_154);
x_7 = x_170;
x_8 = x_169;
goto block_75;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_148);
lean_dec(x_82);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_151, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_151, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_173 = x_151;
} else {
 lean_dec_ref(x_151);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
if (lean_is_scalar(x_150)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_150;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_152);
return x_175;
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_82);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_83);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_83);
lean_ctor_set(x_190, 1, x_84);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_191 = lean_ctor_get(x_83, 0);
x_192 = lean_ctor_get(x_83, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_83);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_84);
return x_194;
}
}
}
}
else
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_264; 
x_206 = lean_ctor_get(x_76, 0);
x_207 = lean_ctor_get(x_76, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_76);
x_208 = 1;
lean_inc(x_4);
x_209 = l_Lean_Parser_mkInputContext(x_206, x_4, x_208);
lean_inc(x_209);
x_264 = l_Lean_Parser_parseHeader(x_209, x_77);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_265);
lean_ctor_set(x_267, 1, x_207);
x_210 = x_267;
x_211 = x_266;
goto block_263;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_268 = lean_ctor_get(x_264, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_264, 1);
lean_inc(x_269);
lean_dec(x_264);
x_270 = lean_io_error_to_string(x_268);
x_271 = 3;
x_272 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set_uint8(x_272, sizeof(void*)*1, x_271);
x_273 = lean_array_get_size(x_207);
x_274 = lean_array_push(x_207, x_272);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
x_210 = x_275;
x_211 = x_269;
goto block_263;
}
block_263:
{
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_246; 
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_215 = x_210;
} else {
 lean_dec_ref(x_210);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_212, 0);
lean_inc(x_216);
lean_dec(x_212);
x_217 = lean_ctor_get(x_213, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_213, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_219 = x_213;
} else {
 lean_dec_ref(x_213);
 x_219 = lean_box(0);
}
lean_inc(x_209);
lean_inc(x_3);
x_246 = l_Lake_processHeader(x_216, x_3, x_209, x_218, x_211);
lean_dec(x_216);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
if (lean_is_scalar(x_215)) {
 x_249 = lean_alloc_ctor(0, 2, 0);
} else {
 x_249 = x_215;
}
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_214);
x_220 = x_249;
x_221 = x_248;
goto block_245;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_250 = lean_ctor_get(x_246, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_246, 1);
lean_inc(x_251);
lean_dec(x_246);
x_252 = lean_io_error_to_string(x_250);
x_253 = 3;
x_254 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set_uint8(x_254, sizeof(void*)*1, x_253);
x_255 = lean_array_get_size(x_214);
x_256 = lean_array_push(x_214, x_254);
if (lean_is_scalar(x_215)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_215;
 lean_ctor_set_tag(x_257, 1);
}
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_220 = x_257;
x_221 = x_251;
goto block_245;
}
block_245:
{
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_219);
x_222 = lean_ctor_get(x_220, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_224 = x_220;
} else {
 lean_dec_ref(x_220);
 x_224 = lean_box(0);
}
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = l_Lake_configModuleName;
x_228 = l_Lean_Environment_setMainModule(x_225, x_227);
x_229 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_229, 0, x_1);
x_230 = l_Lake_elabConfigFile___closed__3;
x_231 = l_Lean_EnvExtension_setState___rarg(x_230, x_228, x_229);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_2);
x_233 = l_Lake_elabConfigFile___closed__4;
x_234 = l_Lean_EnvExtension_setState___rarg(x_233, x_231, x_232);
x_235 = l_Lean_Elab_Command_mkState(x_234, x_226, x_3);
x_236 = l_Lean_Elab_IO_processCommands(x_209, x_217, x_235, x_221);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
if (lean_is_scalar(x_224)) {
 x_239 = lean_alloc_ctor(0, 2, 0);
} else {
 x_239 = x_224;
}
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_223);
x_7 = x_239;
x_8 = x_238;
goto block_75;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_217);
lean_dec(x_209);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_240 = lean_ctor_get(x_220, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_220, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_242 = x_220;
} else {
 lean_dec_ref(x_220);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(1, 2, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
if (lean_is_scalar(x_219)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_219;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_221);
return x_244;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_209);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_258 = lean_ctor_get(x_210, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_210, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_260 = x_210;
} else {
 lean_dec_ref(x_210);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_211);
return x_262;
}
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_76);
if (x_276 == 0)
{
lean_object* x_277; 
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_76);
lean_ctor_set(x_277, 1, x_77);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_278 = lean_ctor_get(x_76, 0);
x_279 = lean_ctor_get(x_76, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_76);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_77);
return x_281;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__4(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__5(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_elabConfigFile___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forMAux___at_Lake_elabConfigFile___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_elabConfigFile___spec__6(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_elabConfigFile___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forM___at_Lake_elabConfigFile___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_elabConfigFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageLog_forM___at_Lake_elabConfigFile___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
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
x_4 = l_Lean_readModuleData(x_1, x_3);
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
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("platform", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanHash", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("configHash", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("options", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(lean_object* x_1) {
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
x_7 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_3);
x_12 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__2;
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
x_18 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__3;
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
x_24 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__4;
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
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_), 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___lambda__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_cstr_to_nat("18446744073709551616");
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value '{j}' is too large for `UInt64`", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__1;
x_10 = lean_nat_dec_le(x_9, x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_box(0);
x_12 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___lambda__1(x_8, x_11);
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
x_16 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__3;
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ConfigTrace", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_importConfigFileCore_lakeExts___closed__1;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__2;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__4;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__5;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__7;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__6;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__8;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__9;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__13() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__12;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__6;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__13;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__14;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__17() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__16;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__6;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__17;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__18;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__21() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__20;
x_2 = 1;
x_3 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3;
x_4 = l_Lean_Name_toString(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__6;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__21;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__22;
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__10;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__1;
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
x_6 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__11;
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
x_9 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__11;
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
x_13 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__2;
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
x_17 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__15;
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
x_20 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__15;
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
x_24 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__3;
lean_inc(x_1);
x_25 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1(x_1, x_24);
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
x_28 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__19;
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
x_31 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__19;
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
x_35 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__4;
x_36 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__2(x_1, x_35);
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
x_39 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__23;
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
x_42 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__23;
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
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instFromJsonConfigTrace___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950_), 1, 0);
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
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 6);
lean_inc(x_4);
lean_inc(x_4);
x_5 = l_System_FilePath_fileName(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_1);
x_6 = lean_array_get_size(x_2);
x_7 = l_Lake_importConfigFile___closed__2;
x_8 = lean_array_push(x_2, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_2123; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 x_12 = x_5;
} else {
 lean_dec_ref(x_5);
 x_12 = lean_box(0);
}
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
x_14 = l_Lake_defaultLakeDir;
lean_inc(x_13);
x_15 = l_Lake_joinRelative(x_13, x_14);
x_16 = l_Lake_importConfigFile___closed__3;
lean_inc(x_11);
x_17 = l_System_FilePath_withExtension(x_11, x_16);
lean_inc(x_15);
x_18 = l_Lake_joinRelative(x_15, x_17);
lean_dec(x_17);
x_19 = l_Lake_importConfigFile___closed__4;
lean_inc(x_11);
x_20 = l_System_FilePath_withExtension(x_11, x_19);
lean_inc(x_15);
x_21 = l_Lake_joinRelative(x_15, x_20);
lean_dec(x_20);
x_22 = l_Lake_importConfigFile___closed__5;
x_23 = l_System_FilePath_withExtension(x_11, x_22);
lean_inc(x_15);
x_24 = l_Lake_joinRelative(x_15, x_23);
lean_dec(x_23);
x_2123 = l_Lake_computeTextFileHash(x_4, x_3);
if (lean_obj_tag(x_2123) == 0)
{
uint8_t x_2124; 
x_2124 = !lean_is_exclusive(x_2123);
if (x_2124 == 0)
{
lean_object* x_2125; 
x_2125 = lean_ctor_get(x_2123, 1);
lean_ctor_set(x_2123, 1, x_2);
x_25 = x_2123;
x_26 = x_2125;
goto block_2122;
}
else
{
lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; 
x_2126 = lean_ctor_get(x_2123, 0);
x_2127 = lean_ctor_get(x_2123, 1);
lean_inc(x_2127);
lean_inc(x_2126);
lean_dec(x_2123);
x_2128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2128, 0, x_2126);
lean_ctor_set(x_2128, 1, x_2);
x_25 = x_2128;
x_26 = x_2127;
goto block_2122;
}
}
else
{
uint8_t x_2129; 
x_2129 = !lean_is_exclusive(x_2123);
if (x_2129 == 0)
{
lean_object* x_2130; lean_object* x_2131; lean_object* x_2132; uint8_t x_2133; lean_object* x_2134; lean_object* x_2135; lean_object* x_2136; 
x_2130 = lean_ctor_get(x_2123, 0);
x_2131 = lean_ctor_get(x_2123, 1);
x_2132 = lean_io_error_to_string(x_2130);
x_2133 = 3;
x_2134 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2134, 0, x_2132);
lean_ctor_set_uint8(x_2134, sizeof(void*)*1, x_2133);
x_2135 = lean_array_get_size(x_2);
x_2136 = lean_array_push(x_2, x_2134);
lean_ctor_set(x_2123, 1, x_2136);
lean_ctor_set(x_2123, 0, x_2135);
x_25 = x_2123;
x_26 = x_2131;
goto block_2122;
}
else
{
lean_object* x_2137; lean_object* x_2138; lean_object* x_2139; uint8_t x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; 
x_2137 = lean_ctor_get(x_2123, 0);
x_2138 = lean_ctor_get(x_2123, 1);
lean_inc(x_2138);
lean_inc(x_2137);
lean_dec(x_2123);
x_2139 = lean_io_error_to_string(x_2137);
x_2140 = 3;
x_2141 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2141, 0, x_2139);
lean_ctor_set_uint8(x_2141, sizeof(void*)*1, x_2140);
x_2142 = lean_array_get_size(x_2);
x_2143 = lean_array_push(x_2, x_2141);
x_2144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2144, 0, x_2142);
lean_ctor_set(x_2144, 1, x_2143);
x_25 = x_2144;
x_26 = x_2138;
goto block_2122;
}
}
block_2122:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_527; lean_object* x_528; lean_object* x_1272; lean_object* x_1273; lean_object* x_2026; lean_object* x_2027; uint8_t x_2028; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_29 = x_25;
} else {
 lean_dec_ref(x_25);
 x_29 = lean_box(0);
}
x_2026 = l_System_FilePath_pathExists(x_21, x_26);
x_2027 = lean_ctor_get(x_2026, 0);
lean_inc(x_2027);
x_2028 = lean_unbox(x_2027);
lean_dec(x_2027);
if (x_2028 == 0)
{
uint8_t x_2029; 
x_2029 = !lean_is_exclusive(x_2026);
if (x_2029 == 0)
{
lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; 
x_2030 = lean_ctor_get(x_2026, 1);
x_2031 = lean_ctor_get(x_2026, 0);
lean_dec(x_2031);
x_2032 = l_IO_FS_createDirAll(x_15, x_2030);
lean_dec(x_15);
if (lean_obj_tag(x_2032) == 0)
{
lean_object* x_2033; uint8_t x_2034; lean_object* x_2035; 
lean_free_object(x_2026);
x_2033 = lean_ctor_get(x_2032, 1);
lean_inc(x_2033);
lean_dec(x_2032);
x_2034 = 2;
x_2035 = lean_io_prim_handle_mk(x_21, x_2034, x_2033);
if (lean_obj_tag(x_2035) == 0)
{
uint8_t x_2036; 
x_2036 = !lean_is_exclusive(x_2035);
if (x_2036 == 0)
{
lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; 
x_2037 = lean_ctor_get(x_2035, 0);
x_2038 = lean_ctor_get(x_2035, 1);
x_2039 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2039, 0, x_2037);
lean_ctor_set(x_2035, 1, x_28);
lean_ctor_set(x_2035, 0, x_2039);
x_1272 = x_2035;
x_1273 = x_2038;
goto block_2025;
}
else
{
lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; 
x_2040 = lean_ctor_get(x_2035, 0);
x_2041 = lean_ctor_get(x_2035, 1);
lean_inc(x_2041);
lean_inc(x_2040);
lean_dec(x_2035);
x_2042 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2042, 0, x_2040);
x_2043 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2043, 0, x_2042);
lean_ctor_set(x_2043, 1, x_28);
x_1272 = x_2043;
x_1273 = x_2041;
goto block_2025;
}
}
else
{
uint8_t x_2044; 
x_2044 = !lean_is_exclusive(x_2035);
if (x_2044 == 0)
{
lean_object* x_2045; lean_object* x_2046; lean_object* x_2047; 
x_2045 = lean_ctor_get(x_2035, 0);
x_2046 = lean_ctor_get(x_2035, 1);
x_2047 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2047, 0, x_2045);
lean_ctor_set_tag(x_2035, 0);
lean_ctor_set(x_2035, 1, x_28);
lean_ctor_set(x_2035, 0, x_2047);
x_1272 = x_2035;
x_1273 = x_2046;
goto block_2025;
}
else
{
lean_object* x_2048; lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; 
x_2048 = lean_ctor_get(x_2035, 0);
x_2049 = lean_ctor_get(x_2035, 1);
lean_inc(x_2049);
lean_inc(x_2048);
lean_dec(x_2035);
x_2050 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2050, 0, x_2048);
x_2051 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2051, 0, x_2050);
lean_ctor_set(x_2051, 1, x_28);
x_1272 = x_2051;
x_1273 = x_2049;
goto block_2025;
}
}
}
else
{
uint8_t x_2052; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_2052 = !lean_is_exclusive(x_2032);
if (x_2052 == 0)
{
lean_object* x_2053; lean_object* x_2054; uint8_t x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; 
x_2053 = lean_ctor_get(x_2032, 0);
x_2054 = lean_io_error_to_string(x_2053);
x_2055 = 3;
x_2056 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2056, 0, x_2054);
lean_ctor_set_uint8(x_2056, sizeof(void*)*1, x_2055);
x_2057 = lean_array_get_size(x_28);
x_2058 = lean_array_push(x_28, x_2056);
lean_ctor_set_tag(x_2026, 1);
lean_ctor_set(x_2026, 1, x_2058);
lean_ctor_set(x_2026, 0, x_2057);
lean_ctor_set_tag(x_2032, 0);
lean_ctor_set(x_2032, 0, x_2026);
return x_2032;
}
else
{
lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; uint8_t x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; 
x_2059 = lean_ctor_get(x_2032, 0);
x_2060 = lean_ctor_get(x_2032, 1);
lean_inc(x_2060);
lean_inc(x_2059);
lean_dec(x_2032);
x_2061 = lean_io_error_to_string(x_2059);
x_2062 = 3;
x_2063 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2063, 0, x_2061);
lean_ctor_set_uint8(x_2063, sizeof(void*)*1, x_2062);
x_2064 = lean_array_get_size(x_28);
x_2065 = lean_array_push(x_28, x_2063);
lean_ctor_set_tag(x_2026, 1);
lean_ctor_set(x_2026, 1, x_2065);
lean_ctor_set(x_2026, 0, x_2064);
x_2066 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2066, 0, x_2026);
lean_ctor_set(x_2066, 1, x_2060);
return x_2066;
}
}
}
else
{
lean_object* x_2067; lean_object* x_2068; 
x_2067 = lean_ctor_get(x_2026, 1);
lean_inc(x_2067);
lean_dec(x_2026);
x_2068 = l_IO_FS_createDirAll(x_15, x_2067);
lean_dec(x_15);
if (lean_obj_tag(x_2068) == 0)
{
lean_object* x_2069; uint8_t x_2070; lean_object* x_2071; 
x_2069 = lean_ctor_get(x_2068, 1);
lean_inc(x_2069);
lean_dec(x_2068);
x_2070 = 2;
x_2071 = lean_io_prim_handle_mk(x_21, x_2070, x_2069);
if (lean_obj_tag(x_2071) == 0)
{
lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; 
x_2072 = lean_ctor_get(x_2071, 0);
lean_inc(x_2072);
x_2073 = lean_ctor_get(x_2071, 1);
lean_inc(x_2073);
if (lean_is_exclusive(x_2071)) {
 lean_ctor_release(x_2071, 0);
 lean_ctor_release(x_2071, 1);
 x_2074 = x_2071;
} else {
 lean_dec_ref(x_2071);
 x_2074 = lean_box(0);
}
x_2075 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2075, 0, x_2072);
if (lean_is_scalar(x_2074)) {
 x_2076 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2076 = x_2074;
}
lean_ctor_set(x_2076, 0, x_2075);
lean_ctor_set(x_2076, 1, x_28);
x_1272 = x_2076;
x_1273 = x_2073;
goto block_2025;
}
else
{
lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; 
x_2077 = lean_ctor_get(x_2071, 0);
lean_inc(x_2077);
x_2078 = lean_ctor_get(x_2071, 1);
lean_inc(x_2078);
if (lean_is_exclusive(x_2071)) {
 lean_ctor_release(x_2071, 0);
 lean_ctor_release(x_2071, 1);
 x_2079 = x_2071;
} else {
 lean_dec_ref(x_2071);
 x_2079 = lean_box(0);
}
x_2080 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2080, 0, x_2077);
if (lean_is_scalar(x_2079)) {
 x_2081 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2081 = x_2079;
 lean_ctor_set_tag(x_2081, 0);
}
lean_ctor_set(x_2081, 0, x_2080);
lean_ctor_set(x_2081, 1, x_28);
x_1272 = x_2081;
x_1273 = x_2078;
goto block_2025;
}
}
else
{
lean_object* x_2082; lean_object* x_2083; lean_object* x_2084; lean_object* x_2085; uint8_t x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_2082 = lean_ctor_get(x_2068, 0);
lean_inc(x_2082);
x_2083 = lean_ctor_get(x_2068, 1);
lean_inc(x_2083);
if (lean_is_exclusive(x_2068)) {
 lean_ctor_release(x_2068, 0);
 lean_ctor_release(x_2068, 1);
 x_2084 = x_2068;
} else {
 lean_dec_ref(x_2068);
 x_2084 = lean_box(0);
}
x_2085 = lean_io_error_to_string(x_2082);
x_2086 = 3;
x_2087 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2087, 0, x_2085);
lean_ctor_set_uint8(x_2087, sizeof(void*)*1, x_2086);
x_2088 = lean_array_get_size(x_28);
x_2089 = lean_array_push(x_28, x_2087);
x_2090 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2090, 0, x_2088);
lean_ctor_set(x_2090, 1, x_2089);
if (lean_is_scalar(x_2084)) {
 x_2091 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2091 = x_2084;
 lean_ctor_set_tag(x_2091, 0);
}
lean_ctor_set(x_2091, 0, x_2090);
lean_ctor_set(x_2091, 1, x_2083);
return x_2091;
}
}
}
else
{
lean_object* x_2092; uint8_t x_2093; lean_object* x_2094; 
lean_dec(x_15);
x_2092 = lean_ctor_get(x_2026, 1);
lean_inc(x_2092);
lean_dec(x_2026);
x_2093 = 0;
x_2094 = lean_io_prim_handle_mk(x_21, x_2093, x_2092);
if (lean_obj_tag(x_2094) == 0)
{
uint8_t x_2095; 
x_2095 = !lean_is_exclusive(x_2094);
if (x_2095 == 0)
{
lean_object* x_2096; 
x_2096 = lean_ctor_get(x_2094, 1);
lean_ctor_set(x_2094, 1, x_28);
x_527 = x_2094;
x_528 = x_2096;
goto block_1271;
}
else
{
lean_object* x_2097; lean_object* x_2098; lean_object* x_2099; 
x_2097 = lean_ctor_get(x_2094, 0);
x_2098 = lean_ctor_get(x_2094, 1);
lean_inc(x_2098);
lean_inc(x_2097);
lean_dec(x_2094);
x_2099 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2099, 0, x_2097);
lean_ctor_set(x_2099, 1, x_28);
x_527 = x_2099;
x_528 = x_2098;
goto block_1271;
}
}
else
{
uint8_t x_2100; 
x_2100 = !lean_is_exclusive(x_2094);
if (x_2100 == 0)
{
lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; uint8_t x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; 
x_2101 = lean_ctor_get(x_2094, 0);
x_2102 = lean_ctor_get(x_2094, 1);
x_2103 = lean_io_error_to_string(x_2101);
x_2104 = 3;
x_2105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2105, 0, x_2103);
lean_ctor_set_uint8(x_2105, sizeof(void*)*1, x_2104);
x_2106 = lean_array_get_size(x_28);
x_2107 = lean_array_push(x_28, x_2105);
lean_ctor_set(x_2094, 1, x_2107);
lean_ctor_set(x_2094, 0, x_2106);
x_527 = x_2094;
x_528 = x_2102;
goto block_1271;
}
else
{
lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; uint8_t x_2111; lean_object* x_2112; lean_object* x_2113; lean_object* x_2114; lean_object* x_2115; 
x_2108 = lean_ctor_get(x_2094, 0);
x_2109 = lean_ctor_get(x_2094, 1);
lean_inc(x_2109);
lean_inc(x_2108);
lean_dec(x_2094);
x_2110 = lean_io_error_to_string(x_2108);
x_2111 = 3;
x_2112 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2112, 0, x_2110);
lean_ctor_set_uint8(x_2112, sizeof(void*)*1, x_2111);
x_2113 = lean_array_get_size(x_28);
x_2114 = lean_array_push(x_28, x_2112);
x_2115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2115, 0, x_2113);
lean_ctor_set(x_2115, 1, x_2114);
x_527 = x_2115;
x_528 = x_2109;
goto block_1271;
}
}
}
block_526:
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_136; lean_object* x_137; lean_object* x_345; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_1, 8);
lean_inc(x_34);
x_345 = lean_io_remove_file(x_18, x_31);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
if (lean_is_scalar(x_12)) {
 x_348 = lean_alloc_ctor(1, 1, 0);
} else {
 x_348 = x_12;
}
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_30, 0, x_348);
x_136 = x_30;
x_137 = x_347;
goto block_344;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_345, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_345, 1);
lean_inc(x_350);
lean_dec(x_345);
if (lean_is_scalar(x_12)) {
 x_351 = lean_alloc_ctor(0, 1, 0);
} else {
 x_351 = x_12;
 lean_ctor_set_tag(x_351, 0);
}
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_30, 0, x_351);
x_136 = x_30;
x_137 = x_350;
goto block_344;
}
block_135:
{
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_1, 9);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lake_elabConfigFile(x_13, x_34, x_38, x_4, x_37, x_36);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
x_45 = 0;
lean_inc(x_43);
x_46 = lean_write_module(x_43, x_18, x_45, x_41);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_io_prim_handle_unlock(x_33, x_47);
lean_dec(x_33);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_40);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_43);
x_53 = !lean_is_exclusive(x_48);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_io_error_to_string(x_54);
x_56 = 3;
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_56);
x_58 = lean_array_get_size(x_44);
x_59 = lean_array_push(x_44, x_57);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_59);
lean_ctor_set(x_40, 0, x_58);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_40);
return x_48;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_48, 0);
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_48);
x_62 = lean_io_error_to_string(x_60);
x_63 = 3;
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_63);
x_65 = lean_array_get_size(x_44);
x_66 = lean_array_push(x_44, x_64);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_66);
lean_ctor_set(x_40, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_40);
lean_ctor_set(x_67, 1, x_61);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_43);
lean_dec(x_33);
x_68 = !lean_is_exclusive(x_46);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_46, 0);
x_70 = lean_io_error_to_string(x_69);
x_71 = 3;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_array_get_size(x_44);
x_74 = lean_array_push(x_44, x_72);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_74);
lean_ctor_set(x_40, 0, x_73);
lean_ctor_set_tag(x_46, 0);
lean_ctor_set(x_46, 0, x_40);
return x_46;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_ctor_get(x_46, 0);
x_76 = lean_ctor_get(x_46, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_46);
x_77 = lean_io_error_to_string(x_75);
x_78 = 3;
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_78);
x_80 = lean_array_get_size(x_44);
x_81 = lean_array_push(x_44, x_79);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_81);
lean_ctor_set(x_40, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_40);
lean_ctor_set(x_82, 1, x_76);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_40, 0);
x_84 = lean_ctor_get(x_40, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_40);
x_85 = 0;
lean_inc(x_83);
x_86 = lean_write_module(x_83, x_18, x_85, x_41);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_io_prim_handle_unlock(x_33, x_87);
lean_dec(x_33);
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
lean_ctor_set(x_91, 0, x_83);
lean_ctor_set(x_91, 1, x_84);
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
lean_dec(x_83);
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
x_99 = lean_array_get_size(x_84);
x_100 = lean_array_push(x_84, x_98);
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
lean_dec(x_83);
lean_dec(x_33);
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
x_109 = lean_array_get_size(x_84);
x_110 = lean_array_push(x_84, x_108);
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
lean_dec(x_33);
lean_dec(x_18);
x_113 = !lean_is_exclusive(x_39);
if (x_113 == 0)
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_39, 0);
lean_dec(x_114);
x_115 = !lean_is_exclusive(x_40);
if (x_115 == 0)
{
return x_39;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_40, 0);
x_117 = lean_ctor_get(x_40, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_40);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
lean_ctor_set(x_39, 0, x_118);
return x_39;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_39, 1);
lean_inc(x_119);
lean_dec(x_39);
x_120 = lean_ctor_get(x_40, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_40, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_122 = x_40;
} else {
 lean_dec_ref(x_40);
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
lean_dec(x_33);
lean_dec(x_18);
x_125 = !lean_is_exclusive(x_39);
if (x_125 == 0)
{
return x_39;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_39, 0);
x_127 = lean_ctor_get(x_39, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_39);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_35);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_35);
lean_ctor_set(x_130, 1, x_36);
return x_130;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_35, 0);
x_132 = lean_ctor_get(x_35, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_35);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_36);
return x_134;
}
}
}
block_344:
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
if (lean_obj_tag(x_139) == 11)
{
uint8_t x_140; 
lean_dec(x_139);
lean_dec(x_21);
x_140 = !lean_is_exclusive(x_136);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_141 = lean_ctor_get(x_136, 1);
x_142 = lean_ctor_get(x_136, 0);
lean_dec(x_142);
x_143 = lean_ctor_get(x_1, 0);
lean_inc(x_143);
x_144 = l_Lake_Env_leanGithash(x_143);
lean_dec(x_143);
x_145 = l_System_Platform_target;
lean_inc(x_34);
x_146 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
lean_ctor_set(x_146, 2, x_27);
lean_ctor_set(x_146, 3, x_34);
x_147 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_146);
x_148 = lean_unsigned_to_nat(80u);
x_149 = l_Lean_Json_pretty(x_147, x_148);
x_150 = l_IO_FS_Handle_putStrLn(x_33, x_149, x_137);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_io_prim_handle_truncate(x_33, x_151);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_ctor_set(x_136, 0, x_153);
x_35 = x_136;
x_36 = x_154;
goto block_135;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_152, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_152, 1);
lean_inc(x_156);
lean_dec(x_152);
x_157 = lean_io_error_to_string(x_155);
x_158 = 3;
x_159 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*1, x_158);
x_160 = lean_array_get_size(x_141);
x_161 = lean_array_push(x_141, x_159);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_161);
lean_ctor_set(x_136, 0, x_160);
x_35 = x_136;
x_36 = x_156;
goto block_135;
}
}
else
{
uint8_t x_162; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_162 = !lean_is_exclusive(x_150);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_150, 0);
x_164 = lean_io_error_to_string(x_163);
x_165 = 3;
x_166 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_165);
x_167 = lean_array_get_size(x_141);
x_168 = lean_array_push(x_141, x_166);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_168);
lean_ctor_set(x_136, 0, x_167);
lean_ctor_set_tag(x_150, 0);
lean_ctor_set(x_150, 0, x_136);
return x_150;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_169 = lean_ctor_get(x_150, 0);
x_170 = lean_ctor_get(x_150, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_150);
x_171 = lean_io_error_to_string(x_169);
x_172 = 3;
x_173 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set_uint8(x_173, sizeof(void*)*1, x_172);
x_174 = lean_array_get_size(x_141);
x_175 = lean_array_push(x_141, x_173);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_175);
lean_ctor_set(x_136, 0, x_174);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_136);
lean_ctor_set(x_176, 1, x_170);
return x_176;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_177 = lean_ctor_get(x_136, 1);
lean_inc(x_177);
lean_dec(x_136);
x_178 = lean_ctor_get(x_1, 0);
lean_inc(x_178);
x_179 = l_Lake_Env_leanGithash(x_178);
lean_dec(x_178);
x_180 = l_System_Platform_target;
lean_inc(x_34);
x_181 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
lean_ctor_set(x_181, 2, x_27);
lean_ctor_set(x_181, 3, x_34);
x_182 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_181);
x_183 = lean_unsigned_to_nat(80u);
x_184 = l_Lean_Json_pretty(x_182, x_183);
x_185 = l_IO_FS_Handle_putStrLn(x_33, x_184, x_137);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
x_187 = lean_io_prim_handle_truncate(x_33, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_177);
x_35 = x_190;
x_36 = x_189;
goto block_135;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_191 = lean_ctor_get(x_187, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_187, 1);
lean_inc(x_192);
lean_dec(x_187);
x_193 = lean_io_error_to_string(x_191);
x_194 = 3;
x_195 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*1, x_194);
x_196 = lean_array_get_size(x_177);
x_197 = lean_array_push(x_177, x_195);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_35 = x_198;
x_36 = x_192;
goto block_135;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_199 = lean_ctor_get(x_185, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_185, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_201 = x_185;
} else {
 lean_dec_ref(x_185);
 x_201 = lean_box(0);
}
x_202 = lean_io_error_to_string(x_199);
x_203 = 3;
x_204 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set_uint8(x_204, sizeof(void*)*1, x_203);
x_205 = lean_array_get_size(x_177);
x_206 = lean_array_push(x_177, x_204);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
if (lean_is_scalar(x_201)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_201;
 lean_ctor_set_tag(x_208, 0);
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_200);
return x_208;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_136);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_136, 1);
x_211 = lean_ctor_get(x_136, 0);
lean_dec(x_211);
x_212 = lean_io_error_to_string(x_139);
x_213 = 3;
x_214 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_213);
x_215 = lean_array_get_size(x_210);
x_216 = lean_array_push(x_210, x_214);
x_217 = lean_io_prim_handle_unlock(x_33, x_137);
lean_dec(x_33);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_219 = lean_io_remove_file(x_21, x_218);
lean_dec(x_21);
if (lean_obj_tag(x_219) == 0)
{
uint8_t x_220; 
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; 
x_221 = lean_ctor_get(x_219, 0);
lean_dec(x_221);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_216);
lean_ctor_set(x_136, 0, x_215);
lean_ctor_set(x_219, 0, x_136);
return x_219;
}
else
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_219, 1);
lean_inc(x_222);
lean_dec(x_219);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_216);
lean_ctor_set(x_136, 0, x_215);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_136);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
else
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_219);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_219, 0);
x_226 = lean_io_error_to_string(x_225);
x_227 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set_uint8(x_227, sizeof(void*)*1, x_213);
x_228 = lean_array_push(x_216, x_227);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_228);
lean_ctor_set(x_136, 0, x_215);
lean_ctor_set_tag(x_219, 0);
lean_ctor_set(x_219, 0, x_136);
return x_219;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_229 = lean_ctor_get(x_219, 0);
x_230 = lean_ctor_get(x_219, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_219);
x_231 = lean_io_error_to_string(x_229);
x_232 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_232, 0, x_231);
lean_ctor_set_uint8(x_232, sizeof(void*)*1, x_213);
x_233 = lean_array_push(x_216, x_232);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_233);
lean_ctor_set(x_136, 0, x_215);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_136);
lean_ctor_set(x_234, 1, x_230);
return x_234;
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_21);
x_235 = !lean_is_exclusive(x_217);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_217, 0);
x_237 = lean_io_error_to_string(x_236);
x_238 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set_uint8(x_238, sizeof(void*)*1, x_213);
x_239 = lean_array_push(x_216, x_238);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_239);
lean_ctor_set(x_136, 0, x_215);
lean_ctor_set_tag(x_217, 0);
lean_ctor_set(x_217, 0, x_136);
return x_217;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_240 = lean_ctor_get(x_217, 0);
x_241 = lean_ctor_get(x_217, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_217);
x_242 = lean_io_error_to_string(x_240);
x_243 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set_uint8(x_243, sizeof(void*)*1, x_213);
x_244 = lean_array_push(x_216, x_243);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_244);
lean_ctor_set(x_136, 0, x_215);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_136);
lean_ctor_set(x_245, 1, x_241);
return x_245;
}
}
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_136, 1);
lean_inc(x_246);
lean_dec(x_136);
x_247 = lean_io_error_to_string(x_139);
x_248 = 3;
x_249 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*1, x_248);
x_250 = lean_array_get_size(x_246);
x_251 = lean_array_push(x_246, x_249);
x_252 = lean_io_prim_handle_unlock(x_33, x_137);
lean_dec(x_33);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_io_remove_file(x_21, x_253);
lean_dec(x_21);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_256 = x_254;
} else {
 lean_dec_ref(x_254);
 x_256 = lean_box(0);
}
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_250);
lean_ctor_set(x_257, 1, x_251);
if (lean_is_scalar(x_256)) {
 x_258 = lean_alloc_ctor(0, 2, 0);
} else {
 x_258 = x_256;
}
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_255);
return x_258;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_259 = lean_ctor_get(x_254, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_254, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_261 = x_254;
} else {
 lean_dec_ref(x_254);
 x_261 = lean_box(0);
}
x_262 = lean_io_error_to_string(x_259);
x_263 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set_uint8(x_263, sizeof(void*)*1, x_248);
x_264 = lean_array_push(x_251, x_263);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_250);
lean_ctor_set(x_265, 1, x_264);
if (lean_is_scalar(x_261)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_261;
 lean_ctor_set_tag(x_266, 0);
}
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_260);
return x_266;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_21);
x_267 = lean_ctor_get(x_252, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_252, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_269 = x_252;
} else {
 lean_dec_ref(x_252);
 x_269 = lean_box(0);
}
x_270 = lean_io_error_to_string(x_267);
x_271 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set_uint8(x_271, sizeof(void*)*1, x_248);
x_272 = lean_array_push(x_251, x_271);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_250);
lean_ctor_set(x_273, 1, x_272);
if (lean_is_scalar(x_269)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_269;
 lean_ctor_set_tag(x_274, 0);
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_268);
return x_274;
}
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_138);
lean_dec(x_21);
x_275 = !lean_is_exclusive(x_136);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_276 = lean_ctor_get(x_136, 1);
x_277 = lean_ctor_get(x_136, 0);
lean_dec(x_277);
x_278 = lean_ctor_get(x_1, 0);
lean_inc(x_278);
x_279 = l_Lake_Env_leanGithash(x_278);
lean_dec(x_278);
x_280 = l_System_Platform_target;
lean_inc(x_34);
x_281 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_281, 0, x_280);
lean_ctor_set(x_281, 1, x_279);
lean_ctor_set(x_281, 2, x_27);
lean_ctor_set(x_281, 3, x_34);
x_282 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_281);
x_283 = lean_unsigned_to_nat(80u);
x_284 = l_Lean_Json_pretty(x_282, x_283);
x_285 = l_IO_FS_Handle_putStrLn(x_33, x_284, x_137);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
lean_dec(x_285);
x_287 = lean_io_prim_handle_truncate(x_33, x_286);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
lean_ctor_set(x_136, 0, x_288);
x_35 = x_136;
x_36 = x_289;
goto block_135;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_290 = lean_ctor_get(x_287, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_287, 1);
lean_inc(x_291);
lean_dec(x_287);
x_292 = lean_io_error_to_string(x_290);
x_293 = 3;
x_294 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set_uint8(x_294, sizeof(void*)*1, x_293);
x_295 = lean_array_get_size(x_276);
x_296 = lean_array_push(x_276, x_294);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_296);
lean_ctor_set(x_136, 0, x_295);
x_35 = x_136;
x_36 = x_291;
goto block_135;
}
}
else
{
uint8_t x_297; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_297 = !lean_is_exclusive(x_285);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_ctor_get(x_285, 0);
x_299 = lean_io_error_to_string(x_298);
x_300 = 3;
x_301 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set_uint8(x_301, sizeof(void*)*1, x_300);
x_302 = lean_array_get_size(x_276);
x_303 = lean_array_push(x_276, x_301);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_303);
lean_ctor_set(x_136, 0, x_302);
lean_ctor_set_tag(x_285, 0);
lean_ctor_set(x_285, 0, x_136);
return x_285;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_304 = lean_ctor_get(x_285, 0);
x_305 = lean_ctor_get(x_285, 1);
lean_inc(x_305);
lean_inc(x_304);
lean_dec(x_285);
x_306 = lean_io_error_to_string(x_304);
x_307 = 3;
x_308 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set_uint8(x_308, sizeof(void*)*1, x_307);
x_309 = lean_array_get_size(x_276);
x_310 = lean_array_push(x_276, x_308);
lean_ctor_set_tag(x_136, 1);
lean_ctor_set(x_136, 1, x_310);
lean_ctor_set(x_136, 0, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_136);
lean_ctor_set(x_311, 1, x_305);
return x_311;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_312 = lean_ctor_get(x_136, 1);
lean_inc(x_312);
lean_dec(x_136);
x_313 = lean_ctor_get(x_1, 0);
lean_inc(x_313);
x_314 = l_Lake_Env_leanGithash(x_313);
lean_dec(x_313);
x_315 = l_System_Platform_target;
lean_inc(x_34);
x_316 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_314);
lean_ctor_set(x_316, 2, x_27);
lean_ctor_set(x_316, 3, x_34);
x_317 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_316);
x_318 = lean_unsigned_to_nat(80u);
x_319 = l_Lean_Json_pretty(x_317, x_318);
x_320 = l_IO_FS_Handle_putStrLn(x_33, x_319, x_137);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_320, 1);
lean_inc(x_321);
lean_dec(x_320);
x_322 = lean_io_prim_handle_truncate(x_33, x_321);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_312);
x_35 = x_325;
x_36 = x_324;
goto block_135;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_326 = lean_ctor_get(x_322, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_322, 1);
lean_inc(x_327);
lean_dec(x_322);
x_328 = lean_io_error_to_string(x_326);
x_329 = 3;
x_330 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set_uint8(x_330, sizeof(void*)*1, x_329);
x_331 = lean_array_get_size(x_312);
x_332 = lean_array_push(x_312, x_330);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_35 = x_333;
x_36 = x_327;
goto block_135;
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_334 = lean_ctor_get(x_320, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_320, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_320)) {
 lean_ctor_release(x_320, 0);
 lean_ctor_release(x_320, 1);
 x_336 = x_320;
} else {
 lean_dec_ref(x_320);
 x_336 = lean_box(0);
}
x_337 = lean_io_error_to_string(x_334);
x_338 = 3;
x_339 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set_uint8(x_339, sizeof(void*)*1, x_338);
x_340 = lean_array_get_size(x_312);
x_341 = lean_array_push(x_312, x_339);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
if (lean_is_scalar(x_336)) {
 x_343 = lean_alloc_ctor(0, 2, 0);
} else {
 x_343 = x_336;
 lean_ctor_set_tag(x_343, 0);
}
lean_ctor_set(x_343, 0, x_342);
lean_ctor_set(x_343, 1, x_335);
return x_343;
}
}
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_410; lean_object* x_411; lean_object* x_511; 
x_352 = lean_ctor_get(x_30, 0);
x_353 = lean_ctor_get(x_30, 1);
lean_inc(x_353);
lean_inc(x_352);
lean_dec(x_30);
x_354 = lean_ctor_get(x_1, 8);
lean_inc(x_354);
x_511 = lean_io_remove_file(x_18, x_31);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
if (lean_is_scalar(x_12)) {
 x_514 = lean_alloc_ctor(1, 1, 0);
} else {
 x_514 = x_12;
}
lean_ctor_set(x_514, 0, x_512);
x_515 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_515, 0, x_514);
lean_ctor_set(x_515, 1, x_353);
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
if (lean_is_scalar(x_12)) {
 x_518 = lean_alloc_ctor(0, 1, 0);
} else {
 x_518 = x_12;
 lean_ctor_set_tag(x_518, 0);
}
lean_ctor_set(x_518, 0, x_516);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_518);
lean_ctor_set(x_519, 1, x_353);
x_410 = x_519;
x_411 = x_517;
goto block_510;
}
block_409:
{
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = lean_ctor_get(x_1, 9);
lean_inc(x_358);
lean_dec(x_1);
x_359 = l_Lake_elabConfigFile(x_13, x_354, x_358, x_4, x_357, x_356);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; 
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = lean_ctor_get(x_360, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_364 = x_360;
} else {
 lean_dec_ref(x_360);
 x_364 = lean_box(0);
}
x_365 = 0;
lean_inc(x_362);
x_366 = lean_write_module(x_362, x_18, x_365, x_361);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
x_368 = lean_io_prim_handle_unlock(x_352, x_367);
lean_dec(x_352);
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
if (lean_is_scalar(x_364)) {
 x_371 = lean_alloc_ctor(0, 2, 0);
} else {
 x_371 = x_364;
}
lean_ctor_set(x_371, 0, x_362);
lean_ctor_set(x_371, 1, x_363);
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
lean_dec(x_362);
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
x_379 = lean_array_get_size(x_363);
x_380 = lean_array_push(x_363, x_378);
if (lean_is_scalar(x_364)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_364;
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
lean_dec(x_362);
lean_dec(x_352);
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
x_389 = lean_array_get_size(x_363);
x_390 = lean_array_push(x_363, x_388);
if (lean_is_scalar(x_364)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_364;
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
lean_dec(x_352);
lean_dec(x_18);
x_393 = lean_ctor_get(x_359, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_394 = x_359;
} else {
 lean_dec_ref(x_359);
 x_394 = lean_box(0);
}
x_395 = lean_ctor_get(x_360, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_360, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_397 = x_360;
} else {
 lean_dec_ref(x_360);
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
lean_dec(x_352);
lean_dec(x_18);
x_400 = lean_ctor_get(x_359, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_359, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_402 = x_359;
} else {
 lean_dec_ref(x_359);
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
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_404 = lean_ctor_get(x_355, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_355, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_406 = x_355;
} else {
 lean_dec_ref(x_355);
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
lean_ctor_set(x_408, 1, x_356);
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
lean_dec(x_21);
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
lean_inc(x_354);
x_419 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_417);
lean_ctor_set(x_419, 2, x_27);
lean_ctor_set(x_419, 3, x_354);
x_420 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_419);
x_421 = lean_unsigned_to_nat(80u);
x_422 = l_Lean_Json_pretty(x_420, x_421);
x_423 = l_IO_FS_Handle_putStrLn(x_352, x_422, x_411);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_423, 1);
lean_inc(x_424);
lean_dec(x_423);
x_425 = lean_io_prim_handle_truncate(x_352, x_424);
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
x_355 = x_428;
x_356 = x_427;
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
x_355 = x_436;
x_356 = x_430;
goto block_409;
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
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
lean_dec(x_354);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
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
x_454 = lean_io_prim_handle_unlock(x_352, x_411);
lean_dec(x_352);
if (lean_obj_tag(x_454) == 0)
{
lean_object* x_455; lean_object* x_456; 
x_455 = lean_ctor_get(x_454, 1);
lean_inc(x_455);
lean_dec(x_454);
x_456 = lean_io_remove_file(x_21, x_455);
lean_dec(x_21);
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
lean_dec(x_21);
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
lean_dec(x_21);
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
lean_inc(x_354);
x_482 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_480);
lean_ctor_set(x_482, 2, x_27);
lean_ctor_set(x_482, 3, x_354);
x_483 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_482);
x_484 = lean_unsigned_to_nat(80u);
x_485 = l_Lean_Json_pretty(x_483, x_484);
x_486 = l_IO_FS_Handle_putStrLn(x_352, x_485, x_411);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
lean_dec(x_486);
x_488 = lean_io_prim_handle_truncate(x_352, x_487);
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
x_355 = x_491;
x_356 = x_490;
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
x_355 = x_499;
x_356 = x_493;
goto block_409;
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; uint8_t x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_354);
lean_dec(x_352);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
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
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_520 = !lean_is_exclusive(x_30);
if (x_520 == 0)
{
lean_object* x_521; 
x_521 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_521, 0, x_30);
lean_ctor_set(x_521, 1, x_31);
return x_521;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_30, 0);
x_523 = lean_ctor_get(x_30, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_30);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_522);
lean_ctor_set(x_524, 1, x_523);
x_525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_31);
return x_525;
}
}
}
block_1271:
{
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; uint8_t x_1172; 
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
x_1172 = lean_ctor_get_uint8(x_1, sizeof(void*)*12);
if (x_1172 == 0)
{
uint8_t x_1173; lean_object* x_1174; 
lean_dec(x_12);
x_1173 = 0;
x_1174 = lean_io_prim_handle_lock(x_529, x_1173, x_528);
if (lean_obj_tag(x_1174) == 0)
{
lean_object* x_1175; lean_object* x_1176; 
x_1175 = lean_ctor_get(x_1174, 1);
lean_inc(x_1175);
lean_dec(x_1174);
x_1176 = l_IO_FS_Handle_readToEnd(x_529, x_1175);
if (lean_obj_tag(x_1176) == 0)
{
uint8_t x_1177; 
x_1177 = !lean_is_exclusive(x_1176);
if (x_1177 == 0)
{
lean_object* x_1178; 
x_1178 = lean_ctor_get(x_1176, 1);
lean_ctor_set(x_1176, 1, x_530);
x_532 = x_1176;
x_533 = x_1178;
goto block_1171;
}
else
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; 
x_1179 = lean_ctor_get(x_1176, 0);
x_1180 = lean_ctor_get(x_1176, 1);
lean_inc(x_1180);
lean_inc(x_1179);
lean_dec(x_1176);
x_1181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1181, 0, x_1179);
lean_ctor_set(x_1181, 1, x_530);
x_532 = x_1181;
x_533 = x_1180;
goto block_1171;
}
}
else
{
uint8_t x_1182; 
x_1182 = !lean_is_exclusive(x_1176);
if (x_1182 == 0)
{
lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; uint8_t x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
x_1183 = lean_ctor_get(x_1176, 0);
x_1184 = lean_ctor_get(x_1176, 1);
x_1185 = lean_io_error_to_string(x_1183);
x_1186 = 3;
x_1187 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1187, 0, x_1185);
lean_ctor_set_uint8(x_1187, sizeof(void*)*1, x_1186);
x_1188 = lean_array_get_size(x_530);
x_1189 = lean_array_push(x_530, x_1187);
lean_ctor_set(x_1176, 1, x_1189);
lean_ctor_set(x_1176, 0, x_1188);
x_532 = x_1176;
x_533 = x_1184;
goto block_1171;
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; uint8_t x_1193; lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; 
x_1190 = lean_ctor_get(x_1176, 0);
x_1191 = lean_ctor_get(x_1176, 1);
lean_inc(x_1191);
lean_inc(x_1190);
lean_dec(x_1176);
x_1192 = lean_io_error_to_string(x_1190);
x_1193 = 3;
x_1194 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set_uint8(x_1194, sizeof(void*)*1, x_1193);
x_1195 = lean_array_get_size(x_530);
x_1196 = lean_array_push(x_530, x_1194);
x_1197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1197, 0, x_1195);
lean_ctor_set(x_1197, 1, x_1196);
x_532 = x_1197;
x_533 = x_1191;
goto block_1171;
}
}
}
else
{
uint8_t x_1198; 
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1198 = !lean_is_exclusive(x_1174);
if (x_1198 == 0)
{
lean_object* x_1199; lean_object* x_1200; uint8_t x_1201; lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
x_1199 = lean_ctor_get(x_1174, 0);
x_1200 = lean_io_error_to_string(x_1199);
x_1201 = 3;
x_1202 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1202, 0, x_1200);
lean_ctor_set_uint8(x_1202, sizeof(void*)*1, x_1201);
x_1203 = lean_array_get_size(x_530);
x_1204 = lean_array_push(x_530, x_1202);
x_1205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1205, 0, x_1203);
lean_ctor_set(x_1205, 1, x_1204);
lean_ctor_set_tag(x_1174, 0);
lean_ctor_set(x_1174, 0, x_1205);
return x_1174;
}
else
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; uint8_t x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
x_1206 = lean_ctor_get(x_1174, 0);
x_1207 = lean_ctor_get(x_1174, 1);
lean_inc(x_1207);
lean_inc(x_1206);
lean_dec(x_1174);
x_1208 = lean_io_error_to_string(x_1206);
x_1209 = 3;
x_1210 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1210, 0, x_1208);
lean_ctor_set_uint8(x_1210, sizeof(void*)*1, x_1209);
x_1211 = lean_array_get_size(x_530);
x_1212 = lean_array_push(x_530, x_1210);
x_1213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1213, 0, x_1211);
lean_ctor_set(x_1213, 1, x_1212);
x_1214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1214, 0, x_1213);
lean_ctor_set(x_1214, 1, x_1207);
return x_1214;
}
}
}
else
{
lean_object* x_1215; lean_object* x_1216; uint8_t x_1224; lean_object* x_1225; 
lean_dec(x_531);
lean_dec(x_29);
x_1224 = 1;
x_1225 = lean_io_prim_handle_mk(x_24, x_1224, x_528);
lean_dec(x_24);
if (lean_obj_tag(x_1225) == 0)
{
lean_object* x_1226; lean_object* x_1227; uint8_t x_1228; lean_object* x_1229; 
x_1226 = lean_ctor_get(x_1225, 0);
lean_inc(x_1226);
x_1227 = lean_ctor_get(x_1225, 1);
lean_inc(x_1227);
lean_dec(x_1225);
x_1228 = 1;
x_1229 = lean_io_prim_handle_try_lock(x_1226, x_1228, x_1227);
if (lean_obj_tag(x_1229) == 0)
{
lean_object* x_1230; uint8_t x_1231; 
x_1230 = lean_ctor_get(x_1229, 0);
lean_inc(x_1230);
x_1231 = lean_unbox(x_1230);
lean_dec(x_1230);
if (x_1231 == 0)
{
lean_object* x_1232; lean_object* x_1233; 
lean_dec(x_1226);
x_1232 = lean_ctor_get(x_1229, 1);
lean_inc(x_1232);
lean_dec(x_1229);
x_1233 = lean_io_prim_handle_unlock(x_529, x_1232);
lean_dec(x_529);
if (lean_obj_tag(x_1233) == 0)
{
lean_object* x_1234; lean_object* x_1235; 
x_1234 = lean_ctor_get(x_1233, 1);
lean_inc(x_1234);
lean_dec(x_1233);
x_1235 = l_Lake_importConfigFile___closed__12;
x_1215 = x_1235;
x_1216 = x_1234;
goto block_1223;
}
else
{
lean_object* x_1236; lean_object* x_1237; 
x_1236 = lean_ctor_get(x_1233, 0);
lean_inc(x_1236);
x_1237 = lean_ctor_get(x_1233, 1);
lean_inc(x_1237);
lean_dec(x_1233);
x_1215 = x_1236;
x_1216 = x_1237;
goto block_1223;
}
}
else
{
lean_object* x_1238; lean_object* x_1239; 
x_1238 = lean_ctor_get(x_1229, 1);
lean_inc(x_1238);
lean_dec(x_1229);
x_1239 = lean_io_prim_handle_unlock(x_529, x_1238);
lean_dec(x_529);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; uint8_t x_1241; lean_object* x_1242; 
x_1240 = lean_ctor_get(x_1239, 1);
lean_inc(x_1240);
lean_dec(x_1239);
x_1241 = 3;
x_1242 = lean_io_prim_handle_mk(x_21, x_1241, x_1240);
if (lean_obj_tag(x_1242) == 0)
{
lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; 
x_1243 = lean_ctor_get(x_1242, 0);
lean_inc(x_1243);
x_1244 = lean_ctor_get(x_1242, 1);
lean_inc(x_1244);
lean_dec(x_1242);
x_1245 = lean_io_prim_handle_lock(x_1243, x_1228, x_1244);
if (lean_obj_tag(x_1245) == 0)
{
lean_object* x_1246; lean_object* x_1247; 
x_1246 = lean_ctor_get(x_1245, 1);
lean_inc(x_1246);
lean_dec(x_1245);
x_1247 = lean_io_prim_handle_unlock(x_1226, x_1246);
lean_dec(x_1226);
if (lean_obj_tag(x_1247) == 0)
{
uint8_t x_1248; 
x_1248 = !lean_is_exclusive(x_1247);
if (x_1248 == 0)
{
lean_object* x_1249; lean_object* x_1250; 
x_1249 = lean_ctor_get(x_1247, 1);
x_1250 = lean_ctor_get(x_1247, 0);
lean_dec(x_1250);
lean_ctor_set(x_1247, 1, x_530);
lean_ctor_set(x_1247, 0, x_1243);
x_30 = x_1247;
x_31 = x_1249;
goto block_526;
}
else
{
lean_object* x_1251; lean_object* x_1252; 
x_1251 = lean_ctor_get(x_1247, 1);
lean_inc(x_1251);
lean_dec(x_1247);
x_1252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1252, 0, x_1243);
lean_ctor_set(x_1252, 1, x_530);
x_30 = x_1252;
x_31 = x_1251;
goto block_526;
}
}
else
{
lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1243);
x_1253 = lean_ctor_get(x_1247, 0);
lean_inc(x_1253);
x_1254 = lean_ctor_get(x_1247, 1);
lean_inc(x_1254);
lean_dec(x_1247);
x_1215 = x_1253;
x_1216 = x_1254;
goto block_1223;
}
}
else
{
lean_object* x_1255; lean_object* x_1256; 
lean_dec(x_1243);
lean_dec(x_1226);
x_1255 = lean_ctor_get(x_1245, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1245, 1);
lean_inc(x_1256);
lean_dec(x_1245);
x_1215 = x_1255;
x_1216 = x_1256;
goto block_1223;
}
}
else
{
lean_object* x_1257; lean_object* x_1258; 
lean_dec(x_1226);
x_1257 = lean_ctor_get(x_1242, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1242, 1);
lean_inc(x_1258);
lean_dec(x_1242);
x_1215 = x_1257;
x_1216 = x_1258;
goto block_1223;
}
}
else
{
lean_object* x_1259; lean_object* x_1260; 
lean_dec(x_1226);
x_1259 = lean_ctor_get(x_1239, 0);
lean_inc(x_1259);
x_1260 = lean_ctor_get(x_1239, 1);
lean_inc(x_1260);
lean_dec(x_1239);
x_1215 = x_1259;
x_1216 = x_1260;
goto block_1223;
}
}
}
else
{
lean_object* x_1261; lean_object* x_1262; 
lean_dec(x_1226);
lean_dec(x_529);
x_1261 = lean_ctor_get(x_1229, 0);
lean_inc(x_1261);
x_1262 = lean_ctor_get(x_1229, 1);
lean_inc(x_1262);
lean_dec(x_1229);
x_1215 = x_1261;
x_1216 = x_1262;
goto block_1223;
}
}
else
{
lean_object* x_1263; lean_object* x_1264; 
lean_dec(x_529);
x_1263 = lean_ctor_get(x_1225, 0);
lean_inc(x_1263);
x_1264 = lean_ctor_get(x_1225, 1);
lean_inc(x_1264);
lean_dec(x_1225);
x_1215 = x_1263;
x_1216 = x_1264;
goto block_1223;
}
block_1223:
{
lean_object* x_1217; uint8_t x_1218; lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; 
x_1217 = lean_io_error_to_string(x_1215);
x_1218 = 3;
x_1219 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1219, 0, x_1217);
lean_ctor_set_uint8(x_1219, sizeof(void*)*1, x_1218);
x_1220 = lean_array_get_size(x_530);
x_1221 = lean_array_push(x_530, x_1219);
x_1222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1222, 0, x_1220);
lean_ctor_set(x_1222, 1, x_1221);
x_30 = x_1222;
x_31 = x_1216;
goto block_526;
}
}
block_1171:
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
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
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
x_545 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950_(x_544);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_545);
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
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
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; uint8_t x_1104; 
x_551 = lean_ctor_get(x_545, 0);
lean_inc(x_551);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 x_552 = x_545;
} else {
 lean_dec_ref(x_545);
 x_552 = lean_box(0);
}
x_1052 = l_System_FilePath_pathExists(x_18, x_533);
x_1053 = lean_ctor_get(x_1052, 0);
lean_inc(x_1053);
x_1054 = lean_ctor_get(x_1052, 1);
lean_inc(x_1054);
lean_dec(x_1052);
x_1104 = lean_unbox(x_1053);
lean_dec(x_1053);
if (x_1104 == 0)
{
lean_object* x_1105; 
lean_dec(x_29);
x_1105 = lean_box(0);
x_1055 = x_1105;
goto block_1103;
}
else
{
lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; uint8_t x_1110; 
x_1106 = lean_ctor_get(x_551, 0);
lean_inc(x_1106);
x_1107 = lean_ctor_get(x_551, 1);
lean_inc(x_1107);
x_1108 = lean_ctor_get(x_551, 2);
lean_inc(x_1108);
x_1109 = l_System_Platform_target;
x_1110 = lean_string_dec_eq(x_1106, x_1109);
lean_dec(x_1106);
if (x_1110 == 0)
{
lean_object* x_1111; 
lean_dec(x_1108);
lean_dec(x_1107);
lean_dec(x_29);
x_1111 = lean_box(0);
x_1055 = x_1111;
goto block_1103;
}
else
{
lean_object* x_1112; lean_object* x_1113; uint8_t x_1114; 
x_1112 = lean_ctor_get(x_1, 0);
lean_inc(x_1112);
x_1113 = l_Lake_Env_leanGithash(x_1112);
lean_dec(x_1112);
x_1114 = lean_string_dec_eq(x_1107, x_1113);
lean_dec(x_1113);
lean_dec(x_1107);
if (x_1114 == 0)
{
lean_object* x_1115; 
lean_dec(x_1108);
lean_dec(x_29);
x_1115 = lean_box(0);
x_1055 = x_1115;
goto block_1103;
}
else
{
uint64_t x_1116; uint64_t x_1117; uint8_t x_1118; 
x_1116 = lean_unbox_uint64(x_1108);
lean_dec(x_1108);
x_1117 = lean_unbox_uint64(x_27);
x_1118 = lean_uint64_dec_eq(x_1116, x_1117);
if (x_1118 == 0)
{
lean_object* x_1119; 
lean_dec(x_29);
x_1119 = lean_box(0);
x_1055 = x_1119;
goto block_1103;
}
else
{
lean_object* x_1120; lean_object* x_1121; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_536);
lean_dec(x_531);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_4);
x_1120 = lean_ctor_get(x_1, 9);
lean_inc(x_1120);
lean_dec(x_1);
x_1121 = l_Lake_importConfigFileCore(x_18, x_1120, x_1054);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
x_1123 = lean_ctor_get(x_1121, 1);
lean_inc(x_1123);
lean_dec(x_1121);
x_1124 = lean_io_prim_handle_unlock(x_529, x_1123);
lean_dec(x_529);
if (lean_obj_tag(x_1124) == 0)
{
uint8_t x_1125; 
x_1125 = !lean_is_exclusive(x_1124);
if (x_1125 == 0)
{
lean_object* x_1126; lean_object* x_1127; 
x_1126 = lean_ctor_get(x_1124, 0);
lean_dec(x_1126);
if (lean_is_scalar(x_29)) {
 x_1127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1127 = x_29;
}
lean_ctor_set(x_1127, 0, x_1122);
lean_ctor_set(x_1127, 1, x_535);
lean_ctor_set(x_1124, 0, x_1127);
return x_1124;
}
else
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; 
x_1128 = lean_ctor_get(x_1124, 1);
lean_inc(x_1128);
lean_dec(x_1124);
if (lean_is_scalar(x_29)) {
 x_1129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1129 = x_29;
}
lean_ctor_set(x_1129, 0, x_1122);
lean_ctor_set(x_1129, 1, x_535);
x_1130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1130, 0, x_1129);
lean_ctor_set(x_1130, 1, x_1128);
return x_1130;
}
}
else
{
uint8_t x_1131; 
lean_dec(x_1122);
x_1131 = !lean_is_exclusive(x_1124);
if (x_1131 == 0)
{
lean_object* x_1132; lean_object* x_1133; uint8_t x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
x_1132 = lean_ctor_get(x_1124, 0);
x_1133 = lean_io_error_to_string(x_1132);
x_1134 = 3;
x_1135 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1135, 0, x_1133);
lean_ctor_set_uint8(x_1135, sizeof(void*)*1, x_1134);
x_1136 = lean_array_get_size(x_535);
x_1137 = lean_array_push(x_535, x_1135);
if (lean_is_scalar(x_29)) {
 x_1138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1138 = x_29;
 lean_ctor_set_tag(x_1138, 1);
}
lean_ctor_set(x_1138, 0, x_1136);
lean_ctor_set(x_1138, 1, x_1137);
lean_ctor_set_tag(x_1124, 0);
lean_ctor_set(x_1124, 0, x_1138);
return x_1124;
}
else
{
lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; uint8_t x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1139 = lean_ctor_get(x_1124, 0);
x_1140 = lean_ctor_get(x_1124, 1);
lean_inc(x_1140);
lean_inc(x_1139);
lean_dec(x_1124);
x_1141 = lean_io_error_to_string(x_1139);
x_1142 = 3;
x_1143 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1143, 0, x_1141);
lean_ctor_set_uint8(x_1143, sizeof(void*)*1, x_1142);
x_1144 = lean_array_get_size(x_535);
x_1145 = lean_array_push(x_535, x_1143);
if (lean_is_scalar(x_29)) {
 x_1146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1146 = x_29;
 lean_ctor_set_tag(x_1146, 1);
}
lean_ctor_set(x_1146, 0, x_1144);
lean_ctor_set(x_1146, 1, x_1145);
x_1147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1147, 0, x_1146);
lean_ctor_set(x_1147, 1, x_1140);
return x_1147;
}
}
}
else
{
uint8_t x_1148; 
lean_dec(x_529);
x_1148 = !lean_is_exclusive(x_1121);
if (x_1148 == 0)
{
lean_object* x_1149; lean_object* x_1150; uint8_t x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
x_1149 = lean_ctor_get(x_1121, 0);
x_1150 = lean_io_error_to_string(x_1149);
x_1151 = 3;
x_1152 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1152, 0, x_1150);
lean_ctor_set_uint8(x_1152, sizeof(void*)*1, x_1151);
x_1153 = lean_array_get_size(x_535);
x_1154 = lean_array_push(x_535, x_1152);
if (lean_is_scalar(x_29)) {
 x_1155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1155 = x_29;
 lean_ctor_set_tag(x_1155, 1);
}
lean_ctor_set(x_1155, 0, x_1153);
lean_ctor_set(x_1155, 1, x_1154);
lean_ctor_set_tag(x_1121, 0);
lean_ctor_set(x_1121, 0, x_1155);
return x_1121;
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; uint8_t x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1156 = lean_ctor_get(x_1121, 0);
x_1157 = lean_ctor_get(x_1121, 1);
lean_inc(x_1157);
lean_inc(x_1156);
lean_dec(x_1121);
x_1158 = lean_io_error_to_string(x_1156);
x_1159 = 3;
x_1160 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1160, 0, x_1158);
lean_ctor_set_uint8(x_1160, sizeof(void*)*1, x_1159);
x_1161 = lean_array_get_size(x_535);
x_1162 = lean_array_push(x_535, x_1160);
if (lean_is_scalar(x_29)) {
 x_1163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1163 = x_29;
 lean_ctor_set_tag(x_1163, 1);
}
lean_ctor_set(x_1163, 0, x_1161);
lean_ctor_set(x_1163, 1, x_1162);
x_1164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1164, 0, x_1163);
lean_ctor_set(x_1164, 1, x_1157);
return x_1164;
}
}
}
}
}
}
block_1051:
{
if (lean_obj_tag(x_553) == 0)
{
uint8_t x_555; 
x_555 = !lean_is_exclusive(x_553);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_660; lean_object* x_661; lean_object* x_869; 
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
x_869 = lean_io_remove_file(x_18, x_554);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_870 = lean_ctor_get(x_869, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_869, 1);
lean_inc(x_871);
lean_dec(x_869);
if (lean_is_scalar(x_552)) {
 x_872 = lean_alloc_ctor(1, 1, 0);
} else {
 x_872 = x_552;
}
lean_ctor_set(x_872, 0, x_870);
lean_ctor_set(x_553, 0, x_872);
x_660 = x_553;
x_661 = x_871;
goto block_868;
}
else
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_873 = lean_ctor_get(x_869, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_869, 1);
lean_inc(x_874);
lean_dec(x_869);
if (lean_is_scalar(x_552)) {
 x_875 = lean_alloc_ctor(0, 1, 0);
} else {
 x_875 = x_552;
 lean_ctor_set_tag(x_875, 0);
}
lean_ctor_set(x_875, 0, x_873);
lean_ctor_set(x_553, 0, x_875);
x_660 = x_553;
x_661 = x_874;
goto block_868;
}
block_659:
{
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_ctor_get(x_1, 9);
lean_inc(x_562);
lean_dec(x_1);
x_563 = l_Lake_elabConfigFile(x_13, x_557, x_562, x_4, x_561, x_560);
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
lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; 
x_567 = lean_ctor_get(x_564, 0);
x_568 = lean_ctor_get(x_564, 1);
x_569 = 0;
lean_inc(x_567);
x_570 = lean_write_module(x_567, x_18, x_569, x_565);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_ctor_get(x_570, 1);
lean_inc(x_571);
lean_dec(x_570);
x_572 = lean_io_prim_handle_unlock(x_556, x_571);
lean_dec(x_556);
if (lean_obj_tag(x_572) == 0)
{
uint8_t x_573; 
x_573 = !lean_is_exclusive(x_572);
if (x_573 == 0)
{
lean_object* x_574; 
x_574 = lean_ctor_get(x_572, 0);
lean_dec(x_574);
lean_ctor_set(x_572, 0, x_564);
return x_572;
}
else
{
lean_object* x_575; lean_object* x_576; 
x_575 = lean_ctor_get(x_572, 1);
lean_inc(x_575);
lean_dec(x_572);
x_576 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_576, 0, x_564);
lean_ctor_set(x_576, 1, x_575);
return x_576;
}
}
else
{
uint8_t x_577; 
lean_dec(x_567);
x_577 = !lean_is_exclusive(x_572);
if (x_577 == 0)
{
lean_object* x_578; lean_object* x_579; uint8_t x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
x_578 = lean_ctor_get(x_572, 0);
x_579 = lean_io_error_to_string(x_578);
x_580 = 3;
x_581 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set_uint8(x_581, sizeof(void*)*1, x_580);
x_582 = lean_array_get_size(x_568);
x_583 = lean_array_push(x_568, x_581);
lean_ctor_set_tag(x_564, 1);
lean_ctor_set(x_564, 1, x_583);
lean_ctor_set(x_564, 0, x_582);
lean_ctor_set_tag(x_572, 0);
lean_ctor_set(x_572, 0, x_564);
return x_572;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_584 = lean_ctor_get(x_572, 0);
x_585 = lean_ctor_get(x_572, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_572);
x_586 = lean_io_error_to_string(x_584);
x_587 = 3;
x_588 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_588, 0, x_586);
lean_ctor_set_uint8(x_588, sizeof(void*)*1, x_587);
x_589 = lean_array_get_size(x_568);
x_590 = lean_array_push(x_568, x_588);
lean_ctor_set_tag(x_564, 1);
lean_ctor_set(x_564, 1, x_590);
lean_ctor_set(x_564, 0, x_589);
x_591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_591, 0, x_564);
lean_ctor_set(x_591, 1, x_585);
return x_591;
}
}
}
else
{
uint8_t x_592; 
lean_dec(x_567);
lean_dec(x_556);
x_592 = !lean_is_exclusive(x_570);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; uint8_t x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_593 = lean_ctor_get(x_570, 0);
x_594 = lean_io_error_to_string(x_593);
x_595 = 3;
x_596 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set_uint8(x_596, sizeof(void*)*1, x_595);
x_597 = lean_array_get_size(x_568);
x_598 = lean_array_push(x_568, x_596);
lean_ctor_set_tag(x_564, 1);
lean_ctor_set(x_564, 1, x_598);
lean_ctor_set(x_564, 0, x_597);
lean_ctor_set_tag(x_570, 0);
lean_ctor_set(x_570, 0, x_564);
return x_570;
}
else
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; uint8_t x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_599 = lean_ctor_get(x_570, 0);
x_600 = lean_ctor_get(x_570, 1);
lean_inc(x_600);
lean_inc(x_599);
lean_dec(x_570);
x_601 = lean_io_error_to_string(x_599);
x_602 = 3;
x_603 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set_uint8(x_603, sizeof(void*)*1, x_602);
x_604 = lean_array_get_size(x_568);
x_605 = lean_array_push(x_568, x_603);
lean_ctor_set_tag(x_564, 1);
lean_ctor_set(x_564, 1, x_605);
lean_ctor_set(x_564, 0, x_604);
x_606 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_606, 0, x_564);
lean_ctor_set(x_606, 1, x_600);
return x_606;
}
}
}
else
{
lean_object* x_607; lean_object* x_608; uint8_t x_609; lean_object* x_610; 
x_607 = lean_ctor_get(x_564, 0);
x_608 = lean_ctor_get(x_564, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_564);
x_609 = 0;
lean_inc(x_607);
x_610 = lean_write_module(x_607, x_18, x_609, x_565);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_ctor_get(x_610, 1);
lean_inc(x_611);
lean_dec(x_610);
x_612 = lean_io_prim_handle_unlock(x_556, x_611);
lean_dec(x_556);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_614 = x_612;
} else {
 lean_dec_ref(x_612);
 x_614 = lean_box(0);
}
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_607);
lean_ctor_set(x_615, 1, x_608);
if (lean_is_scalar(x_614)) {
 x_616 = lean_alloc_ctor(0, 2, 0);
} else {
 x_616 = x_614;
}
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_613);
return x_616;
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; uint8_t x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_607);
x_617 = lean_ctor_get(x_612, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_612, 1);
lean_inc(x_618);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_619 = x_612;
} else {
 lean_dec_ref(x_612);
 x_619 = lean_box(0);
}
x_620 = lean_io_error_to_string(x_617);
x_621 = 3;
x_622 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_622, 0, x_620);
lean_ctor_set_uint8(x_622, sizeof(void*)*1, x_621);
x_623 = lean_array_get_size(x_608);
x_624 = lean_array_push(x_608, x_622);
x_625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
if (lean_is_scalar(x_619)) {
 x_626 = lean_alloc_ctor(0, 2, 0);
} else {
 x_626 = x_619;
 lean_ctor_set_tag(x_626, 0);
}
lean_ctor_set(x_626, 0, x_625);
lean_ctor_set(x_626, 1, x_618);
return x_626;
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_607);
lean_dec(x_556);
x_627 = lean_ctor_get(x_610, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_610, 1);
lean_inc(x_628);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_629 = x_610;
} else {
 lean_dec_ref(x_610);
 x_629 = lean_box(0);
}
x_630 = lean_io_error_to_string(x_627);
x_631 = 3;
x_632 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_632, 0, x_630);
lean_ctor_set_uint8(x_632, sizeof(void*)*1, x_631);
x_633 = lean_array_get_size(x_608);
x_634 = lean_array_push(x_608, x_632);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
if (lean_is_scalar(x_629)) {
 x_636 = lean_alloc_ctor(0, 2, 0);
} else {
 x_636 = x_629;
 lean_ctor_set_tag(x_636, 0);
}
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_628);
return x_636;
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_556);
lean_dec(x_18);
x_637 = !lean_is_exclusive(x_563);
if (x_637 == 0)
{
lean_object* x_638; uint8_t x_639; 
x_638 = lean_ctor_get(x_563, 0);
lean_dec(x_638);
x_639 = !lean_is_exclusive(x_564);
if (x_639 == 0)
{
return x_563;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_564, 0);
x_641 = lean_ctor_get(x_564, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_564);
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
lean_ctor_set(x_563, 0, x_642);
return x_563;
}
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_643 = lean_ctor_get(x_563, 1);
lean_inc(x_643);
lean_dec(x_563);
x_644 = lean_ctor_get(x_564, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_564, 1);
lean_inc(x_645);
if (lean_is_exclusive(x_564)) {
 lean_ctor_release(x_564, 0);
 lean_ctor_release(x_564, 1);
 x_646 = x_564;
} else {
 lean_dec_ref(x_564);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 2, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_644);
lean_ctor_set(x_647, 1, x_645);
x_648 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_643);
return x_648;
}
}
}
else
{
uint8_t x_649; 
lean_dec(x_556);
lean_dec(x_18);
x_649 = !lean_is_exclusive(x_563);
if (x_649 == 0)
{
return x_563;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_563, 0);
x_651 = lean_ctor_get(x_563, 1);
lean_inc(x_651);
lean_inc(x_650);
lean_dec(x_563);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_650);
lean_ctor_set(x_652, 1, x_651);
return x_652;
}
}
}
else
{
uint8_t x_653; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_653 = !lean_is_exclusive(x_559);
if (x_653 == 0)
{
lean_object* x_654; 
x_654 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_654, 0, x_559);
lean_ctor_set(x_654, 1, x_560);
return x_654;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_655 = lean_ctor_get(x_559, 0);
x_656 = lean_ctor_get(x_559, 1);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_559);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_656);
x_658 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_560);
return x_658;
}
}
}
block_868:
{
lean_object* x_662; 
x_662 = lean_ctor_get(x_660, 0);
lean_inc(x_662);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; 
x_663 = lean_ctor_get(x_662, 0);
lean_inc(x_663);
lean_dec(x_662);
if (lean_obj_tag(x_663) == 11)
{
uint8_t x_664; 
lean_dec(x_663);
lean_dec(x_21);
x_664 = !lean_is_exclusive(x_660);
if (x_664 == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_665 = lean_ctor_get(x_660, 1);
x_666 = lean_ctor_get(x_660, 0);
lean_dec(x_666);
x_667 = lean_ctor_get(x_1, 0);
lean_inc(x_667);
x_668 = l_Lake_Env_leanGithash(x_667);
lean_dec(x_667);
x_669 = l_System_Platform_target;
lean_inc(x_557);
if (lean_is_scalar(x_558)) {
 x_670 = lean_alloc_ctor(0, 4, 0);
} else {
 x_670 = x_558;
}
lean_ctor_set(x_670, 0, x_669);
lean_ctor_set(x_670, 1, x_668);
lean_ctor_set(x_670, 2, x_27);
lean_ctor_set(x_670, 3, x_557);
x_671 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_670);
x_672 = lean_unsigned_to_nat(80u);
x_673 = l_Lean_Json_pretty(x_671, x_672);
x_674 = l_IO_FS_Handle_putStrLn(x_556, x_673, x_661);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_674, 1);
lean_inc(x_675);
lean_dec(x_674);
x_676 = lean_io_prim_handle_truncate(x_556, x_675);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_ctor_get(x_676, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_676, 1);
lean_inc(x_678);
lean_dec(x_676);
lean_ctor_set(x_660, 0, x_677);
x_559 = x_660;
x_560 = x_678;
goto block_659;
}
else
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; uint8_t x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_679 = lean_ctor_get(x_676, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_676, 1);
lean_inc(x_680);
lean_dec(x_676);
x_681 = lean_io_error_to_string(x_679);
x_682 = 3;
x_683 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_683, 0, x_681);
lean_ctor_set_uint8(x_683, sizeof(void*)*1, x_682);
x_684 = lean_array_get_size(x_665);
x_685 = lean_array_push(x_665, x_683);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_685);
lean_ctor_set(x_660, 0, x_684);
x_559 = x_660;
x_560 = x_680;
goto block_659;
}
}
else
{
uint8_t x_686; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_686 = !lean_is_exclusive(x_674);
if (x_686 == 0)
{
lean_object* x_687; lean_object* x_688; uint8_t x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; 
x_687 = lean_ctor_get(x_674, 0);
x_688 = lean_io_error_to_string(x_687);
x_689 = 3;
x_690 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_690, 0, x_688);
lean_ctor_set_uint8(x_690, sizeof(void*)*1, x_689);
x_691 = lean_array_get_size(x_665);
x_692 = lean_array_push(x_665, x_690);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_692);
lean_ctor_set(x_660, 0, x_691);
lean_ctor_set_tag(x_674, 0);
lean_ctor_set(x_674, 0, x_660);
return x_674;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; uint8_t x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_693 = lean_ctor_get(x_674, 0);
x_694 = lean_ctor_get(x_674, 1);
lean_inc(x_694);
lean_inc(x_693);
lean_dec(x_674);
x_695 = lean_io_error_to_string(x_693);
x_696 = 3;
x_697 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set_uint8(x_697, sizeof(void*)*1, x_696);
x_698 = lean_array_get_size(x_665);
x_699 = lean_array_push(x_665, x_697);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_699);
lean_ctor_set(x_660, 0, x_698);
x_700 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_700, 0, x_660);
lean_ctor_set(x_700, 1, x_694);
return x_700;
}
}
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_701 = lean_ctor_get(x_660, 1);
lean_inc(x_701);
lean_dec(x_660);
x_702 = lean_ctor_get(x_1, 0);
lean_inc(x_702);
x_703 = l_Lake_Env_leanGithash(x_702);
lean_dec(x_702);
x_704 = l_System_Platform_target;
lean_inc(x_557);
if (lean_is_scalar(x_558)) {
 x_705 = lean_alloc_ctor(0, 4, 0);
} else {
 x_705 = x_558;
}
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_703);
lean_ctor_set(x_705, 2, x_27);
lean_ctor_set(x_705, 3, x_557);
x_706 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_705);
x_707 = lean_unsigned_to_nat(80u);
x_708 = l_Lean_Json_pretty(x_706, x_707);
x_709 = l_IO_FS_Handle_putStrLn(x_556, x_708, x_661);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; lean_object* x_711; 
x_710 = lean_ctor_get(x_709, 1);
lean_inc(x_710);
lean_dec(x_709);
x_711 = lean_io_prim_handle_truncate(x_556, x_710);
if (lean_obj_tag(x_711) == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; 
x_712 = lean_ctor_get(x_711, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_711, 1);
lean_inc(x_713);
lean_dec(x_711);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_712);
lean_ctor_set(x_714, 1, x_701);
x_559 = x_714;
x_560 = x_713;
goto block_659;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; uint8_t x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_715 = lean_ctor_get(x_711, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_711, 1);
lean_inc(x_716);
lean_dec(x_711);
x_717 = lean_io_error_to_string(x_715);
x_718 = 3;
x_719 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set_uint8(x_719, sizeof(void*)*1, x_718);
x_720 = lean_array_get_size(x_701);
x_721 = lean_array_push(x_701, x_719);
x_722 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_722, 0, x_720);
lean_ctor_set(x_722, 1, x_721);
x_559 = x_722;
x_560 = x_716;
goto block_659;
}
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; uint8_t x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_723 = lean_ctor_get(x_709, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_709, 1);
lean_inc(x_724);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_725 = x_709;
} else {
 lean_dec_ref(x_709);
 x_725 = lean_box(0);
}
x_726 = lean_io_error_to_string(x_723);
x_727 = 3;
x_728 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_728, 0, x_726);
lean_ctor_set_uint8(x_728, sizeof(void*)*1, x_727);
x_729 = lean_array_get_size(x_701);
x_730 = lean_array_push(x_701, x_728);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
if (lean_is_scalar(x_725)) {
 x_732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_732 = x_725;
 lean_ctor_set_tag(x_732, 0);
}
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_724);
return x_732;
}
}
}
else
{
uint8_t x_733; 
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_733 = !lean_is_exclusive(x_660);
if (x_733 == 0)
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; uint8_t x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
x_734 = lean_ctor_get(x_660, 1);
x_735 = lean_ctor_get(x_660, 0);
lean_dec(x_735);
x_736 = lean_io_error_to_string(x_663);
x_737 = 3;
x_738 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_738, 0, x_736);
lean_ctor_set_uint8(x_738, sizeof(void*)*1, x_737);
x_739 = lean_array_get_size(x_734);
x_740 = lean_array_push(x_734, x_738);
x_741 = lean_io_prim_handle_unlock(x_556, x_661);
lean_dec(x_556);
if (lean_obj_tag(x_741) == 0)
{
lean_object* x_742; lean_object* x_743; 
x_742 = lean_ctor_get(x_741, 1);
lean_inc(x_742);
lean_dec(x_741);
x_743 = lean_io_remove_file(x_21, x_742);
lean_dec(x_21);
if (lean_obj_tag(x_743) == 0)
{
uint8_t x_744; 
x_744 = !lean_is_exclusive(x_743);
if (x_744 == 0)
{
lean_object* x_745; 
x_745 = lean_ctor_get(x_743, 0);
lean_dec(x_745);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_740);
lean_ctor_set(x_660, 0, x_739);
lean_ctor_set(x_743, 0, x_660);
return x_743;
}
else
{
lean_object* x_746; lean_object* x_747; 
x_746 = lean_ctor_get(x_743, 1);
lean_inc(x_746);
lean_dec(x_743);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_740);
lean_ctor_set(x_660, 0, x_739);
x_747 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_747, 0, x_660);
lean_ctor_set(x_747, 1, x_746);
return x_747;
}
}
else
{
uint8_t x_748; 
x_748 = !lean_is_exclusive(x_743);
if (x_748 == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_749 = lean_ctor_get(x_743, 0);
x_750 = lean_io_error_to_string(x_749);
x_751 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_751, 0, x_750);
lean_ctor_set_uint8(x_751, sizeof(void*)*1, x_737);
x_752 = lean_array_push(x_740, x_751);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_752);
lean_ctor_set(x_660, 0, x_739);
lean_ctor_set_tag(x_743, 0);
lean_ctor_set(x_743, 0, x_660);
return x_743;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_753 = lean_ctor_get(x_743, 0);
x_754 = lean_ctor_get(x_743, 1);
lean_inc(x_754);
lean_inc(x_753);
lean_dec(x_743);
x_755 = lean_io_error_to_string(x_753);
x_756 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_756, 0, x_755);
lean_ctor_set_uint8(x_756, sizeof(void*)*1, x_737);
x_757 = lean_array_push(x_740, x_756);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_757);
lean_ctor_set(x_660, 0, x_739);
x_758 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_758, 0, x_660);
lean_ctor_set(x_758, 1, x_754);
return x_758;
}
}
}
else
{
uint8_t x_759; 
lean_dec(x_21);
x_759 = !lean_is_exclusive(x_741);
if (x_759 == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
x_760 = lean_ctor_get(x_741, 0);
x_761 = lean_io_error_to_string(x_760);
x_762 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set_uint8(x_762, sizeof(void*)*1, x_737);
x_763 = lean_array_push(x_740, x_762);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_763);
lean_ctor_set(x_660, 0, x_739);
lean_ctor_set_tag(x_741, 0);
lean_ctor_set(x_741, 0, x_660);
return x_741;
}
else
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_764 = lean_ctor_get(x_741, 0);
x_765 = lean_ctor_get(x_741, 1);
lean_inc(x_765);
lean_inc(x_764);
lean_dec(x_741);
x_766 = lean_io_error_to_string(x_764);
x_767 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set_uint8(x_767, sizeof(void*)*1, x_737);
x_768 = lean_array_push(x_740, x_767);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_768);
lean_ctor_set(x_660, 0, x_739);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_660);
lean_ctor_set(x_769, 1, x_765);
return x_769;
}
}
}
else
{
lean_object* x_770; lean_object* x_771; uint8_t x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_770 = lean_ctor_get(x_660, 1);
lean_inc(x_770);
lean_dec(x_660);
x_771 = lean_io_error_to_string(x_663);
x_772 = 3;
x_773 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set_uint8(x_773, sizeof(void*)*1, x_772);
x_774 = lean_array_get_size(x_770);
x_775 = lean_array_push(x_770, x_773);
x_776 = lean_io_prim_handle_unlock(x_556, x_661);
lean_dec(x_556);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; 
x_777 = lean_ctor_get(x_776, 1);
lean_inc(x_777);
lean_dec(x_776);
x_778 = lean_io_remove_file(x_21, x_777);
lean_dec(x_21);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_780 = x_778;
} else {
 lean_dec_ref(x_778);
 x_780 = lean_box(0);
}
x_781 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_781, 0, x_774);
lean_ctor_set(x_781, 1, x_775);
if (lean_is_scalar(x_780)) {
 x_782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_782 = x_780;
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_779);
return x_782;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_783 = lean_ctor_get(x_778, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_778, 1);
lean_inc(x_784);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_785 = x_778;
} else {
 lean_dec_ref(x_778);
 x_785 = lean_box(0);
}
x_786 = lean_io_error_to_string(x_783);
x_787 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_787, 0, x_786);
lean_ctor_set_uint8(x_787, sizeof(void*)*1, x_772);
x_788 = lean_array_push(x_775, x_787);
x_789 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_789, 0, x_774);
lean_ctor_set(x_789, 1, x_788);
if (lean_is_scalar(x_785)) {
 x_790 = lean_alloc_ctor(0, 2, 0);
} else {
 x_790 = x_785;
 lean_ctor_set_tag(x_790, 0);
}
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set(x_790, 1, x_784);
return x_790;
}
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_21);
x_791 = lean_ctor_get(x_776, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_776, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_793 = x_776;
} else {
 lean_dec_ref(x_776);
 x_793 = lean_box(0);
}
x_794 = lean_io_error_to_string(x_791);
x_795 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set_uint8(x_795, sizeof(void*)*1, x_772);
x_796 = lean_array_push(x_775, x_795);
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_774);
lean_ctor_set(x_797, 1, x_796);
if (lean_is_scalar(x_793)) {
 x_798 = lean_alloc_ctor(0, 2, 0);
} else {
 x_798 = x_793;
 lean_ctor_set_tag(x_798, 0);
}
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_792);
return x_798;
}
}
}
}
else
{
uint8_t x_799; 
lean_dec(x_662);
lean_dec(x_21);
x_799 = !lean_is_exclusive(x_660);
if (x_799 == 0)
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; lean_object* x_809; 
x_800 = lean_ctor_get(x_660, 1);
x_801 = lean_ctor_get(x_660, 0);
lean_dec(x_801);
x_802 = lean_ctor_get(x_1, 0);
lean_inc(x_802);
x_803 = l_Lake_Env_leanGithash(x_802);
lean_dec(x_802);
x_804 = l_System_Platform_target;
lean_inc(x_557);
if (lean_is_scalar(x_558)) {
 x_805 = lean_alloc_ctor(0, 4, 0);
} else {
 x_805 = x_558;
}
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_803);
lean_ctor_set(x_805, 2, x_27);
lean_ctor_set(x_805, 3, x_557);
x_806 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_805);
x_807 = lean_unsigned_to_nat(80u);
x_808 = l_Lean_Json_pretty(x_806, x_807);
x_809 = l_IO_FS_Handle_putStrLn(x_556, x_808, x_661);
if (lean_obj_tag(x_809) == 0)
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_ctor_get(x_809, 1);
lean_inc(x_810);
lean_dec(x_809);
x_811 = lean_io_prim_handle_truncate(x_556, x_810);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
lean_ctor_set(x_660, 0, x_812);
x_559 = x_660;
x_560 = x_813;
goto block_659;
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; uint8_t x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_814 = lean_ctor_get(x_811, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_811, 1);
lean_inc(x_815);
lean_dec(x_811);
x_816 = lean_io_error_to_string(x_814);
x_817 = 3;
x_818 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_818, 0, x_816);
lean_ctor_set_uint8(x_818, sizeof(void*)*1, x_817);
x_819 = lean_array_get_size(x_800);
x_820 = lean_array_push(x_800, x_818);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_820);
lean_ctor_set(x_660, 0, x_819);
x_559 = x_660;
x_560 = x_815;
goto block_659;
}
}
else
{
uint8_t x_821; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_821 = !lean_is_exclusive(x_809);
if (x_821 == 0)
{
lean_object* x_822; lean_object* x_823; uint8_t x_824; lean_object* x_825; lean_object* x_826; lean_object* x_827; 
x_822 = lean_ctor_get(x_809, 0);
x_823 = lean_io_error_to_string(x_822);
x_824 = 3;
x_825 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_825, 0, x_823);
lean_ctor_set_uint8(x_825, sizeof(void*)*1, x_824);
x_826 = lean_array_get_size(x_800);
x_827 = lean_array_push(x_800, x_825);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_827);
lean_ctor_set(x_660, 0, x_826);
lean_ctor_set_tag(x_809, 0);
lean_ctor_set(x_809, 0, x_660);
return x_809;
}
else
{
lean_object* x_828; lean_object* x_829; lean_object* x_830; uint8_t x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_828 = lean_ctor_get(x_809, 0);
x_829 = lean_ctor_get(x_809, 1);
lean_inc(x_829);
lean_inc(x_828);
lean_dec(x_809);
x_830 = lean_io_error_to_string(x_828);
x_831 = 3;
x_832 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set_uint8(x_832, sizeof(void*)*1, x_831);
x_833 = lean_array_get_size(x_800);
x_834 = lean_array_push(x_800, x_832);
lean_ctor_set_tag(x_660, 1);
lean_ctor_set(x_660, 1, x_834);
lean_ctor_set(x_660, 0, x_833);
x_835 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_835, 0, x_660);
lean_ctor_set(x_835, 1, x_829);
return x_835;
}
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_836 = lean_ctor_get(x_660, 1);
lean_inc(x_836);
lean_dec(x_660);
x_837 = lean_ctor_get(x_1, 0);
lean_inc(x_837);
x_838 = l_Lake_Env_leanGithash(x_837);
lean_dec(x_837);
x_839 = l_System_Platform_target;
lean_inc(x_557);
if (lean_is_scalar(x_558)) {
 x_840 = lean_alloc_ctor(0, 4, 0);
} else {
 x_840 = x_558;
}
lean_ctor_set(x_840, 0, x_839);
lean_ctor_set(x_840, 1, x_838);
lean_ctor_set(x_840, 2, x_27);
lean_ctor_set(x_840, 3, x_557);
x_841 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_840);
x_842 = lean_unsigned_to_nat(80u);
x_843 = l_Lean_Json_pretty(x_841, x_842);
x_844 = l_IO_FS_Handle_putStrLn(x_556, x_843, x_661);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; lean_object* x_846; 
x_845 = lean_ctor_get(x_844, 1);
lean_inc(x_845);
lean_dec(x_844);
x_846 = lean_io_prim_handle_truncate(x_556, x_845);
if (lean_obj_tag(x_846) == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_847 = lean_ctor_get(x_846, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_846, 1);
lean_inc(x_848);
lean_dec(x_846);
x_849 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_849, 0, x_847);
lean_ctor_set(x_849, 1, x_836);
x_559 = x_849;
x_560 = x_848;
goto block_659;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; uint8_t x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; 
x_850 = lean_ctor_get(x_846, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_846, 1);
lean_inc(x_851);
lean_dec(x_846);
x_852 = lean_io_error_to_string(x_850);
x_853 = 3;
x_854 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_854, 0, x_852);
lean_ctor_set_uint8(x_854, sizeof(void*)*1, x_853);
x_855 = lean_array_get_size(x_836);
x_856 = lean_array_push(x_836, x_854);
x_857 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
x_559 = x_857;
x_560 = x_851;
goto block_659;
}
}
else
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; uint8_t x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
lean_dec(x_557);
lean_dec(x_556);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_858 = lean_ctor_get(x_844, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_844, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_844)) {
 lean_ctor_release(x_844, 0);
 lean_ctor_release(x_844, 1);
 x_860 = x_844;
} else {
 lean_dec_ref(x_844);
 x_860 = lean_box(0);
}
x_861 = lean_io_error_to_string(x_858);
x_862 = 3;
x_863 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_863, 0, x_861);
lean_ctor_set_uint8(x_863, sizeof(void*)*1, x_862);
x_864 = lean_array_get_size(x_836);
x_865 = lean_array_push(x_836, x_863);
x_866 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_866, 0, x_864);
lean_ctor_set(x_866, 1, x_865);
if (lean_is_scalar(x_860)) {
 x_867 = lean_alloc_ctor(0, 2, 0);
} else {
 x_867 = x_860;
 lean_ctor_set_tag(x_867, 0);
}
lean_ctor_set(x_867, 0, x_866);
lean_ctor_set(x_867, 1, x_859);
return x_867;
}
}
}
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_935; lean_object* x_936; lean_object* x_1036; 
x_876 = lean_ctor_get(x_553, 0);
x_877 = lean_ctor_get(x_553, 1);
lean_inc(x_877);
lean_inc(x_876);
lean_dec(x_553);
x_878 = lean_ctor_get(x_551, 3);
lean_inc(x_878);
if (lean_is_exclusive(x_551)) {
 lean_ctor_release(x_551, 0);
 lean_ctor_release(x_551, 1);
 lean_ctor_release(x_551, 2);
 lean_ctor_release(x_551, 3);
 x_879 = x_551;
} else {
 lean_dec_ref(x_551);
 x_879 = lean_box(0);
}
x_1036 = lean_io_remove_file(x_18, x_554);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1037 = lean_ctor_get(x_1036, 0);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_1036, 1);
lean_inc(x_1038);
lean_dec(x_1036);
if (lean_is_scalar(x_552)) {
 x_1039 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1039 = x_552;
}
lean_ctor_set(x_1039, 0, x_1037);
x_1040 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1040, 0, x_1039);
lean_ctor_set(x_1040, 1, x_877);
x_935 = x_1040;
x_936 = x_1038;
goto block_1035;
}
else
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1041 = lean_ctor_get(x_1036, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1036, 1);
lean_inc(x_1042);
lean_dec(x_1036);
if (lean_is_scalar(x_552)) {
 x_1043 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1043 = x_552;
 lean_ctor_set_tag(x_1043, 0);
}
lean_ctor_set(x_1043, 0, x_1041);
x_1044 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1044, 0, x_1043);
lean_ctor_set(x_1044, 1, x_877);
x_935 = x_1044;
x_936 = x_1042;
goto block_1035;
}
block_934:
{
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
lean_dec(x_880);
x_883 = lean_ctor_get(x_1, 9);
lean_inc(x_883);
lean_dec(x_1);
x_884 = l_Lake_elabConfigFile(x_13, x_878, x_883, x_4, x_882, x_881);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; uint8_t x_890; lean_object* x_891; 
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
x_887 = lean_ctor_get(x_885, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_885, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_889 = x_885;
} else {
 lean_dec_ref(x_885);
 x_889 = lean_box(0);
}
x_890 = 0;
lean_inc(x_887);
x_891 = lean_write_module(x_887, x_18, x_890, x_886);
if (lean_obj_tag(x_891) == 0)
{
lean_object* x_892; lean_object* x_893; 
x_892 = lean_ctor_get(x_891, 1);
lean_inc(x_892);
lean_dec(x_891);
x_893 = lean_io_prim_handle_unlock(x_876, x_892);
lean_dec(x_876);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_894 = lean_ctor_get(x_893, 1);
lean_inc(x_894);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_895 = x_893;
} else {
 lean_dec_ref(x_893);
 x_895 = lean_box(0);
}
if (lean_is_scalar(x_889)) {
 x_896 = lean_alloc_ctor(0, 2, 0);
} else {
 x_896 = x_889;
}
lean_ctor_set(x_896, 0, x_887);
lean_ctor_set(x_896, 1, x_888);
if (lean_is_scalar(x_895)) {
 x_897 = lean_alloc_ctor(0, 2, 0);
} else {
 x_897 = x_895;
}
lean_ctor_set(x_897, 0, x_896);
lean_ctor_set(x_897, 1, x_894);
return x_897;
}
else
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; uint8_t x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_887);
x_898 = lean_ctor_get(x_893, 0);
lean_inc(x_898);
x_899 = lean_ctor_get(x_893, 1);
lean_inc(x_899);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_900 = x_893;
} else {
 lean_dec_ref(x_893);
 x_900 = lean_box(0);
}
x_901 = lean_io_error_to_string(x_898);
x_902 = 3;
x_903 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_903, 0, x_901);
lean_ctor_set_uint8(x_903, sizeof(void*)*1, x_902);
x_904 = lean_array_get_size(x_888);
x_905 = lean_array_push(x_888, x_903);
if (lean_is_scalar(x_889)) {
 x_906 = lean_alloc_ctor(1, 2, 0);
} else {
 x_906 = x_889;
 lean_ctor_set_tag(x_906, 1);
}
lean_ctor_set(x_906, 0, x_904);
lean_ctor_set(x_906, 1, x_905);
if (lean_is_scalar(x_900)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_900;
 lean_ctor_set_tag(x_907, 0);
}
lean_ctor_set(x_907, 0, x_906);
lean_ctor_set(x_907, 1, x_899);
return x_907;
}
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; uint8_t x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
lean_dec(x_887);
lean_dec(x_876);
x_908 = lean_ctor_get(x_891, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_891, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_891)) {
 lean_ctor_release(x_891, 0);
 lean_ctor_release(x_891, 1);
 x_910 = x_891;
} else {
 lean_dec_ref(x_891);
 x_910 = lean_box(0);
}
x_911 = lean_io_error_to_string(x_908);
x_912 = 3;
x_913 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_913, 0, x_911);
lean_ctor_set_uint8(x_913, sizeof(void*)*1, x_912);
x_914 = lean_array_get_size(x_888);
x_915 = lean_array_push(x_888, x_913);
if (lean_is_scalar(x_889)) {
 x_916 = lean_alloc_ctor(1, 2, 0);
} else {
 x_916 = x_889;
 lean_ctor_set_tag(x_916, 1);
}
lean_ctor_set(x_916, 0, x_914);
lean_ctor_set(x_916, 1, x_915);
if (lean_is_scalar(x_910)) {
 x_917 = lean_alloc_ctor(0, 2, 0);
} else {
 x_917 = x_910;
 lean_ctor_set_tag(x_917, 0);
}
lean_ctor_set(x_917, 0, x_916);
lean_ctor_set(x_917, 1, x_909);
return x_917;
}
}
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec(x_876);
lean_dec(x_18);
x_918 = lean_ctor_get(x_884, 1);
lean_inc(x_918);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 x_919 = x_884;
} else {
 lean_dec_ref(x_884);
 x_919 = lean_box(0);
}
x_920 = lean_ctor_get(x_885, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_885, 1);
lean_inc(x_921);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_922 = x_885;
} else {
 lean_dec_ref(x_885);
 x_922 = lean_box(0);
}
if (lean_is_scalar(x_922)) {
 x_923 = lean_alloc_ctor(1, 2, 0);
} else {
 x_923 = x_922;
}
lean_ctor_set(x_923, 0, x_920);
lean_ctor_set(x_923, 1, x_921);
if (lean_is_scalar(x_919)) {
 x_924 = lean_alloc_ctor(0, 2, 0);
} else {
 x_924 = x_919;
}
lean_ctor_set(x_924, 0, x_923);
lean_ctor_set(x_924, 1, x_918);
return x_924;
}
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_876);
lean_dec(x_18);
x_925 = lean_ctor_get(x_884, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_884, 1);
lean_inc(x_926);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 x_927 = x_884;
} else {
 lean_dec_ref(x_884);
 x_927 = lean_box(0);
}
if (lean_is_scalar(x_927)) {
 x_928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_928 = x_927;
}
lean_ctor_set(x_928, 0, x_925);
lean_ctor_set(x_928, 1, x_926);
return x_928;
}
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
lean_dec(x_878);
lean_dec(x_876);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_929 = lean_ctor_get(x_880, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_880, 1);
lean_inc(x_930);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_931 = x_880;
} else {
 lean_dec_ref(x_880);
 x_931 = lean_box(0);
}
if (lean_is_scalar(x_931)) {
 x_932 = lean_alloc_ctor(1, 2, 0);
} else {
 x_932 = x_931;
}
lean_ctor_set(x_932, 0, x_929);
lean_ctor_set(x_932, 1, x_930);
x_933 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_933, 0, x_932);
lean_ctor_set(x_933, 1, x_881);
return x_933;
}
}
block_1035:
{
lean_object* x_937; 
x_937 = lean_ctor_get(x_935, 0);
lean_inc(x_937);
if (lean_obj_tag(x_937) == 0)
{
lean_object* x_938; 
x_938 = lean_ctor_get(x_937, 0);
lean_inc(x_938);
lean_dec(x_937);
if (lean_obj_tag(x_938) == 11)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; 
lean_dec(x_938);
lean_dec(x_21);
x_939 = lean_ctor_get(x_935, 1);
lean_inc(x_939);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_940 = x_935;
} else {
 lean_dec_ref(x_935);
 x_940 = lean_box(0);
}
x_941 = lean_ctor_get(x_1, 0);
lean_inc(x_941);
x_942 = l_Lake_Env_leanGithash(x_941);
lean_dec(x_941);
x_943 = l_System_Platform_target;
lean_inc(x_878);
if (lean_is_scalar(x_879)) {
 x_944 = lean_alloc_ctor(0, 4, 0);
} else {
 x_944 = x_879;
}
lean_ctor_set(x_944, 0, x_943);
lean_ctor_set(x_944, 1, x_942);
lean_ctor_set(x_944, 2, x_27);
lean_ctor_set(x_944, 3, x_878);
x_945 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_944);
x_946 = lean_unsigned_to_nat(80u);
x_947 = l_Lean_Json_pretty(x_945, x_946);
x_948 = l_IO_FS_Handle_putStrLn(x_876, x_947, x_936);
if (lean_obj_tag(x_948) == 0)
{
lean_object* x_949; lean_object* x_950; 
x_949 = lean_ctor_get(x_948, 1);
lean_inc(x_949);
lean_dec(x_948);
x_950 = lean_io_prim_handle_truncate(x_876, x_949);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; lean_object* x_953; 
x_951 = lean_ctor_get(x_950, 0);
lean_inc(x_951);
x_952 = lean_ctor_get(x_950, 1);
lean_inc(x_952);
lean_dec(x_950);
if (lean_is_scalar(x_940)) {
 x_953 = lean_alloc_ctor(0, 2, 0);
} else {
 x_953 = x_940;
}
lean_ctor_set(x_953, 0, x_951);
lean_ctor_set(x_953, 1, x_939);
x_880 = x_953;
x_881 = x_952;
goto block_934;
}
else
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; uint8_t x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; 
x_954 = lean_ctor_get(x_950, 0);
lean_inc(x_954);
x_955 = lean_ctor_get(x_950, 1);
lean_inc(x_955);
lean_dec(x_950);
x_956 = lean_io_error_to_string(x_954);
x_957 = 3;
x_958 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_958, 0, x_956);
lean_ctor_set_uint8(x_958, sizeof(void*)*1, x_957);
x_959 = lean_array_get_size(x_939);
x_960 = lean_array_push(x_939, x_958);
if (lean_is_scalar(x_940)) {
 x_961 = lean_alloc_ctor(1, 2, 0);
} else {
 x_961 = x_940;
 lean_ctor_set_tag(x_961, 1);
}
lean_ctor_set(x_961, 0, x_959);
lean_ctor_set(x_961, 1, x_960);
x_880 = x_961;
x_881 = x_955;
goto block_934;
}
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; uint8_t x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; 
lean_dec(x_878);
lean_dec(x_876);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_962 = lean_ctor_get(x_948, 0);
lean_inc(x_962);
x_963 = lean_ctor_get(x_948, 1);
lean_inc(x_963);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_964 = x_948;
} else {
 lean_dec_ref(x_948);
 x_964 = lean_box(0);
}
x_965 = lean_io_error_to_string(x_962);
x_966 = 3;
x_967 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_967, 0, x_965);
lean_ctor_set_uint8(x_967, sizeof(void*)*1, x_966);
x_968 = lean_array_get_size(x_939);
x_969 = lean_array_push(x_939, x_967);
if (lean_is_scalar(x_940)) {
 x_970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_970 = x_940;
 lean_ctor_set_tag(x_970, 1);
}
lean_ctor_set(x_970, 0, x_968);
lean_ctor_set(x_970, 1, x_969);
if (lean_is_scalar(x_964)) {
 x_971 = lean_alloc_ctor(0, 2, 0);
} else {
 x_971 = x_964;
 lean_ctor_set_tag(x_971, 0);
}
lean_ctor_set(x_971, 0, x_970);
lean_ctor_set(x_971, 1, x_963);
return x_971;
}
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; uint8_t x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
lean_dec(x_879);
lean_dec(x_878);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_972 = lean_ctor_get(x_935, 1);
lean_inc(x_972);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_973 = x_935;
} else {
 lean_dec_ref(x_935);
 x_973 = lean_box(0);
}
x_974 = lean_io_error_to_string(x_938);
x_975 = 3;
x_976 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_976, 0, x_974);
lean_ctor_set_uint8(x_976, sizeof(void*)*1, x_975);
x_977 = lean_array_get_size(x_972);
x_978 = lean_array_push(x_972, x_976);
x_979 = lean_io_prim_handle_unlock(x_876, x_936);
lean_dec(x_876);
if (lean_obj_tag(x_979) == 0)
{
lean_object* x_980; lean_object* x_981; 
x_980 = lean_ctor_get(x_979, 1);
lean_inc(x_980);
lean_dec(x_979);
x_981 = lean_io_remove_file(x_21, x_980);
lean_dec(x_21);
if (lean_obj_tag(x_981) == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_982 = lean_ctor_get(x_981, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_983 = x_981;
} else {
 lean_dec_ref(x_981);
 x_983 = lean_box(0);
}
if (lean_is_scalar(x_973)) {
 x_984 = lean_alloc_ctor(1, 2, 0);
} else {
 x_984 = x_973;
 lean_ctor_set_tag(x_984, 1);
}
lean_ctor_set(x_984, 0, x_977);
lean_ctor_set(x_984, 1, x_978);
if (lean_is_scalar(x_983)) {
 x_985 = lean_alloc_ctor(0, 2, 0);
} else {
 x_985 = x_983;
}
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_982);
return x_985;
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; 
x_986 = lean_ctor_get(x_981, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_981, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_981)) {
 lean_ctor_release(x_981, 0);
 lean_ctor_release(x_981, 1);
 x_988 = x_981;
} else {
 lean_dec_ref(x_981);
 x_988 = lean_box(0);
}
x_989 = lean_io_error_to_string(x_986);
x_990 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_990, 0, x_989);
lean_ctor_set_uint8(x_990, sizeof(void*)*1, x_975);
x_991 = lean_array_push(x_978, x_990);
if (lean_is_scalar(x_973)) {
 x_992 = lean_alloc_ctor(1, 2, 0);
} else {
 x_992 = x_973;
 lean_ctor_set_tag(x_992, 1);
}
lean_ctor_set(x_992, 0, x_977);
lean_ctor_set(x_992, 1, x_991);
if (lean_is_scalar(x_988)) {
 x_993 = lean_alloc_ctor(0, 2, 0);
} else {
 x_993 = x_988;
 lean_ctor_set_tag(x_993, 0);
}
lean_ctor_set(x_993, 0, x_992);
lean_ctor_set(x_993, 1, x_987);
return x_993;
}
}
else
{
lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_21);
x_994 = lean_ctor_get(x_979, 0);
lean_inc(x_994);
x_995 = lean_ctor_get(x_979, 1);
lean_inc(x_995);
if (lean_is_exclusive(x_979)) {
 lean_ctor_release(x_979, 0);
 lean_ctor_release(x_979, 1);
 x_996 = x_979;
} else {
 lean_dec_ref(x_979);
 x_996 = lean_box(0);
}
x_997 = lean_io_error_to_string(x_994);
x_998 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set_uint8(x_998, sizeof(void*)*1, x_975);
x_999 = lean_array_push(x_978, x_998);
if (lean_is_scalar(x_973)) {
 x_1000 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1000 = x_973;
 lean_ctor_set_tag(x_1000, 1);
}
lean_ctor_set(x_1000, 0, x_977);
lean_ctor_set(x_1000, 1, x_999);
if (lean_is_scalar(x_996)) {
 x_1001 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1001 = x_996;
 lean_ctor_set_tag(x_1001, 0);
}
lean_ctor_set(x_1001, 0, x_1000);
lean_ctor_set(x_1001, 1, x_995);
return x_1001;
}
}
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_937);
lean_dec(x_21);
x_1002 = lean_ctor_get(x_935, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_1003 = x_935;
} else {
 lean_dec_ref(x_935);
 x_1003 = lean_box(0);
}
x_1004 = lean_ctor_get(x_1, 0);
lean_inc(x_1004);
x_1005 = l_Lake_Env_leanGithash(x_1004);
lean_dec(x_1004);
x_1006 = l_System_Platform_target;
lean_inc(x_878);
if (lean_is_scalar(x_879)) {
 x_1007 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1007 = x_879;
}
lean_ctor_set(x_1007, 0, x_1006);
lean_ctor_set(x_1007, 1, x_1005);
lean_ctor_set(x_1007, 2, x_27);
lean_ctor_set(x_1007, 3, x_878);
x_1008 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1007);
x_1009 = lean_unsigned_to_nat(80u);
x_1010 = l_Lean_Json_pretty(x_1008, x_1009);
x_1011 = l_IO_FS_Handle_putStrLn(x_876, x_1010, x_936);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; lean_object* x_1013; 
x_1012 = lean_ctor_get(x_1011, 1);
lean_inc(x_1012);
lean_dec(x_1011);
x_1013 = lean_io_prim_handle_truncate(x_876, x_1012);
if (lean_obj_tag(x_1013) == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_1013, 0);
lean_inc(x_1014);
x_1015 = lean_ctor_get(x_1013, 1);
lean_inc(x_1015);
lean_dec(x_1013);
if (lean_is_scalar(x_1003)) {
 x_1016 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1016 = x_1003;
}
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1002);
x_880 = x_1016;
x_881 = x_1015;
goto block_934;
}
else
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
x_1017 = lean_ctor_get(x_1013, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1013, 1);
lean_inc(x_1018);
lean_dec(x_1013);
x_1019 = lean_io_error_to_string(x_1017);
x_1020 = 3;
x_1021 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1021, 0, x_1019);
lean_ctor_set_uint8(x_1021, sizeof(void*)*1, x_1020);
x_1022 = lean_array_get_size(x_1002);
x_1023 = lean_array_push(x_1002, x_1021);
if (lean_is_scalar(x_1003)) {
 x_1024 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1024 = x_1003;
 lean_ctor_set_tag(x_1024, 1);
}
lean_ctor_set(x_1024, 0, x_1022);
lean_ctor_set(x_1024, 1, x_1023);
x_880 = x_1024;
x_881 = x_1018;
goto block_934;
}
}
else
{
lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; uint8_t x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
lean_dec(x_878);
lean_dec(x_876);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1025 = lean_ctor_get(x_1011, 0);
lean_inc(x_1025);
x_1026 = lean_ctor_get(x_1011, 1);
lean_inc(x_1026);
if (lean_is_exclusive(x_1011)) {
 lean_ctor_release(x_1011, 0);
 lean_ctor_release(x_1011, 1);
 x_1027 = x_1011;
} else {
 lean_dec_ref(x_1011);
 x_1027 = lean_box(0);
}
x_1028 = lean_io_error_to_string(x_1025);
x_1029 = 3;
x_1030 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1030, 0, x_1028);
lean_ctor_set_uint8(x_1030, sizeof(void*)*1, x_1029);
x_1031 = lean_array_get_size(x_1002);
x_1032 = lean_array_push(x_1002, x_1030);
if (lean_is_scalar(x_1003)) {
 x_1033 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1033 = x_1003;
 lean_ctor_set_tag(x_1033, 1);
}
lean_ctor_set(x_1033, 0, x_1031);
lean_ctor_set(x_1033, 1, x_1032);
if (lean_is_scalar(x_1027)) {
 x_1034 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1034 = x_1027;
 lean_ctor_set_tag(x_1034, 0);
}
lean_ctor_set(x_1034, 0, x_1033);
lean_ctor_set(x_1034, 1, x_1026);
return x_1034;
}
}
}
}
}
else
{
uint8_t x_1045; 
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1045 = !lean_is_exclusive(x_553);
if (x_1045 == 0)
{
lean_object* x_1046; 
x_1046 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1046, 0, x_553);
lean_ctor_set(x_1046, 1, x_554);
return x_1046;
}
else
{
lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
x_1047 = lean_ctor_get(x_553, 0);
x_1048 = lean_ctor_get(x_553, 1);
lean_inc(x_1048);
lean_inc(x_1047);
lean_dec(x_553);
x_1049 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1049, 0, x_1047);
lean_ctor_set(x_1049, 1, x_1048);
x_1050 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1050, 0, x_1049);
lean_ctor_set(x_1050, 1, x_554);
return x_1050;
}
}
}
block_1103:
{
lean_object* x_1056; lean_object* x_1057; uint8_t x_1065; lean_object* x_1066; 
lean_dec(x_1055);
x_1065 = 1;
x_1066 = lean_io_prim_handle_mk(x_24, x_1065, x_1054);
lean_dec(x_24);
if (lean_obj_tag(x_1066) == 0)
{
lean_object* x_1067; lean_object* x_1068; uint8_t x_1069; lean_object* x_1070; 
x_1067 = lean_ctor_get(x_1066, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1066, 1);
lean_inc(x_1068);
lean_dec(x_1066);
x_1069 = 1;
x_1070 = lean_io_prim_handle_try_lock(x_1067, x_1069, x_1068);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; uint8_t x_1072; 
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_unbox(x_1071);
lean_dec(x_1071);
if (x_1072 == 0)
{
lean_object* x_1073; lean_object* x_1074; 
lean_dec(x_1067);
lean_dec(x_531);
x_1073 = lean_ctor_get(x_1070, 1);
lean_inc(x_1073);
lean_dec(x_1070);
x_1074 = lean_io_prim_handle_unlock(x_529, x_1073);
lean_dec(x_529);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; 
x_1075 = lean_ctor_get(x_1074, 1);
lean_inc(x_1075);
lean_dec(x_1074);
x_1076 = l_Lake_importConfigFile___closed__12;
x_1056 = x_1076;
x_1057 = x_1075;
goto block_1064;
}
else
{
lean_object* x_1077; lean_object* x_1078; 
x_1077 = lean_ctor_get(x_1074, 0);
lean_inc(x_1077);
x_1078 = lean_ctor_get(x_1074, 1);
lean_inc(x_1078);
lean_dec(x_1074);
x_1056 = x_1077;
x_1057 = x_1078;
goto block_1064;
}
}
else
{
lean_object* x_1079; lean_object* x_1080; 
x_1079 = lean_ctor_get(x_1070, 1);
lean_inc(x_1079);
lean_dec(x_1070);
x_1080 = lean_io_prim_handle_unlock(x_529, x_1079);
lean_dec(x_529);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; uint8_t x_1082; lean_object* x_1083; 
x_1081 = lean_ctor_get(x_1080, 1);
lean_inc(x_1081);
lean_dec(x_1080);
x_1082 = 3;
x_1083 = lean_io_prim_handle_mk(x_21, x_1082, x_1081);
if (lean_obj_tag(x_1083) == 0)
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; 
x_1084 = lean_ctor_get(x_1083, 0);
lean_inc(x_1084);
x_1085 = lean_ctor_get(x_1083, 1);
lean_inc(x_1085);
lean_dec(x_1083);
x_1086 = lean_io_prim_handle_lock(x_1084, x_1069, x_1085);
if (lean_obj_tag(x_1086) == 0)
{
lean_object* x_1087; lean_object* x_1088; 
x_1087 = lean_ctor_get(x_1086, 1);
lean_inc(x_1087);
lean_dec(x_1086);
x_1088 = lean_io_prim_handle_unlock(x_1067, x_1087);
lean_dec(x_1067);
if (lean_obj_tag(x_1088) == 0)
{
lean_object* x_1089; lean_object* x_1090; 
lean_dec(x_536);
x_1089 = lean_ctor_get(x_1088, 1);
lean_inc(x_1089);
lean_dec(x_1088);
if (lean_is_scalar(x_531)) {
 x_1090 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1090 = x_531;
}
lean_ctor_set(x_1090, 0, x_1084);
lean_ctor_set(x_1090, 1, x_535);
x_553 = x_1090;
x_554 = x_1089;
goto block_1051;
}
else
{
lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_1084);
lean_dec(x_531);
x_1091 = lean_ctor_get(x_1088, 0);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_1088, 1);
lean_inc(x_1092);
lean_dec(x_1088);
x_1056 = x_1091;
x_1057 = x_1092;
goto block_1064;
}
}
else
{
lean_object* x_1093; lean_object* x_1094; 
lean_dec(x_1084);
lean_dec(x_1067);
lean_dec(x_531);
x_1093 = lean_ctor_get(x_1086, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1086, 1);
lean_inc(x_1094);
lean_dec(x_1086);
x_1056 = x_1093;
x_1057 = x_1094;
goto block_1064;
}
}
else
{
lean_object* x_1095; lean_object* x_1096; 
lean_dec(x_1067);
lean_dec(x_531);
x_1095 = lean_ctor_get(x_1083, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1083, 1);
lean_inc(x_1096);
lean_dec(x_1083);
x_1056 = x_1095;
x_1057 = x_1096;
goto block_1064;
}
}
else
{
lean_object* x_1097; lean_object* x_1098; 
lean_dec(x_1067);
lean_dec(x_531);
x_1097 = lean_ctor_get(x_1080, 0);
lean_inc(x_1097);
x_1098 = lean_ctor_get(x_1080, 1);
lean_inc(x_1098);
lean_dec(x_1080);
x_1056 = x_1097;
x_1057 = x_1098;
goto block_1064;
}
}
}
else
{
lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_1067);
lean_dec(x_531);
lean_dec(x_529);
x_1099 = lean_ctor_get(x_1070, 0);
lean_inc(x_1099);
x_1100 = lean_ctor_get(x_1070, 1);
lean_inc(x_1100);
lean_dec(x_1070);
x_1056 = x_1099;
x_1057 = x_1100;
goto block_1064;
}
}
else
{
lean_object* x_1101; lean_object* x_1102; 
lean_dec(x_531);
lean_dec(x_529);
x_1101 = lean_ctor_get(x_1066, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1066, 1);
lean_inc(x_1102);
lean_dec(x_1066);
x_1056 = x_1101;
x_1057 = x_1102;
goto block_1064;
}
block_1064:
{
lean_object* x_1058; uint8_t x_1059; lean_object* x_1060; lean_object* x_1061; lean_object* x_1062; lean_object* x_1063; 
x_1058 = lean_io_error_to_string(x_1056);
x_1059 = 3;
x_1060 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1060, 0, x_1058);
lean_ctor_set_uint8(x_1060, sizeof(void*)*1, x_1059);
x_1061 = lean_array_get_size(x_535);
x_1062 = lean_array_push(x_535, x_1060);
if (lean_is_scalar(x_536)) {
 x_1063 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1063 = x_536;
 lean_ctor_set_tag(x_1063, 1);
}
lean_ctor_set(x_1063, 0, x_1061);
lean_ctor_set(x_1063, 1, x_1062);
x_553 = x_1063;
x_554 = x_1057;
goto block_1051;
}
}
}
}
}
else
{
uint8_t x_1165; 
lean_dec(x_531);
lean_dec(x_529);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1165 = !lean_is_exclusive(x_532);
if (x_1165 == 0)
{
lean_object* x_1166; 
x_1166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1166, 0, x_532);
lean_ctor_set(x_1166, 1, x_533);
return x_1166;
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
x_1167 = lean_ctor_get(x_532, 0);
x_1168 = lean_ctor_get(x_532, 1);
lean_inc(x_1168);
lean_inc(x_1167);
lean_dec(x_532);
x_1169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1169, 0, x_1167);
lean_ctor_set(x_1169, 1, x_1168);
x_1170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1170, 0, x_1169);
lean_ctor_set(x_1170, 1, x_533);
return x_1170;
}
}
}
}
else
{
uint8_t x_1265; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_1265 = !lean_is_exclusive(x_527);
if (x_1265 == 0)
{
lean_object* x_1266; 
x_1266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1266, 0, x_527);
lean_ctor_set(x_1266, 1, x_528);
return x_1266;
}
else
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; 
x_1267 = lean_ctor_get(x_527, 0);
x_1268 = lean_ctor_get(x_527, 1);
lean_inc(x_1268);
lean_inc(x_1267);
lean_dec(x_527);
x_1269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1269, 0, x_1267);
lean_ctor_set(x_1269, 1, x_1268);
x_1270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1270, 0, x_1269);
lean_ctor_set(x_1270, 1, x_528);
return x_1270;
}
}
}
block_2025:
{
lean_object* x_1274; 
x_1274 = lean_ctor_get(x_1272, 0);
lean_inc(x_1274);
if (lean_obj_tag(x_1274) == 0)
{
lean_object* x_1275; 
x_1275 = lean_ctor_get(x_1274, 0);
lean_inc(x_1275);
lean_dec(x_1274);
if (lean_obj_tag(x_1275) == 0)
{
uint8_t x_1276; 
lean_dec(x_1275);
x_1276 = !lean_is_exclusive(x_1272);
if (x_1276 == 0)
{
lean_object* x_1277; lean_object* x_1278; uint8_t x_1279; lean_object* x_1280; 
x_1277 = lean_ctor_get(x_1272, 1);
x_1278 = lean_ctor_get(x_1272, 0);
lean_dec(x_1278);
x_1279 = 0;
x_1280 = lean_io_prim_handle_mk(x_21, x_1279, x_1273);
if (lean_obj_tag(x_1280) == 0)
{
lean_object* x_1281; lean_object* x_1282; 
x_1281 = lean_ctor_get(x_1280, 0);
lean_inc(x_1281);
x_1282 = lean_ctor_get(x_1280, 1);
lean_inc(x_1282);
lean_dec(x_1280);
lean_ctor_set(x_1272, 0, x_1281);
x_527 = x_1272;
x_528 = x_1282;
goto block_1271;
}
else
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; uint8_t x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
x_1283 = lean_ctor_get(x_1280, 0);
lean_inc(x_1283);
x_1284 = lean_ctor_get(x_1280, 1);
lean_inc(x_1284);
lean_dec(x_1280);
x_1285 = lean_io_error_to_string(x_1283);
x_1286 = 3;
x_1287 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1287, 0, x_1285);
lean_ctor_set_uint8(x_1287, sizeof(void*)*1, x_1286);
x_1288 = lean_array_get_size(x_1277);
x_1289 = lean_array_push(x_1277, x_1287);
lean_ctor_set_tag(x_1272, 1);
lean_ctor_set(x_1272, 1, x_1289);
lean_ctor_set(x_1272, 0, x_1288);
x_527 = x_1272;
x_528 = x_1284;
goto block_1271;
}
}
else
{
lean_object* x_1290; uint8_t x_1291; lean_object* x_1292; 
x_1290 = lean_ctor_get(x_1272, 1);
lean_inc(x_1290);
lean_dec(x_1272);
x_1291 = 0;
x_1292 = lean_io_prim_handle_mk(x_21, x_1291, x_1273);
if (lean_obj_tag(x_1292) == 0)
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; 
x_1293 = lean_ctor_get(x_1292, 0);
lean_inc(x_1293);
x_1294 = lean_ctor_get(x_1292, 1);
lean_inc(x_1294);
lean_dec(x_1292);
x_1295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1295, 0, x_1293);
lean_ctor_set(x_1295, 1, x_1290);
x_527 = x_1295;
x_528 = x_1294;
goto block_1271;
}
else
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; uint8_t x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; 
x_1296 = lean_ctor_get(x_1292, 0);
lean_inc(x_1296);
x_1297 = lean_ctor_get(x_1292, 1);
lean_inc(x_1297);
lean_dec(x_1292);
x_1298 = lean_io_error_to_string(x_1296);
x_1299 = 3;
x_1300 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1300, 0, x_1298);
lean_ctor_set_uint8(x_1300, sizeof(void*)*1, x_1299);
x_1301 = lean_array_get_size(x_1290);
x_1302 = lean_array_push(x_1290, x_1300);
x_1303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1303, 0, x_1301);
lean_ctor_set(x_1303, 1, x_1302);
x_527 = x_1303;
x_528 = x_1297;
goto block_1271;
}
}
}
else
{
uint8_t x_1304; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_1304 = !lean_is_exclusive(x_1272);
if (x_1304 == 0)
{
lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; uint8_t x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
x_1305 = lean_ctor_get(x_1272, 1);
x_1306 = lean_ctor_get(x_1272, 0);
lean_dec(x_1306);
x_1307 = lean_io_error_to_string(x_1275);
x_1308 = 3;
x_1309 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1309, 0, x_1307);
lean_ctor_set_uint8(x_1309, sizeof(void*)*1, x_1308);
x_1310 = lean_array_get_size(x_1305);
x_1311 = lean_array_push(x_1305, x_1309);
lean_ctor_set_tag(x_1272, 1);
lean_ctor_set(x_1272, 1, x_1311);
lean_ctor_set(x_1272, 0, x_1310);
x_1312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1312, 0, x_1272);
lean_ctor_set(x_1312, 1, x_1273);
return x_1312;
}
else
{
lean_object* x_1313; lean_object* x_1314; uint8_t x_1315; lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; 
x_1313 = lean_ctor_get(x_1272, 1);
lean_inc(x_1313);
lean_dec(x_1272);
x_1314 = lean_io_error_to_string(x_1275);
x_1315 = 3;
x_1316 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1316, 0, x_1314);
lean_ctor_set_uint8(x_1316, sizeof(void*)*1, x_1315);
x_1317 = lean_array_get_size(x_1313);
x_1318 = lean_array_push(x_1313, x_1316);
x_1319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1319, 0, x_1317);
lean_ctor_set(x_1319, 1, x_1318);
x_1320 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1320, 0, x_1319);
lean_ctor_set(x_1320, 1, x_1273);
return x_1320;
}
}
}
else
{
uint8_t x_1321; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_12);
x_1321 = !lean_is_exclusive(x_1272);
if (x_1321 == 0)
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; uint8_t x_1822; lean_object* x_1823; 
x_1322 = lean_ctor_get(x_1272, 1);
x_1323 = lean_ctor_get(x_1272, 0);
lean_dec(x_1323);
x_1324 = lean_ctor_get(x_1274, 0);
lean_inc(x_1324);
if (lean_is_exclusive(x_1274)) {
 lean_ctor_release(x_1274, 0);
 x_1325 = x_1274;
} else {
 lean_dec_ref(x_1274);
 x_1325 = lean_box(0);
}
x_1822 = 1;
x_1823 = lean_io_prim_handle_lock(x_1324, x_1822, x_1273);
if (lean_obj_tag(x_1823) == 0)
{
lean_object* x_1824; lean_object* x_1825; 
x_1824 = lean_ctor_get(x_1823, 0);
lean_inc(x_1824);
x_1825 = lean_ctor_get(x_1823, 1);
lean_inc(x_1825);
lean_dec(x_1823);
lean_ctor_set(x_1272, 0, x_1824);
x_1326 = x_1272;
x_1327 = x_1825;
goto block_1821;
}
else
{
lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; uint8_t x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; 
x_1826 = lean_ctor_get(x_1823, 0);
lean_inc(x_1826);
x_1827 = lean_ctor_get(x_1823, 1);
lean_inc(x_1827);
lean_dec(x_1823);
x_1828 = lean_io_error_to_string(x_1826);
x_1829 = 3;
x_1830 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1830, 0, x_1828);
lean_ctor_set_uint8(x_1830, sizeof(void*)*1, x_1829);
x_1831 = lean_array_get_size(x_1322);
x_1832 = lean_array_push(x_1322, x_1830);
lean_ctor_set_tag(x_1272, 1);
lean_ctor_set(x_1272, 1, x_1832);
lean_ctor_set(x_1272, 0, x_1831);
x_1326 = x_1272;
x_1327 = x_1827;
goto block_1821;
}
block_1821:
{
if (lean_obj_tag(x_1326) == 0)
{
uint8_t x_1328; 
x_1328 = !lean_is_exclusive(x_1326);
if (x_1328 == 0)
{
lean_object* x_1329; lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; lean_object* x_1432; lean_object* x_1433; lean_object* x_1641; 
x_1329 = lean_ctor_get(x_1326, 0);
lean_dec(x_1329);
x_1330 = lean_ctor_get(x_1, 8);
lean_inc(x_1330);
x_1641 = lean_io_remove_file(x_18, x_1327);
if (lean_obj_tag(x_1641) == 0)
{
lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; 
x_1642 = lean_ctor_get(x_1641, 0);
lean_inc(x_1642);
x_1643 = lean_ctor_get(x_1641, 1);
lean_inc(x_1643);
lean_dec(x_1641);
if (lean_is_scalar(x_1325)) {
 x_1644 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1644 = x_1325;
}
lean_ctor_set(x_1644, 0, x_1642);
lean_ctor_set(x_1326, 0, x_1644);
x_1432 = x_1326;
x_1433 = x_1643;
goto block_1640;
}
else
{
lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; 
x_1645 = lean_ctor_get(x_1641, 0);
lean_inc(x_1645);
x_1646 = lean_ctor_get(x_1641, 1);
lean_inc(x_1646);
lean_dec(x_1641);
if (lean_is_scalar(x_1325)) {
 x_1647 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1647 = x_1325;
 lean_ctor_set_tag(x_1647, 0);
}
lean_ctor_set(x_1647, 0, x_1645);
lean_ctor_set(x_1326, 0, x_1647);
x_1432 = x_1326;
x_1433 = x_1646;
goto block_1640;
}
block_1431:
{
if (lean_obj_tag(x_1331) == 0)
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1333 = lean_ctor_get(x_1331, 1);
lean_inc(x_1333);
lean_dec(x_1331);
x_1334 = lean_ctor_get(x_1, 9);
lean_inc(x_1334);
lean_dec(x_1);
x_1335 = l_Lake_elabConfigFile(x_13, x_1330, x_1334, x_4, x_1333, x_1332);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; 
x_1336 = lean_ctor_get(x_1335, 0);
lean_inc(x_1336);
if (lean_obj_tag(x_1336) == 0)
{
lean_object* x_1337; uint8_t x_1338; 
x_1337 = lean_ctor_get(x_1335, 1);
lean_inc(x_1337);
lean_dec(x_1335);
x_1338 = !lean_is_exclusive(x_1336);
if (x_1338 == 0)
{
lean_object* x_1339; lean_object* x_1340; uint8_t x_1341; lean_object* x_1342; 
x_1339 = lean_ctor_get(x_1336, 0);
x_1340 = lean_ctor_get(x_1336, 1);
x_1341 = 0;
lean_inc(x_1339);
x_1342 = lean_write_module(x_1339, x_18, x_1341, x_1337);
if (lean_obj_tag(x_1342) == 0)
{
lean_object* x_1343; lean_object* x_1344; 
x_1343 = lean_ctor_get(x_1342, 1);
lean_inc(x_1343);
lean_dec(x_1342);
x_1344 = lean_io_prim_handle_unlock(x_1324, x_1343);
lean_dec(x_1324);
if (lean_obj_tag(x_1344) == 0)
{
uint8_t x_1345; 
x_1345 = !lean_is_exclusive(x_1344);
if (x_1345 == 0)
{
lean_object* x_1346; 
x_1346 = lean_ctor_get(x_1344, 0);
lean_dec(x_1346);
lean_ctor_set(x_1344, 0, x_1336);
return x_1344;
}
else
{
lean_object* x_1347; lean_object* x_1348; 
x_1347 = lean_ctor_get(x_1344, 1);
lean_inc(x_1347);
lean_dec(x_1344);
x_1348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1348, 0, x_1336);
lean_ctor_set(x_1348, 1, x_1347);
return x_1348;
}
}
else
{
uint8_t x_1349; 
lean_dec(x_1339);
x_1349 = !lean_is_exclusive(x_1344);
if (x_1349 == 0)
{
lean_object* x_1350; lean_object* x_1351; uint8_t x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; 
x_1350 = lean_ctor_get(x_1344, 0);
x_1351 = lean_io_error_to_string(x_1350);
x_1352 = 3;
x_1353 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1353, 0, x_1351);
lean_ctor_set_uint8(x_1353, sizeof(void*)*1, x_1352);
x_1354 = lean_array_get_size(x_1340);
x_1355 = lean_array_push(x_1340, x_1353);
lean_ctor_set_tag(x_1336, 1);
lean_ctor_set(x_1336, 1, x_1355);
lean_ctor_set(x_1336, 0, x_1354);
lean_ctor_set_tag(x_1344, 0);
lean_ctor_set(x_1344, 0, x_1336);
return x_1344;
}
else
{
lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; uint8_t x_1359; lean_object* x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
x_1356 = lean_ctor_get(x_1344, 0);
x_1357 = lean_ctor_get(x_1344, 1);
lean_inc(x_1357);
lean_inc(x_1356);
lean_dec(x_1344);
x_1358 = lean_io_error_to_string(x_1356);
x_1359 = 3;
x_1360 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1360, 0, x_1358);
lean_ctor_set_uint8(x_1360, sizeof(void*)*1, x_1359);
x_1361 = lean_array_get_size(x_1340);
x_1362 = lean_array_push(x_1340, x_1360);
lean_ctor_set_tag(x_1336, 1);
lean_ctor_set(x_1336, 1, x_1362);
lean_ctor_set(x_1336, 0, x_1361);
x_1363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1363, 0, x_1336);
lean_ctor_set(x_1363, 1, x_1357);
return x_1363;
}
}
}
else
{
uint8_t x_1364; 
lean_dec(x_1339);
lean_dec(x_1324);
x_1364 = !lean_is_exclusive(x_1342);
if (x_1364 == 0)
{
lean_object* x_1365; lean_object* x_1366; uint8_t x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; 
x_1365 = lean_ctor_get(x_1342, 0);
x_1366 = lean_io_error_to_string(x_1365);
x_1367 = 3;
x_1368 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1368, 0, x_1366);
lean_ctor_set_uint8(x_1368, sizeof(void*)*1, x_1367);
x_1369 = lean_array_get_size(x_1340);
x_1370 = lean_array_push(x_1340, x_1368);
lean_ctor_set_tag(x_1336, 1);
lean_ctor_set(x_1336, 1, x_1370);
lean_ctor_set(x_1336, 0, x_1369);
lean_ctor_set_tag(x_1342, 0);
lean_ctor_set(x_1342, 0, x_1336);
return x_1342;
}
else
{
lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; uint8_t x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; lean_object* x_1378; 
x_1371 = lean_ctor_get(x_1342, 0);
x_1372 = lean_ctor_get(x_1342, 1);
lean_inc(x_1372);
lean_inc(x_1371);
lean_dec(x_1342);
x_1373 = lean_io_error_to_string(x_1371);
x_1374 = 3;
x_1375 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1375, 0, x_1373);
lean_ctor_set_uint8(x_1375, sizeof(void*)*1, x_1374);
x_1376 = lean_array_get_size(x_1340);
x_1377 = lean_array_push(x_1340, x_1375);
lean_ctor_set_tag(x_1336, 1);
lean_ctor_set(x_1336, 1, x_1377);
lean_ctor_set(x_1336, 0, x_1376);
x_1378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1378, 0, x_1336);
lean_ctor_set(x_1378, 1, x_1372);
return x_1378;
}
}
}
else
{
lean_object* x_1379; lean_object* x_1380; uint8_t x_1381; lean_object* x_1382; 
x_1379 = lean_ctor_get(x_1336, 0);
x_1380 = lean_ctor_get(x_1336, 1);
lean_inc(x_1380);
lean_inc(x_1379);
lean_dec(x_1336);
x_1381 = 0;
lean_inc(x_1379);
x_1382 = lean_write_module(x_1379, x_18, x_1381, x_1337);
if (lean_obj_tag(x_1382) == 0)
{
lean_object* x_1383; lean_object* x_1384; 
x_1383 = lean_ctor_get(x_1382, 1);
lean_inc(x_1383);
lean_dec(x_1382);
x_1384 = lean_io_prim_handle_unlock(x_1324, x_1383);
lean_dec(x_1324);
if (lean_obj_tag(x_1384) == 0)
{
lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; 
x_1385 = lean_ctor_get(x_1384, 1);
lean_inc(x_1385);
if (lean_is_exclusive(x_1384)) {
 lean_ctor_release(x_1384, 0);
 lean_ctor_release(x_1384, 1);
 x_1386 = x_1384;
} else {
 lean_dec_ref(x_1384);
 x_1386 = lean_box(0);
}
x_1387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1387, 0, x_1379);
lean_ctor_set(x_1387, 1, x_1380);
if (lean_is_scalar(x_1386)) {
 x_1388 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1388 = x_1386;
}
lean_ctor_set(x_1388, 0, x_1387);
lean_ctor_set(x_1388, 1, x_1385);
return x_1388;
}
else
{
lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; uint8_t x_1393; lean_object* x_1394; lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_1379);
x_1389 = lean_ctor_get(x_1384, 0);
lean_inc(x_1389);
x_1390 = lean_ctor_get(x_1384, 1);
lean_inc(x_1390);
if (lean_is_exclusive(x_1384)) {
 lean_ctor_release(x_1384, 0);
 lean_ctor_release(x_1384, 1);
 x_1391 = x_1384;
} else {
 lean_dec_ref(x_1384);
 x_1391 = lean_box(0);
}
x_1392 = lean_io_error_to_string(x_1389);
x_1393 = 3;
x_1394 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1394, 0, x_1392);
lean_ctor_set_uint8(x_1394, sizeof(void*)*1, x_1393);
x_1395 = lean_array_get_size(x_1380);
x_1396 = lean_array_push(x_1380, x_1394);
x_1397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1397, 0, x_1395);
lean_ctor_set(x_1397, 1, x_1396);
if (lean_is_scalar(x_1391)) {
 x_1398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1398 = x_1391;
 lean_ctor_set_tag(x_1398, 0);
}
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_1390);
return x_1398;
}
}
else
{
lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; uint8_t x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; 
lean_dec(x_1379);
lean_dec(x_1324);
x_1399 = lean_ctor_get(x_1382, 0);
lean_inc(x_1399);
x_1400 = lean_ctor_get(x_1382, 1);
lean_inc(x_1400);
if (lean_is_exclusive(x_1382)) {
 lean_ctor_release(x_1382, 0);
 lean_ctor_release(x_1382, 1);
 x_1401 = x_1382;
} else {
 lean_dec_ref(x_1382);
 x_1401 = lean_box(0);
}
x_1402 = lean_io_error_to_string(x_1399);
x_1403 = 3;
x_1404 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1404, 0, x_1402);
lean_ctor_set_uint8(x_1404, sizeof(void*)*1, x_1403);
x_1405 = lean_array_get_size(x_1380);
x_1406 = lean_array_push(x_1380, x_1404);
x_1407 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1407, 0, x_1405);
lean_ctor_set(x_1407, 1, x_1406);
if (lean_is_scalar(x_1401)) {
 x_1408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1408 = x_1401;
 lean_ctor_set_tag(x_1408, 0);
}
lean_ctor_set(x_1408, 0, x_1407);
lean_ctor_set(x_1408, 1, x_1400);
return x_1408;
}
}
}
else
{
uint8_t x_1409; 
lean_dec(x_1324);
lean_dec(x_18);
x_1409 = !lean_is_exclusive(x_1335);
if (x_1409 == 0)
{
lean_object* x_1410; uint8_t x_1411; 
x_1410 = lean_ctor_get(x_1335, 0);
lean_dec(x_1410);
x_1411 = !lean_is_exclusive(x_1336);
if (x_1411 == 0)
{
return x_1335;
}
else
{
lean_object* x_1412; lean_object* x_1413; lean_object* x_1414; 
x_1412 = lean_ctor_get(x_1336, 0);
x_1413 = lean_ctor_get(x_1336, 1);
lean_inc(x_1413);
lean_inc(x_1412);
lean_dec(x_1336);
x_1414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1414, 0, x_1412);
lean_ctor_set(x_1414, 1, x_1413);
lean_ctor_set(x_1335, 0, x_1414);
return x_1335;
}
}
else
{
lean_object* x_1415; lean_object* x_1416; lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; 
x_1415 = lean_ctor_get(x_1335, 1);
lean_inc(x_1415);
lean_dec(x_1335);
x_1416 = lean_ctor_get(x_1336, 0);
lean_inc(x_1416);
x_1417 = lean_ctor_get(x_1336, 1);
lean_inc(x_1417);
if (lean_is_exclusive(x_1336)) {
 lean_ctor_release(x_1336, 0);
 lean_ctor_release(x_1336, 1);
 x_1418 = x_1336;
} else {
 lean_dec_ref(x_1336);
 x_1418 = lean_box(0);
}
if (lean_is_scalar(x_1418)) {
 x_1419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1419 = x_1418;
}
lean_ctor_set(x_1419, 0, x_1416);
lean_ctor_set(x_1419, 1, x_1417);
x_1420 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1420, 0, x_1419);
lean_ctor_set(x_1420, 1, x_1415);
return x_1420;
}
}
}
else
{
uint8_t x_1421; 
lean_dec(x_1324);
lean_dec(x_18);
x_1421 = !lean_is_exclusive(x_1335);
if (x_1421 == 0)
{
return x_1335;
}
else
{
lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; 
x_1422 = lean_ctor_get(x_1335, 0);
x_1423 = lean_ctor_get(x_1335, 1);
lean_inc(x_1423);
lean_inc(x_1422);
lean_dec(x_1335);
x_1424 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1424, 0, x_1422);
lean_ctor_set(x_1424, 1, x_1423);
return x_1424;
}
}
}
else
{
uint8_t x_1425; 
lean_dec(x_1330);
lean_dec(x_1324);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1425 = !lean_is_exclusive(x_1331);
if (x_1425 == 0)
{
lean_object* x_1426; 
x_1426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1426, 0, x_1331);
lean_ctor_set(x_1426, 1, x_1332);
return x_1426;
}
else
{
lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; 
x_1427 = lean_ctor_get(x_1331, 0);
x_1428 = lean_ctor_get(x_1331, 1);
lean_inc(x_1428);
lean_inc(x_1427);
lean_dec(x_1331);
x_1429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1429, 0, x_1427);
lean_ctor_set(x_1429, 1, x_1428);
x_1430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1430, 0, x_1429);
lean_ctor_set(x_1430, 1, x_1332);
return x_1430;
}
}
}
block_1640:
{
lean_object* x_1434; 
x_1434 = lean_ctor_get(x_1432, 0);
lean_inc(x_1434);
if (lean_obj_tag(x_1434) == 0)
{
lean_object* x_1435; 
x_1435 = lean_ctor_get(x_1434, 0);
lean_inc(x_1435);
lean_dec(x_1434);
if (lean_obj_tag(x_1435) == 11)
{
uint8_t x_1436; 
lean_dec(x_1435);
lean_dec(x_21);
x_1436 = !lean_is_exclusive(x_1432);
if (x_1436 == 0)
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; lean_object* x_1446; 
x_1437 = lean_ctor_get(x_1432, 1);
x_1438 = lean_ctor_get(x_1432, 0);
lean_dec(x_1438);
x_1439 = lean_ctor_get(x_1, 0);
lean_inc(x_1439);
x_1440 = l_Lake_Env_leanGithash(x_1439);
lean_dec(x_1439);
x_1441 = l_System_Platform_target;
lean_inc(x_1330);
x_1442 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1442, 0, x_1441);
lean_ctor_set(x_1442, 1, x_1440);
lean_ctor_set(x_1442, 2, x_27);
lean_ctor_set(x_1442, 3, x_1330);
x_1443 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1442);
x_1444 = lean_unsigned_to_nat(80u);
x_1445 = l_Lean_Json_pretty(x_1443, x_1444);
x_1446 = l_IO_FS_Handle_putStrLn(x_1324, x_1445, x_1433);
if (lean_obj_tag(x_1446) == 0)
{
lean_object* x_1447; lean_object* x_1448; 
x_1447 = lean_ctor_get(x_1446, 1);
lean_inc(x_1447);
lean_dec(x_1446);
x_1448 = lean_io_prim_handle_truncate(x_1324, x_1447);
if (lean_obj_tag(x_1448) == 0)
{
lean_object* x_1449; lean_object* x_1450; 
x_1449 = lean_ctor_get(x_1448, 0);
lean_inc(x_1449);
x_1450 = lean_ctor_get(x_1448, 1);
lean_inc(x_1450);
lean_dec(x_1448);
lean_ctor_set(x_1432, 0, x_1449);
x_1331 = x_1432;
x_1332 = x_1450;
goto block_1431;
}
else
{
lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; uint8_t x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; 
x_1451 = lean_ctor_get(x_1448, 0);
lean_inc(x_1451);
x_1452 = lean_ctor_get(x_1448, 1);
lean_inc(x_1452);
lean_dec(x_1448);
x_1453 = lean_io_error_to_string(x_1451);
x_1454 = 3;
x_1455 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1455, 0, x_1453);
lean_ctor_set_uint8(x_1455, sizeof(void*)*1, x_1454);
x_1456 = lean_array_get_size(x_1437);
x_1457 = lean_array_push(x_1437, x_1455);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1457);
lean_ctor_set(x_1432, 0, x_1456);
x_1331 = x_1432;
x_1332 = x_1452;
goto block_1431;
}
}
else
{
uint8_t x_1458; 
lean_dec(x_1330);
lean_dec(x_1324);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1458 = !lean_is_exclusive(x_1446);
if (x_1458 == 0)
{
lean_object* x_1459; lean_object* x_1460; uint8_t x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; 
x_1459 = lean_ctor_get(x_1446, 0);
x_1460 = lean_io_error_to_string(x_1459);
x_1461 = 3;
x_1462 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1462, 0, x_1460);
lean_ctor_set_uint8(x_1462, sizeof(void*)*1, x_1461);
x_1463 = lean_array_get_size(x_1437);
x_1464 = lean_array_push(x_1437, x_1462);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1464);
lean_ctor_set(x_1432, 0, x_1463);
lean_ctor_set_tag(x_1446, 0);
lean_ctor_set(x_1446, 0, x_1432);
return x_1446;
}
else
{
lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; uint8_t x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; 
x_1465 = lean_ctor_get(x_1446, 0);
x_1466 = lean_ctor_get(x_1446, 1);
lean_inc(x_1466);
lean_inc(x_1465);
lean_dec(x_1446);
x_1467 = lean_io_error_to_string(x_1465);
x_1468 = 3;
x_1469 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1469, 0, x_1467);
lean_ctor_set_uint8(x_1469, sizeof(void*)*1, x_1468);
x_1470 = lean_array_get_size(x_1437);
x_1471 = lean_array_push(x_1437, x_1469);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1471);
lean_ctor_set(x_1432, 0, x_1470);
x_1472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1472, 0, x_1432);
lean_ctor_set(x_1472, 1, x_1466);
return x_1472;
}
}
}
else
{
lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; 
x_1473 = lean_ctor_get(x_1432, 1);
lean_inc(x_1473);
lean_dec(x_1432);
x_1474 = lean_ctor_get(x_1, 0);
lean_inc(x_1474);
x_1475 = l_Lake_Env_leanGithash(x_1474);
lean_dec(x_1474);
x_1476 = l_System_Platform_target;
lean_inc(x_1330);
x_1477 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1477, 0, x_1476);
lean_ctor_set(x_1477, 1, x_1475);
lean_ctor_set(x_1477, 2, x_27);
lean_ctor_set(x_1477, 3, x_1330);
x_1478 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1477);
x_1479 = lean_unsigned_to_nat(80u);
x_1480 = l_Lean_Json_pretty(x_1478, x_1479);
x_1481 = l_IO_FS_Handle_putStrLn(x_1324, x_1480, x_1433);
if (lean_obj_tag(x_1481) == 0)
{
lean_object* x_1482; lean_object* x_1483; 
x_1482 = lean_ctor_get(x_1481, 1);
lean_inc(x_1482);
lean_dec(x_1481);
x_1483 = lean_io_prim_handle_truncate(x_1324, x_1482);
if (lean_obj_tag(x_1483) == 0)
{
lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; 
x_1484 = lean_ctor_get(x_1483, 0);
lean_inc(x_1484);
x_1485 = lean_ctor_get(x_1483, 1);
lean_inc(x_1485);
lean_dec(x_1483);
x_1486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1486, 0, x_1484);
lean_ctor_set(x_1486, 1, x_1473);
x_1331 = x_1486;
x_1332 = x_1485;
goto block_1431;
}
else
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; uint8_t x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
x_1487 = lean_ctor_get(x_1483, 0);
lean_inc(x_1487);
x_1488 = lean_ctor_get(x_1483, 1);
lean_inc(x_1488);
lean_dec(x_1483);
x_1489 = lean_io_error_to_string(x_1487);
x_1490 = 3;
x_1491 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1491, 0, x_1489);
lean_ctor_set_uint8(x_1491, sizeof(void*)*1, x_1490);
x_1492 = lean_array_get_size(x_1473);
x_1493 = lean_array_push(x_1473, x_1491);
x_1494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1494, 0, x_1492);
lean_ctor_set(x_1494, 1, x_1493);
x_1331 = x_1494;
x_1332 = x_1488;
goto block_1431;
}
}
else
{
lean_object* x_1495; lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; uint8_t x_1499; lean_object* x_1500; lean_object* x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; 
lean_dec(x_1330);
lean_dec(x_1324);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1495 = lean_ctor_get(x_1481, 0);
lean_inc(x_1495);
x_1496 = lean_ctor_get(x_1481, 1);
lean_inc(x_1496);
if (lean_is_exclusive(x_1481)) {
 lean_ctor_release(x_1481, 0);
 lean_ctor_release(x_1481, 1);
 x_1497 = x_1481;
} else {
 lean_dec_ref(x_1481);
 x_1497 = lean_box(0);
}
x_1498 = lean_io_error_to_string(x_1495);
x_1499 = 3;
x_1500 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1500, 0, x_1498);
lean_ctor_set_uint8(x_1500, sizeof(void*)*1, x_1499);
x_1501 = lean_array_get_size(x_1473);
x_1502 = lean_array_push(x_1473, x_1500);
x_1503 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1503, 0, x_1501);
lean_ctor_set(x_1503, 1, x_1502);
if (lean_is_scalar(x_1497)) {
 x_1504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1504 = x_1497;
 lean_ctor_set_tag(x_1504, 0);
}
lean_ctor_set(x_1504, 0, x_1503);
lean_ctor_set(x_1504, 1, x_1496);
return x_1504;
}
}
}
else
{
uint8_t x_1505; 
lean_dec(x_1330);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1505 = !lean_is_exclusive(x_1432);
if (x_1505 == 0)
{
lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; uint8_t x_1509; lean_object* x_1510; lean_object* x_1511; lean_object* x_1512; lean_object* x_1513; 
x_1506 = lean_ctor_get(x_1432, 1);
x_1507 = lean_ctor_get(x_1432, 0);
lean_dec(x_1507);
x_1508 = lean_io_error_to_string(x_1435);
x_1509 = 3;
x_1510 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1510, 0, x_1508);
lean_ctor_set_uint8(x_1510, sizeof(void*)*1, x_1509);
x_1511 = lean_array_get_size(x_1506);
x_1512 = lean_array_push(x_1506, x_1510);
x_1513 = lean_io_prim_handle_unlock(x_1324, x_1433);
lean_dec(x_1324);
if (lean_obj_tag(x_1513) == 0)
{
lean_object* x_1514; lean_object* x_1515; 
x_1514 = lean_ctor_get(x_1513, 1);
lean_inc(x_1514);
lean_dec(x_1513);
x_1515 = lean_io_remove_file(x_21, x_1514);
lean_dec(x_21);
if (lean_obj_tag(x_1515) == 0)
{
uint8_t x_1516; 
x_1516 = !lean_is_exclusive(x_1515);
if (x_1516 == 0)
{
lean_object* x_1517; 
x_1517 = lean_ctor_get(x_1515, 0);
lean_dec(x_1517);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1512);
lean_ctor_set(x_1432, 0, x_1511);
lean_ctor_set(x_1515, 0, x_1432);
return x_1515;
}
else
{
lean_object* x_1518; lean_object* x_1519; 
x_1518 = lean_ctor_get(x_1515, 1);
lean_inc(x_1518);
lean_dec(x_1515);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1512);
lean_ctor_set(x_1432, 0, x_1511);
x_1519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1519, 0, x_1432);
lean_ctor_set(x_1519, 1, x_1518);
return x_1519;
}
}
else
{
uint8_t x_1520; 
x_1520 = !lean_is_exclusive(x_1515);
if (x_1520 == 0)
{
lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; 
x_1521 = lean_ctor_get(x_1515, 0);
x_1522 = lean_io_error_to_string(x_1521);
x_1523 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1523, 0, x_1522);
lean_ctor_set_uint8(x_1523, sizeof(void*)*1, x_1509);
x_1524 = lean_array_push(x_1512, x_1523);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1524);
lean_ctor_set(x_1432, 0, x_1511);
lean_ctor_set_tag(x_1515, 0);
lean_ctor_set(x_1515, 0, x_1432);
return x_1515;
}
else
{
lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; 
x_1525 = lean_ctor_get(x_1515, 0);
x_1526 = lean_ctor_get(x_1515, 1);
lean_inc(x_1526);
lean_inc(x_1525);
lean_dec(x_1515);
x_1527 = lean_io_error_to_string(x_1525);
x_1528 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1528, 0, x_1527);
lean_ctor_set_uint8(x_1528, sizeof(void*)*1, x_1509);
x_1529 = lean_array_push(x_1512, x_1528);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1529);
lean_ctor_set(x_1432, 0, x_1511);
x_1530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1530, 0, x_1432);
lean_ctor_set(x_1530, 1, x_1526);
return x_1530;
}
}
}
else
{
uint8_t x_1531; 
lean_dec(x_21);
x_1531 = !lean_is_exclusive(x_1513);
if (x_1531 == 0)
{
lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; 
x_1532 = lean_ctor_get(x_1513, 0);
x_1533 = lean_io_error_to_string(x_1532);
x_1534 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1534, 0, x_1533);
lean_ctor_set_uint8(x_1534, sizeof(void*)*1, x_1509);
x_1535 = lean_array_push(x_1512, x_1534);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1535);
lean_ctor_set(x_1432, 0, x_1511);
lean_ctor_set_tag(x_1513, 0);
lean_ctor_set(x_1513, 0, x_1432);
return x_1513;
}
else
{
lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; 
x_1536 = lean_ctor_get(x_1513, 0);
x_1537 = lean_ctor_get(x_1513, 1);
lean_inc(x_1537);
lean_inc(x_1536);
lean_dec(x_1513);
x_1538 = lean_io_error_to_string(x_1536);
x_1539 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1539, 0, x_1538);
lean_ctor_set_uint8(x_1539, sizeof(void*)*1, x_1509);
x_1540 = lean_array_push(x_1512, x_1539);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1540);
lean_ctor_set(x_1432, 0, x_1511);
x_1541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1541, 0, x_1432);
lean_ctor_set(x_1541, 1, x_1537);
return x_1541;
}
}
}
else
{
lean_object* x_1542; lean_object* x_1543; uint8_t x_1544; lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; lean_object* x_1548; 
x_1542 = lean_ctor_get(x_1432, 1);
lean_inc(x_1542);
lean_dec(x_1432);
x_1543 = lean_io_error_to_string(x_1435);
x_1544 = 3;
x_1545 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1545, 0, x_1543);
lean_ctor_set_uint8(x_1545, sizeof(void*)*1, x_1544);
x_1546 = lean_array_get_size(x_1542);
x_1547 = lean_array_push(x_1542, x_1545);
x_1548 = lean_io_prim_handle_unlock(x_1324, x_1433);
lean_dec(x_1324);
if (lean_obj_tag(x_1548) == 0)
{
lean_object* x_1549; lean_object* x_1550; 
x_1549 = lean_ctor_get(x_1548, 1);
lean_inc(x_1549);
lean_dec(x_1548);
x_1550 = lean_io_remove_file(x_21, x_1549);
lean_dec(x_21);
if (lean_obj_tag(x_1550) == 0)
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
x_1551 = lean_ctor_get(x_1550, 1);
lean_inc(x_1551);
if (lean_is_exclusive(x_1550)) {
 lean_ctor_release(x_1550, 0);
 lean_ctor_release(x_1550, 1);
 x_1552 = x_1550;
} else {
 lean_dec_ref(x_1550);
 x_1552 = lean_box(0);
}
x_1553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1553, 0, x_1546);
lean_ctor_set(x_1553, 1, x_1547);
if (lean_is_scalar(x_1552)) {
 x_1554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1554 = x_1552;
}
lean_ctor_set(x_1554, 0, x_1553);
lean_ctor_set(x_1554, 1, x_1551);
return x_1554;
}
else
{
lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; 
x_1555 = lean_ctor_get(x_1550, 0);
lean_inc(x_1555);
x_1556 = lean_ctor_get(x_1550, 1);
lean_inc(x_1556);
if (lean_is_exclusive(x_1550)) {
 lean_ctor_release(x_1550, 0);
 lean_ctor_release(x_1550, 1);
 x_1557 = x_1550;
} else {
 lean_dec_ref(x_1550);
 x_1557 = lean_box(0);
}
x_1558 = lean_io_error_to_string(x_1555);
x_1559 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1559, 0, x_1558);
lean_ctor_set_uint8(x_1559, sizeof(void*)*1, x_1544);
x_1560 = lean_array_push(x_1547, x_1559);
x_1561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1561, 0, x_1546);
lean_ctor_set(x_1561, 1, x_1560);
if (lean_is_scalar(x_1557)) {
 x_1562 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1562 = x_1557;
 lean_ctor_set_tag(x_1562, 0);
}
lean_ctor_set(x_1562, 0, x_1561);
lean_ctor_set(x_1562, 1, x_1556);
return x_1562;
}
}
else
{
lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; 
lean_dec(x_21);
x_1563 = lean_ctor_get(x_1548, 0);
lean_inc(x_1563);
x_1564 = lean_ctor_get(x_1548, 1);
lean_inc(x_1564);
if (lean_is_exclusive(x_1548)) {
 lean_ctor_release(x_1548, 0);
 lean_ctor_release(x_1548, 1);
 x_1565 = x_1548;
} else {
 lean_dec_ref(x_1548);
 x_1565 = lean_box(0);
}
x_1566 = lean_io_error_to_string(x_1563);
x_1567 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1567, 0, x_1566);
lean_ctor_set_uint8(x_1567, sizeof(void*)*1, x_1544);
x_1568 = lean_array_push(x_1547, x_1567);
x_1569 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1569, 0, x_1546);
lean_ctor_set(x_1569, 1, x_1568);
if (lean_is_scalar(x_1565)) {
 x_1570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1570 = x_1565;
 lean_ctor_set_tag(x_1570, 0);
}
lean_ctor_set(x_1570, 0, x_1569);
lean_ctor_set(x_1570, 1, x_1564);
return x_1570;
}
}
}
}
else
{
uint8_t x_1571; 
lean_dec(x_1434);
lean_dec(x_21);
x_1571 = !lean_is_exclusive(x_1432);
if (x_1571 == 0)
{
lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; lean_object* x_1581; 
x_1572 = lean_ctor_get(x_1432, 1);
x_1573 = lean_ctor_get(x_1432, 0);
lean_dec(x_1573);
x_1574 = lean_ctor_get(x_1, 0);
lean_inc(x_1574);
x_1575 = l_Lake_Env_leanGithash(x_1574);
lean_dec(x_1574);
x_1576 = l_System_Platform_target;
lean_inc(x_1330);
x_1577 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1577, 0, x_1576);
lean_ctor_set(x_1577, 1, x_1575);
lean_ctor_set(x_1577, 2, x_27);
lean_ctor_set(x_1577, 3, x_1330);
x_1578 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1577);
x_1579 = lean_unsigned_to_nat(80u);
x_1580 = l_Lean_Json_pretty(x_1578, x_1579);
x_1581 = l_IO_FS_Handle_putStrLn(x_1324, x_1580, x_1433);
if (lean_obj_tag(x_1581) == 0)
{
lean_object* x_1582; lean_object* x_1583; 
x_1582 = lean_ctor_get(x_1581, 1);
lean_inc(x_1582);
lean_dec(x_1581);
x_1583 = lean_io_prim_handle_truncate(x_1324, x_1582);
if (lean_obj_tag(x_1583) == 0)
{
lean_object* x_1584; lean_object* x_1585; 
x_1584 = lean_ctor_get(x_1583, 0);
lean_inc(x_1584);
x_1585 = lean_ctor_get(x_1583, 1);
lean_inc(x_1585);
lean_dec(x_1583);
lean_ctor_set(x_1432, 0, x_1584);
x_1331 = x_1432;
x_1332 = x_1585;
goto block_1431;
}
else
{
lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; uint8_t x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; 
x_1586 = lean_ctor_get(x_1583, 0);
lean_inc(x_1586);
x_1587 = lean_ctor_get(x_1583, 1);
lean_inc(x_1587);
lean_dec(x_1583);
x_1588 = lean_io_error_to_string(x_1586);
x_1589 = 3;
x_1590 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1590, 0, x_1588);
lean_ctor_set_uint8(x_1590, sizeof(void*)*1, x_1589);
x_1591 = lean_array_get_size(x_1572);
x_1592 = lean_array_push(x_1572, x_1590);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1592);
lean_ctor_set(x_1432, 0, x_1591);
x_1331 = x_1432;
x_1332 = x_1587;
goto block_1431;
}
}
else
{
uint8_t x_1593; 
lean_dec(x_1330);
lean_dec(x_1324);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1593 = !lean_is_exclusive(x_1581);
if (x_1593 == 0)
{
lean_object* x_1594; lean_object* x_1595; uint8_t x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
x_1594 = lean_ctor_get(x_1581, 0);
x_1595 = lean_io_error_to_string(x_1594);
x_1596 = 3;
x_1597 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1597, 0, x_1595);
lean_ctor_set_uint8(x_1597, sizeof(void*)*1, x_1596);
x_1598 = lean_array_get_size(x_1572);
x_1599 = lean_array_push(x_1572, x_1597);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1599);
lean_ctor_set(x_1432, 0, x_1598);
lean_ctor_set_tag(x_1581, 0);
lean_ctor_set(x_1581, 0, x_1432);
return x_1581;
}
else
{
lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; uint8_t x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; 
x_1600 = lean_ctor_get(x_1581, 0);
x_1601 = lean_ctor_get(x_1581, 1);
lean_inc(x_1601);
lean_inc(x_1600);
lean_dec(x_1581);
x_1602 = lean_io_error_to_string(x_1600);
x_1603 = 3;
x_1604 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1604, 0, x_1602);
lean_ctor_set_uint8(x_1604, sizeof(void*)*1, x_1603);
x_1605 = lean_array_get_size(x_1572);
x_1606 = lean_array_push(x_1572, x_1604);
lean_ctor_set_tag(x_1432, 1);
lean_ctor_set(x_1432, 1, x_1606);
lean_ctor_set(x_1432, 0, x_1605);
x_1607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1607, 0, x_1432);
lean_ctor_set(x_1607, 1, x_1601);
return x_1607;
}
}
}
else
{
lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; 
x_1608 = lean_ctor_get(x_1432, 1);
lean_inc(x_1608);
lean_dec(x_1432);
x_1609 = lean_ctor_get(x_1, 0);
lean_inc(x_1609);
x_1610 = l_Lake_Env_leanGithash(x_1609);
lean_dec(x_1609);
x_1611 = l_System_Platform_target;
lean_inc(x_1330);
x_1612 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1612, 0, x_1611);
lean_ctor_set(x_1612, 1, x_1610);
lean_ctor_set(x_1612, 2, x_27);
lean_ctor_set(x_1612, 3, x_1330);
x_1613 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1612);
x_1614 = lean_unsigned_to_nat(80u);
x_1615 = l_Lean_Json_pretty(x_1613, x_1614);
x_1616 = l_IO_FS_Handle_putStrLn(x_1324, x_1615, x_1433);
if (lean_obj_tag(x_1616) == 0)
{
lean_object* x_1617; lean_object* x_1618; 
x_1617 = lean_ctor_get(x_1616, 1);
lean_inc(x_1617);
lean_dec(x_1616);
x_1618 = lean_io_prim_handle_truncate(x_1324, x_1617);
if (lean_obj_tag(x_1618) == 0)
{
lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
x_1619 = lean_ctor_get(x_1618, 0);
lean_inc(x_1619);
x_1620 = lean_ctor_get(x_1618, 1);
lean_inc(x_1620);
lean_dec(x_1618);
x_1621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1621, 0, x_1619);
lean_ctor_set(x_1621, 1, x_1608);
x_1331 = x_1621;
x_1332 = x_1620;
goto block_1431;
}
else
{
lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; uint8_t x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; 
x_1622 = lean_ctor_get(x_1618, 0);
lean_inc(x_1622);
x_1623 = lean_ctor_get(x_1618, 1);
lean_inc(x_1623);
lean_dec(x_1618);
x_1624 = lean_io_error_to_string(x_1622);
x_1625 = 3;
x_1626 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1626, 0, x_1624);
lean_ctor_set_uint8(x_1626, sizeof(void*)*1, x_1625);
x_1627 = lean_array_get_size(x_1608);
x_1628 = lean_array_push(x_1608, x_1626);
x_1629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1629, 0, x_1627);
lean_ctor_set(x_1629, 1, x_1628);
x_1331 = x_1629;
x_1332 = x_1623;
goto block_1431;
}
}
else
{
lean_object* x_1630; lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; uint8_t x_1634; lean_object* x_1635; lean_object* x_1636; lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; 
lean_dec(x_1330);
lean_dec(x_1324);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1630 = lean_ctor_get(x_1616, 0);
lean_inc(x_1630);
x_1631 = lean_ctor_get(x_1616, 1);
lean_inc(x_1631);
if (lean_is_exclusive(x_1616)) {
 lean_ctor_release(x_1616, 0);
 lean_ctor_release(x_1616, 1);
 x_1632 = x_1616;
} else {
 lean_dec_ref(x_1616);
 x_1632 = lean_box(0);
}
x_1633 = lean_io_error_to_string(x_1630);
x_1634 = 3;
x_1635 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1635, 0, x_1633);
lean_ctor_set_uint8(x_1635, sizeof(void*)*1, x_1634);
x_1636 = lean_array_get_size(x_1608);
x_1637 = lean_array_push(x_1608, x_1635);
x_1638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1638, 0, x_1636);
lean_ctor_set(x_1638, 1, x_1637);
if (lean_is_scalar(x_1632)) {
 x_1639 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1639 = x_1632;
 lean_ctor_set_tag(x_1639, 0);
}
lean_ctor_set(x_1639, 0, x_1638);
lean_ctor_set(x_1639, 1, x_1631);
return x_1639;
}
}
}
}
}
else
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1705; lean_object* x_1706; lean_object* x_1806; 
x_1648 = lean_ctor_get(x_1326, 1);
lean_inc(x_1648);
lean_dec(x_1326);
x_1649 = lean_ctor_get(x_1, 8);
lean_inc(x_1649);
x_1806 = lean_io_remove_file(x_18, x_1327);
if (lean_obj_tag(x_1806) == 0)
{
lean_object* x_1807; lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; 
x_1807 = lean_ctor_get(x_1806, 0);
lean_inc(x_1807);
x_1808 = lean_ctor_get(x_1806, 1);
lean_inc(x_1808);
lean_dec(x_1806);
if (lean_is_scalar(x_1325)) {
 x_1809 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1809 = x_1325;
}
lean_ctor_set(x_1809, 0, x_1807);
x_1810 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1810, 0, x_1809);
lean_ctor_set(x_1810, 1, x_1648);
x_1705 = x_1810;
x_1706 = x_1808;
goto block_1805;
}
else
{
lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; 
x_1811 = lean_ctor_get(x_1806, 0);
lean_inc(x_1811);
x_1812 = lean_ctor_get(x_1806, 1);
lean_inc(x_1812);
lean_dec(x_1806);
if (lean_is_scalar(x_1325)) {
 x_1813 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1813 = x_1325;
 lean_ctor_set_tag(x_1813, 0);
}
lean_ctor_set(x_1813, 0, x_1811);
x_1814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1814, 0, x_1813);
lean_ctor_set(x_1814, 1, x_1648);
x_1705 = x_1814;
x_1706 = x_1812;
goto block_1805;
}
block_1704:
{
if (lean_obj_tag(x_1650) == 0)
{
lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; 
x_1652 = lean_ctor_get(x_1650, 1);
lean_inc(x_1652);
lean_dec(x_1650);
x_1653 = lean_ctor_get(x_1, 9);
lean_inc(x_1653);
lean_dec(x_1);
x_1654 = l_Lake_elabConfigFile(x_13, x_1649, x_1653, x_4, x_1652, x_1651);
if (lean_obj_tag(x_1654) == 0)
{
lean_object* x_1655; 
x_1655 = lean_ctor_get(x_1654, 0);
lean_inc(x_1655);
if (lean_obj_tag(x_1655) == 0)
{
lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; uint8_t x_1660; lean_object* x_1661; 
x_1656 = lean_ctor_get(x_1654, 1);
lean_inc(x_1656);
lean_dec(x_1654);
x_1657 = lean_ctor_get(x_1655, 0);
lean_inc(x_1657);
x_1658 = lean_ctor_get(x_1655, 1);
lean_inc(x_1658);
if (lean_is_exclusive(x_1655)) {
 lean_ctor_release(x_1655, 0);
 lean_ctor_release(x_1655, 1);
 x_1659 = x_1655;
} else {
 lean_dec_ref(x_1655);
 x_1659 = lean_box(0);
}
x_1660 = 0;
lean_inc(x_1657);
x_1661 = lean_write_module(x_1657, x_18, x_1660, x_1656);
if (lean_obj_tag(x_1661) == 0)
{
lean_object* x_1662; lean_object* x_1663; 
x_1662 = lean_ctor_get(x_1661, 1);
lean_inc(x_1662);
lean_dec(x_1661);
x_1663 = lean_io_prim_handle_unlock(x_1324, x_1662);
lean_dec(x_1324);
if (lean_obj_tag(x_1663) == 0)
{
lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; 
x_1664 = lean_ctor_get(x_1663, 1);
lean_inc(x_1664);
if (lean_is_exclusive(x_1663)) {
 lean_ctor_release(x_1663, 0);
 lean_ctor_release(x_1663, 1);
 x_1665 = x_1663;
} else {
 lean_dec_ref(x_1663);
 x_1665 = lean_box(0);
}
if (lean_is_scalar(x_1659)) {
 x_1666 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1666 = x_1659;
}
lean_ctor_set(x_1666, 0, x_1657);
lean_ctor_set(x_1666, 1, x_1658);
if (lean_is_scalar(x_1665)) {
 x_1667 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1667 = x_1665;
}
lean_ctor_set(x_1667, 0, x_1666);
lean_ctor_set(x_1667, 1, x_1664);
return x_1667;
}
else
{
lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; uint8_t x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; 
lean_dec(x_1657);
x_1668 = lean_ctor_get(x_1663, 0);
lean_inc(x_1668);
x_1669 = lean_ctor_get(x_1663, 1);
lean_inc(x_1669);
if (lean_is_exclusive(x_1663)) {
 lean_ctor_release(x_1663, 0);
 lean_ctor_release(x_1663, 1);
 x_1670 = x_1663;
} else {
 lean_dec_ref(x_1663);
 x_1670 = lean_box(0);
}
x_1671 = lean_io_error_to_string(x_1668);
x_1672 = 3;
x_1673 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1673, 0, x_1671);
lean_ctor_set_uint8(x_1673, sizeof(void*)*1, x_1672);
x_1674 = lean_array_get_size(x_1658);
x_1675 = lean_array_push(x_1658, x_1673);
if (lean_is_scalar(x_1659)) {
 x_1676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1676 = x_1659;
 lean_ctor_set_tag(x_1676, 1);
}
lean_ctor_set(x_1676, 0, x_1674);
lean_ctor_set(x_1676, 1, x_1675);
if (lean_is_scalar(x_1670)) {
 x_1677 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1677 = x_1670;
 lean_ctor_set_tag(x_1677, 0);
}
lean_ctor_set(x_1677, 0, x_1676);
lean_ctor_set(x_1677, 1, x_1669);
return x_1677;
}
}
else
{
lean_object* x_1678; lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; uint8_t x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; 
lean_dec(x_1657);
lean_dec(x_1324);
x_1678 = lean_ctor_get(x_1661, 0);
lean_inc(x_1678);
x_1679 = lean_ctor_get(x_1661, 1);
lean_inc(x_1679);
if (lean_is_exclusive(x_1661)) {
 lean_ctor_release(x_1661, 0);
 lean_ctor_release(x_1661, 1);
 x_1680 = x_1661;
} else {
 lean_dec_ref(x_1661);
 x_1680 = lean_box(0);
}
x_1681 = lean_io_error_to_string(x_1678);
x_1682 = 3;
x_1683 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1683, 0, x_1681);
lean_ctor_set_uint8(x_1683, sizeof(void*)*1, x_1682);
x_1684 = lean_array_get_size(x_1658);
x_1685 = lean_array_push(x_1658, x_1683);
if (lean_is_scalar(x_1659)) {
 x_1686 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1686 = x_1659;
 lean_ctor_set_tag(x_1686, 1);
}
lean_ctor_set(x_1686, 0, x_1684);
lean_ctor_set(x_1686, 1, x_1685);
if (lean_is_scalar(x_1680)) {
 x_1687 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1687 = x_1680;
 lean_ctor_set_tag(x_1687, 0);
}
lean_ctor_set(x_1687, 0, x_1686);
lean_ctor_set(x_1687, 1, x_1679);
return x_1687;
}
}
else
{
lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; 
lean_dec(x_1324);
lean_dec(x_18);
x_1688 = lean_ctor_get(x_1654, 1);
lean_inc(x_1688);
if (lean_is_exclusive(x_1654)) {
 lean_ctor_release(x_1654, 0);
 lean_ctor_release(x_1654, 1);
 x_1689 = x_1654;
} else {
 lean_dec_ref(x_1654);
 x_1689 = lean_box(0);
}
x_1690 = lean_ctor_get(x_1655, 0);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1655, 1);
lean_inc(x_1691);
if (lean_is_exclusive(x_1655)) {
 lean_ctor_release(x_1655, 0);
 lean_ctor_release(x_1655, 1);
 x_1692 = x_1655;
} else {
 lean_dec_ref(x_1655);
 x_1692 = lean_box(0);
}
if (lean_is_scalar(x_1692)) {
 x_1693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1693 = x_1692;
}
lean_ctor_set(x_1693, 0, x_1690);
lean_ctor_set(x_1693, 1, x_1691);
if (lean_is_scalar(x_1689)) {
 x_1694 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1694 = x_1689;
}
lean_ctor_set(x_1694, 0, x_1693);
lean_ctor_set(x_1694, 1, x_1688);
return x_1694;
}
}
else
{
lean_object* x_1695; lean_object* x_1696; lean_object* x_1697; lean_object* x_1698; 
lean_dec(x_1324);
lean_dec(x_18);
x_1695 = lean_ctor_get(x_1654, 0);
lean_inc(x_1695);
x_1696 = lean_ctor_get(x_1654, 1);
lean_inc(x_1696);
if (lean_is_exclusive(x_1654)) {
 lean_ctor_release(x_1654, 0);
 lean_ctor_release(x_1654, 1);
 x_1697 = x_1654;
} else {
 lean_dec_ref(x_1654);
 x_1697 = lean_box(0);
}
if (lean_is_scalar(x_1697)) {
 x_1698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1698 = x_1697;
}
lean_ctor_set(x_1698, 0, x_1695);
lean_ctor_set(x_1698, 1, x_1696);
return x_1698;
}
}
else
{
lean_object* x_1699; lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; 
lean_dec(x_1649);
lean_dec(x_1324);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1699 = lean_ctor_get(x_1650, 0);
lean_inc(x_1699);
x_1700 = lean_ctor_get(x_1650, 1);
lean_inc(x_1700);
if (lean_is_exclusive(x_1650)) {
 lean_ctor_release(x_1650, 0);
 lean_ctor_release(x_1650, 1);
 x_1701 = x_1650;
} else {
 lean_dec_ref(x_1650);
 x_1701 = lean_box(0);
}
if (lean_is_scalar(x_1701)) {
 x_1702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1702 = x_1701;
}
lean_ctor_set(x_1702, 0, x_1699);
lean_ctor_set(x_1702, 1, x_1700);
x_1703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1703, 0, x_1702);
lean_ctor_set(x_1703, 1, x_1651);
return x_1703;
}
}
block_1805:
{
lean_object* x_1707; 
x_1707 = lean_ctor_get(x_1705, 0);
lean_inc(x_1707);
if (lean_obj_tag(x_1707) == 0)
{
lean_object* x_1708; 
x_1708 = lean_ctor_get(x_1707, 0);
lean_inc(x_1708);
lean_dec(x_1707);
if (lean_obj_tag(x_1708) == 11)
{
lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; lean_object* x_1718; 
lean_dec(x_1708);
lean_dec(x_21);
x_1709 = lean_ctor_get(x_1705, 1);
lean_inc(x_1709);
if (lean_is_exclusive(x_1705)) {
 lean_ctor_release(x_1705, 0);
 lean_ctor_release(x_1705, 1);
 x_1710 = x_1705;
} else {
 lean_dec_ref(x_1705);
 x_1710 = lean_box(0);
}
x_1711 = lean_ctor_get(x_1, 0);
lean_inc(x_1711);
x_1712 = l_Lake_Env_leanGithash(x_1711);
lean_dec(x_1711);
x_1713 = l_System_Platform_target;
lean_inc(x_1649);
x_1714 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1714, 0, x_1713);
lean_ctor_set(x_1714, 1, x_1712);
lean_ctor_set(x_1714, 2, x_27);
lean_ctor_set(x_1714, 3, x_1649);
x_1715 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1714);
x_1716 = lean_unsigned_to_nat(80u);
x_1717 = l_Lean_Json_pretty(x_1715, x_1716);
x_1718 = l_IO_FS_Handle_putStrLn(x_1324, x_1717, x_1706);
if (lean_obj_tag(x_1718) == 0)
{
lean_object* x_1719; lean_object* x_1720; 
x_1719 = lean_ctor_get(x_1718, 1);
lean_inc(x_1719);
lean_dec(x_1718);
x_1720 = lean_io_prim_handle_truncate(x_1324, x_1719);
if (lean_obj_tag(x_1720) == 0)
{
lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; 
x_1721 = lean_ctor_get(x_1720, 0);
lean_inc(x_1721);
x_1722 = lean_ctor_get(x_1720, 1);
lean_inc(x_1722);
lean_dec(x_1720);
if (lean_is_scalar(x_1710)) {
 x_1723 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1723 = x_1710;
}
lean_ctor_set(x_1723, 0, x_1721);
lean_ctor_set(x_1723, 1, x_1709);
x_1650 = x_1723;
x_1651 = x_1722;
goto block_1704;
}
else
{
lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; uint8_t x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; 
x_1724 = lean_ctor_get(x_1720, 0);
lean_inc(x_1724);
x_1725 = lean_ctor_get(x_1720, 1);
lean_inc(x_1725);
lean_dec(x_1720);
x_1726 = lean_io_error_to_string(x_1724);
x_1727 = 3;
x_1728 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1728, 0, x_1726);
lean_ctor_set_uint8(x_1728, sizeof(void*)*1, x_1727);
x_1729 = lean_array_get_size(x_1709);
x_1730 = lean_array_push(x_1709, x_1728);
if (lean_is_scalar(x_1710)) {
 x_1731 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1731 = x_1710;
 lean_ctor_set_tag(x_1731, 1);
}
lean_ctor_set(x_1731, 0, x_1729);
lean_ctor_set(x_1731, 1, x_1730);
x_1650 = x_1731;
x_1651 = x_1725;
goto block_1704;
}
}
else
{
lean_object* x_1732; lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; uint8_t x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; 
lean_dec(x_1649);
lean_dec(x_1324);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1732 = lean_ctor_get(x_1718, 0);
lean_inc(x_1732);
x_1733 = lean_ctor_get(x_1718, 1);
lean_inc(x_1733);
if (lean_is_exclusive(x_1718)) {
 lean_ctor_release(x_1718, 0);
 lean_ctor_release(x_1718, 1);
 x_1734 = x_1718;
} else {
 lean_dec_ref(x_1718);
 x_1734 = lean_box(0);
}
x_1735 = lean_io_error_to_string(x_1732);
x_1736 = 3;
x_1737 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1737, 0, x_1735);
lean_ctor_set_uint8(x_1737, sizeof(void*)*1, x_1736);
x_1738 = lean_array_get_size(x_1709);
x_1739 = lean_array_push(x_1709, x_1737);
if (lean_is_scalar(x_1710)) {
 x_1740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1740 = x_1710;
 lean_ctor_set_tag(x_1740, 1);
}
lean_ctor_set(x_1740, 0, x_1738);
lean_ctor_set(x_1740, 1, x_1739);
if (lean_is_scalar(x_1734)) {
 x_1741 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1741 = x_1734;
 lean_ctor_set_tag(x_1741, 0);
}
lean_ctor_set(x_1741, 0, x_1740);
lean_ctor_set(x_1741, 1, x_1733);
return x_1741;
}
}
else
{
lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; uint8_t x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; 
lean_dec(x_1649);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1742 = lean_ctor_get(x_1705, 1);
lean_inc(x_1742);
if (lean_is_exclusive(x_1705)) {
 lean_ctor_release(x_1705, 0);
 lean_ctor_release(x_1705, 1);
 x_1743 = x_1705;
} else {
 lean_dec_ref(x_1705);
 x_1743 = lean_box(0);
}
x_1744 = lean_io_error_to_string(x_1708);
x_1745 = 3;
x_1746 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1746, 0, x_1744);
lean_ctor_set_uint8(x_1746, sizeof(void*)*1, x_1745);
x_1747 = lean_array_get_size(x_1742);
x_1748 = lean_array_push(x_1742, x_1746);
x_1749 = lean_io_prim_handle_unlock(x_1324, x_1706);
lean_dec(x_1324);
if (lean_obj_tag(x_1749) == 0)
{
lean_object* x_1750; lean_object* x_1751; 
x_1750 = lean_ctor_get(x_1749, 1);
lean_inc(x_1750);
lean_dec(x_1749);
x_1751 = lean_io_remove_file(x_21, x_1750);
lean_dec(x_21);
if (lean_obj_tag(x_1751) == 0)
{
lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; 
x_1752 = lean_ctor_get(x_1751, 1);
lean_inc(x_1752);
if (lean_is_exclusive(x_1751)) {
 lean_ctor_release(x_1751, 0);
 lean_ctor_release(x_1751, 1);
 x_1753 = x_1751;
} else {
 lean_dec_ref(x_1751);
 x_1753 = lean_box(0);
}
if (lean_is_scalar(x_1743)) {
 x_1754 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1754 = x_1743;
 lean_ctor_set_tag(x_1754, 1);
}
lean_ctor_set(x_1754, 0, x_1747);
lean_ctor_set(x_1754, 1, x_1748);
if (lean_is_scalar(x_1753)) {
 x_1755 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1755 = x_1753;
}
lean_ctor_set(x_1755, 0, x_1754);
lean_ctor_set(x_1755, 1, x_1752);
return x_1755;
}
else
{
lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; 
x_1756 = lean_ctor_get(x_1751, 0);
lean_inc(x_1756);
x_1757 = lean_ctor_get(x_1751, 1);
lean_inc(x_1757);
if (lean_is_exclusive(x_1751)) {
 lean_ctor_release(x_1751, 0);
 lean_ctor_release(x_1751, 1);
 x_1758 = x_1751;
} else {
 lean_dec_ref(x_1751);
 x_1758 = lean_box(0);
}
x_1759 = lean_io_error_to_string(x_1756);
x_1760 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1760, 0, x_1759);
lean_ctor_set_uint8(x_1760, sizeof(void*)*1, x_1745);
x_1761 = lean_array_push(x_1748, x_1760);
if (lean_is_scalar(x_1743)) {
 x_1762 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1762 = x_1743;
 lean_ctor_set_tag(x_1762, 1);
}
lean_ctor_set(x_1762, 0, x_1747);
lean_ctor_set(x_1762, 1, x_1761);
if (lean_is_scalar(x_1758)) {
 x_1763 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1763 = x_1758;
 lean_ctor_set_tag(x_1763, 0);
}
lean_ctor_set(x_1763, 0, x_1762);
lean_ctor_set(x_1763, 1, x_1757);
return x_1763;
}
}
else
{
lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; 
lean_dec(x_21);
x_1764 = lean_ctor_get(x_1749, 0);
lean_inc(x_1764);
x_1765 = lean_ctor_get(x_1749, 1);
lean_inc(x_1765);
if (lean_is_exclusive(x_1749)) {
 lean_ctor_release(x_1749, 0);
 lean_ctor_release(x_1749, 1);
 x_1766 = x_1749;
} else {
 lean_dec_ref(x_1749);
 x_1766 = lean_box(0);
}
x_1767 = lean_io_error_to_string(x_1764);
x_1768 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1768, 0, x_1767);
lean_ctor_set_uint8(x_1768, sizeof(void*)*1, x_1745);
x_1769 = lean_array_push(x_1748, x_1768);
if (lean_is_scalar(x_1743)) {
 x_1770 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1770 = x_1743;
 lean_ctor_set_tag(x_1770, 1);
}
lean_ctor_set(x_1770, 0, x_1747);
lean_ctor_set(x_1770, 1, x_1769);
if (lean_is_scalar(x_1766)) {
 x_1771 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1771 = x_1766;
 lean_ctor_set_tag(x_1771, 0);
}
lean_ctor_set(x_1771, 0, x_1770);
lean_ctor_set(x_1771, 1, x_1765);
return x_1771;
}
}
}
else
{
lean_object* x_1772; lean_object* x_1773; lean_object* x_1774; lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; lean_object* x_1781; 
lean_dec(x_1707);
lean_dec(x_21);
x_1772 = lean_ctor_get(x_1705, 1);
lean_inc(x_1772);
if (lean_is_exclusive(x_1705)) {
 lean_ctor_release(x_1705, 0);
 lean_ctor_release(x_1705, 1);
 x_1773 = x_1705;
} else {
 lean_dec_ref(x_1705);
 x_1773 = lean_box(0);
}
x_1774 = lean_ctor_get(x_1, 0);
lean_inc(x_1774);
x_1775 = l_Lake_Env_leanGithash(x_1774);
lean_dec(x_1774);
x_1776 = l_System_Platform_target;
lean_inc(x_1649);
x_1777 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1777, 0, x_1776);
lean_ctor_set(x_1777, 1, x_1775);
lean_ctor_set(x_1777, 2, x_27);
lean_ctor_set(x_1777, 3, x_1649);
x_1778 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1777);
x_1779 = lean_unsigned_to_nat(80u);
x_1780 = l_Lean_Json_pretty(x_1778, x_1779);
x_1781 = l_IO_FS_Handle_putStrLn(x_1324, x_1780, x_1706);
if (lean_obj_tag(x_1781) == 0)
{
lean_object* x_1782; lean_object* x_1783; 
x_1782 = lean_ctor_get(x_1781, 1);
lean_inc(x_1782);
lean_dec(x_1781);
x_1783 = lean_io_prim_handle_truncate(x_1324, x_1782);
if (lean_obj_tag(x_1783) == 0)
{
lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; 
x_1784 = lean_ctor_get(x_1783, 0);
lean_inc(x_1784);
x_1785 = lean_ctor_get(x_1783, 1);
lean_inc(x_1785);
lean_dec(x_1783);
if (lean_is_scalar(x_1773)) {
 x_1786 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1786 = x_1773;
}
lean_ctor_set(x_1786, 0, x_1784);
lean_ctor_set(x_1786, 1, x_1772);
x_1650 = x_1786;
x_1651 = x_1785;
goto block_1704;
}
else
{
lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; uint8_t x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; 
x_1787 = lean_ctor_get(x_1783, 0);
lean_inc(x_1787);
x_1788 = lean_ctor_get(x_1783, 1);
lean_inc(x_1788);
lean_dec(x_1783);
x_1789 = lean_io_error_to_string(x_1787);
x_1790 = 3;
x_1791 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1791, 0, x_1789);
lean_ctor_set_uint8(x_1791, sizeof(void*)*1, x_1790);
x_1792 = lean_array_get_size(x_1772);
x_1793 = lean_array_push(x_1772, x_1791);
if (lean_is_scalar(x_1773)) {
 x_1794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1794 = x_1773;
 lean_ctor_set_tag(x_1794, 1);
}
lean_ctor_set(x_1794, 0, x_1792);
lean_ctor_set(x_1794, 1, x_1793);
x_1650 = x_1794;
x_1651 = x_1788;
goto block_1704;
}
}
else
{
lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; uint8_t x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; 
lean_dec(x_1649);
lean_dec(x_1324);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1795 = lean_ctor_get(x_1781, 0);
lean_inc(x_1795);
x_1796 = lean_ctor_get(x_1781, 1);
lean_inc(x_1796);
if (lean_is_exclusive(x_1781)) {
 lean_ctor_release(x_1781, 0);
 lean_ctor_release(x_1781, 1);
 x_1797 = x_1781;
} else {
 lean_dec_ref(x_1781);
 x_1797 = lean_box(0);
}
x_1798 = lean_io_error_to_string(x_1795);
x_1799 = 3;
x_1800 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1800, 0, x_1798);
lean_ctor_set_uint8(x_1800, sizeof(void*)*1, x_1799);
x_1801 = lean_array_get_size(x_1772);
x_1802 = lean_array_push(x_1772, x_1800);
if (lean_is_scalar(x_1773)) {
 x_1803 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1803 = x_1773;
 lean_ctor_set_tag(x_1803, 1);
}
lean_ctor_set(x_1803, 0, x_1801);
lean_ctor_set(x_1803, 1, x_1802);
if (lean_is_scalar(x_1797)) {
 x_1804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1804 = x_1797;
 lean_ctor_set_tag(x_1804, 0);
}
lean_ctor_set(x_1804, 0, x_1803);
lean_ctor_set(x_1804, 1, x_1796);
return x_1804;
}
}
}
}
}
else
{
uint8_t x_1815; 
lean_dec(x_1325);
lean_dec(x_1324);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1815 = !lean_is_exclusive(x_1326);
if (x_1815 == 0)
{
lean_object* x_1816; 
x_1816 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1816, 0, x_1326);
lean_ctor_set(x_1816, 1, x_1327);
return x_1816;
}
else
{
lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; 
x_1817 = lean_ctor_get(x_1326, 0);
x_1818 = lean_ctor_get(x_1326, 1);
lean_inc(x_1818);
lean_inc(x_1817);
lean_dec(x_1326);
x_1819 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1819, 0, x_1817);
lean_ctor_set(x_1819, 1, x_1818);
x_1820 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1820, 0, x_1819);
lean_ctor_set(x_1820, 1, x_1327);
return x_1820;
}
}
}
}
else
{
lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; uint8_t x_2012; lean_object* x_2013; 
x_1833 = lean_ctor_get(x_1272, 1);
lean_inc(x_1833);
lean_dec(x_1272);
x_1834 = lean_ctor_get(x_1274, 0);
lean_inc(x_1834);
if (lean_is_exclusive(x_1274)) {
 lean_ctor_release(x_1274, 0);
 x_1835 = x_1274;
} else {
 lean_dec_ref(x_1274);
 x_1835 = lean_box(0);
}
x_2012 = 1;
x_2013 = lean_io_prim_handle_lock(x_1834, x_2012, x_1273);
if (lean_obj_tag(x_2013) == 0)
{
lean_object* x_2014; lean_object* x_2015; lean_object* x_2016; 
x_2014 = lean_ctor_get(x_2013, 0);
lean_inc(x_2014);
x_2015 = lean_ctor_get(x_2013, 1);
lean_inc(x_2015);
lean_dec(x_2013);
x_2016 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2016, 0, x_2014);
lean_ctor_set(x_2016, 1, x_1833);
x_1836 = x_2016;
x_1837 = x_2015;
goto block_2011;
}
else
{
lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; uint8_t x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; 
x_2017 = lean_ctor_get(x_2013, 0);
lean_inc(x_2017);
x_2018 = lean_ctor_get(x_2013, 1);
lean_inc(x_2018);
lean_dec(x_2013);
x_2019 = lean_io_error_to_string(x_2017);
x_2020 = 3;
x_2021 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2021, 0, x_2019);
lean_ctor_set_uint8(x_2021, sizeof(void*)*1, x_2020);
x_2022 = lean_array_get_size(x_1833);
x_2023 = lean_array_push(x_1833, x_2021);
x_2024 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2024, 0, x_2022);
lean_ctor_set(x_2024, 1, x_2023);
x_1836 = x_2024;
x_1837 = x_2018;
goto block_2011;
}
block_2011:
{
if (lean_obj_tag(x_1836) == 0)
{
lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; lean_object* x_1896; lean_object* x_1897; lean_object* x_1997; 
x_1838 = lean_ctor_get(x_1836, 1);
lean_inc(x_1838);
if (lean_is_exclusive(x_1836)) {
 lean_ctor_release(x_1836, 0);
 lean_ctor_release(x_1836, 1);
 x_1839 = x_1836;
} else {
 lean_dec_ref(x_1836);
 x_1839 = lean_box(0);
}
x_1840 = lean_ctor_get(x_1, 8);
lean_inc(x_1840);
x_1997 = lean_io_remove_file(x_18, x_1837);
if (lean_obj_tag(x_1997) == 0)
{
lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; lean_object* x_2001; 
x_1998 = lean_ctor_get(x_1997, 0);
lean_inc(x_1998);
x_1999 = lean_ctor_get(x_1997, 1);
lean_inc(x_1999);
lean_dec(x_1997);
if (lean_is_scalar(x_1835)) {
 x_2000 = lean_alloc_ctor(1, 1, 0);
} else {
 x_2000 = x_1835;
}
lean_ctor_set(x_2000, 0, x_1998);
if (lean_is_scalar(x_1839)) {
 x_2001 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2001 = x_1839;
}
lean_ctor_set(x_2001, 0, x_2000);
lean_ctor_set(x_2001, 1, x_1838);
x_1896 = x_2001;
x_1897 = x_1999;
goto block_1996;
}
else
{
lean_object* x_2002; lean_object* x_2003; lean_object* x_2004; lean_object* x_2005; 
x_2002 = lean_ctor_get(x_1997, 0);
lean_inc(x_2002);
x_2003 = lean_ctor_get(x_1997, 1);
lean_inc(x_2003);
lean_dec(x_1997);
if (lean_is_scalar(x_1835)) {
 x_2004 = lean_alloc_ctor(0, 1, 0);
} else {
 x_2004 = x_1835;
 lean_ctor_set_tag(x_2004, 0);
}
lean_ctor_set(x_2004, 0, x_2002);
if (lean_is_scalar(x_1839)) {
 x_2005 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2005 = x_1839;
}
lean_ctor_set(x_2005, 0, x_2004);
lean_ctor_set(x_2005, 1, x_1838);
x_1896 = x_2005;
x_1897 = x_2003;
goto block_1996;
}
block_1895:
{
if (lean_obj_tag(x_1841) == 0)
{
lean_object* x_1843; lean_object* x_1844; lean_object* x_1845; 
x_1843 = lean_ctor_get(x_1841, 1);
lean_inc(x_1843);
lean_dec(x_1841);
x_1844 = lean_ctor_get(x_1, 9);
lean_inc(x_1844);
lean_dec(x_1);
x_1845 = l_Lake_elabConfigFile(x_13, x_1840, x_1844, x_4, x_1843, x_1842);
if (lean_obj_tag(x_1845) == 0)
{
lean_object* x_1846; 
x_1846 = lean_ctor_get(x_1845, 0);
lean_inc(x_1846);
if (lean_obj_tag(x_1846) == 0)
{
lean_object* x_1847; lean_object* x_1848; lean_object* x_1849; lean_object* x_1850; uint8_t x_1851; lean_object* x_1852; 
x_1847 = lean_ctor_get(x_1845, 1);
lean_inc(x_1847);
lean_dec(x_1845);
x_1848 = lean_ctor_get(x_1846, 0);
lean_inc(x_1848);
x_1849 = lean_ctor_get(x_1846, 1);
lean_inc(x_1849);
if (lean_is_exclusive(x_1846)) {
 lean_ctor_release(x_1846, 0);
 lean_ctor_release(x_1846, 1);
 x_1850 = x_1846;
} else {
 lean_dec_ref(x_1846);
 x_1850 = lean_box(0);
}
x_1851 = 0;
lean_inc(x_1848);
x_1852 = lean_write_module(x_1848, x_18, x_1851, x_1847);
if (lean_obj_tag(x_1852) == 0)
{
lean_object* x_1853; lean_object* x_1854; 
x_1853 = lean_ctor_get(x_1852, 1);
lean_inc(x_1853);
lean_dec(x_1852);
x_1854 = lean_io_prim_handle_unlock(x_1834, x_1853);
lean_dec(x_1834);
if (lean_obj_tag(x_1854) == 0)
{
lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; 
x_1855 = lean_ctor_get(x_1854, 1);
lean_inc(x_1855);
if (lean_is_exclusive(x_1854)) {
 lean_ctor_release(x_1854, 0);
 lean_ctor_release(x_1854, 1);
 x_1856 = x_1854;
} else {
 lean_dec_ref(x_1854);
 x_1856 = lean_box(0);
}
if (lean_is_scalar(x_1850)) {
 x_1857 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1857 = x_1850;
}
lean_ctor_set(x_1857, 0, x_1848);
lean_ctor_set(x_1857, 1, x_1849);
if (lean_is_scalar(x_1856)) {
 x_1858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1858 = x_1856;
}
lean_ctor_set(x_1858, 0, x_1857);
lean_ctor_set(x_1858, 1, x_1855);
return x_1858;
}
else
{
lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; uint8_t x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; 
lean_dec(x_1848);
x_1859 = lean_ctor_get(x_1854, 0);
lean_inc(x_1859);
x_1860 = lean_ctor_get(x_1854, 1);
lean_inc(x_1860);
if (lean_is_exclusive(x_1854)) {
 lean_ctor_release(x_1854, 0);
 lean_ctor_release(x_1854, 1);
 x_1861 = x_1854;
} else {
 lean_dec_ref(x_1854);
 x_1861 = lean_box(0);
}
x_1862 = lean_io_error_to_string(x_1859);
x_1863 = 3;
x_1864 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1864, 0, x_1862);
lean_ctor_set_uint8(x_1864, sizeof(void*)*1, x_1863);
x_1865 = lean_array_get_size(x_1849);
x_1866 = lean_array_push(x_1849, x_1864);
if (lean_is_scalar(x_1850)) {
 x_1867 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1867 = x_1850;
 lean_ctor_set_tag(x_1867, 1);
}
lean_ctor_set(x_1867, 0, x_1865);
lean_ctor_set(x_1867, 1, x_1866);
if (lean_is_scalar(x_1861)) {
 x_1868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1868 = x_1861;
 lean_ctor_set_tag(x_1868, 0);
}
lean_ctor_set(x_1868, 0, x_1867);
lean_ctor_set(x_1868, 1, x_1860);
return x_1868;
}
}
else
{
lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; uint8_t x_1873; lean_object* x_1874; lean_object* x_1875; lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; 
lean_dec(x_1848);
lean_dec(x_1834);
x_1869 = lean_ctor_get(x_1852, 0);
lean_inc(x_1869);
x_1870 = lean_ctor_get(x_1852, 1);
lean_inc(x_1870);
if (lean_is_exclusive(x_1852)) {
 lean_ctor_release(x_1852, 0);
 lean_ctor_release(x_1852, 1);
 x_1871 = x_1852;
} else {
 lean_dec_ref(x_1852);
 x_1871 = lean_box(0);
}
x_1872 = lean_io_error_to_string(x_1869);
x_1873 = 3;
x_1874 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1874, 0, x_1872);
lean_ctor_set_uint8(x_1874, sizeof(void*)*1, x_1873);
x_1875 = lean_array_get_size(x_1849);
x_1876 = lean_array_push(x_1849, x_1874);
if (lean_is_scalar(x_1850)) {
 x_1877 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1877 = x_1850;
 lean_ctor_set_tag(x_1877, 1);
}
lean_ctor_set(x_1877, 0, x_1875);
lean_ctor_set(x_1877, 1, x_1876);
if (lean_is_scalar(x_1871)) {
 x_1878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1878 = x_1871;
 lean_ctor_set_tag(x_1878, 0);
}
lean_ctor_set(x_1878, 0, x_1877);
lean_ctor_set(x_1878, 1, x_1870);
return x_1878;
}
}
else
{
lean_object* x_1879; lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; 
lean_dec(x_1834);
lean_dec(x_18);
x_1879 = lean_ctor_get(x_1845, 1);
lean_inc(x_1879);
if (lean_is_exclusive(x_1845)) {
 lean_ctor_release(x_1845, 0);
 lean_ctor_release(x_1845, 1);
 x_1880 = x_1845;
} else {
 lean_dec_ref(x_1845);
 x_1880 = lean_box(0);
}
x_1881 = lean_ctor_get(x_1846, 0);
lean_inc(x_1881);
x_1882 = lean_ctor_get(x_1846, 1);
lean_inc(x_1882);
if (lean_is_exclusive(x_1846)) {
 lean_ctor_release(x_1846, 0);
 lean_ctor_release(x_1846, 1);
 x_1883 = x_1846;
} else {
 lean_dec_ref(x_1846);
 x_1883 = lean_box(0);
}
if (lean_is_scalar(x_1883)) {
 x_1884 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1884 = x_1883;
}
lean_ctor_set(x_1884, 0, x_1881);
lean_ctor_set(x_1884, 1, x_1882);
if (lean_is_scalar(x_1880)) {
 x_1885 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1885 = x_1880;
}
lean_ctor_set(x_1885, 0, x_1884);
lean_ctor_set(x_1885, 1, x_1879);
return x_1885;
}
}
else
{
lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; 
lean_dec(x_1834);
lean_dec(x_18);
x_1886 = lean_ctor_get(x_1845, 0);
lean_inc(x_1886);
x_1887 = lean_ctor_get(x_1845, 1);
lean_inc(x_1887);
if (lean_is_exclusive(x_1845)) {
 lean_ctor_release(x_1845, 0);
 lean_ctor_release(x_1845, 1);
 x_1888 = x_1845;
} else {
 lean_dec_ref(x_1845);
 x_1888 = lean_box(0);
}
if (lean_is_scalar(x_1888)) {
 x_1889 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1889 = x_1888;
}
lean_ctor_set(x_1889, 0, x_1886);
lean_ctor_set(x_1889, 1, x_1887);
return x_1889;
}
}
else
{
lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; 
lean_dec(x_1840);
lean_dec(x_1834);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1890 = lean_ctor_get(x_1841, 0);
lean_inc(x_1890);
x_1891 = lean_ctor_get(x_1841, 1);
lean_inc(x_1891);
if (lean_is_exclusive(x_1841)) {
 lean_ctor_release(x_1841, 0);
 lean_ctor_release(x_1841, 1);
 x_1892 = x_1841;
} else {
 lean_dec_ref(x_1841);
 x_1892 = lean_box(0);
}
if (lean_is_scalar(x_1892)) {
 x_1893 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1893 = x_1892;
}
lean_ctor_set(x_1893, 0, x_1890);
lean_ctor_set(x_1893, 1, x_1891);
x_1894 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1894, 0, x_1893);
lean_ctor_set(x_1894, 1, x_1842);
return x_1894;
}
}
block_1996:
{
lean_object* x_1898; 
x_1898 = lean_ctor_get(x_1896, 0);
lean_inc(x_1898);
if (lean_obj_tag(x_1898) == 0)
{
lean_object* x_1899; 
x_1899 = lean_ctor_get(x_1898, 0);
lean_inc(x_1899);
lean_dec(x_1898);
if (lean_obj_tag(x_1899) == 11)
{
lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; lean_object* x_1909; 
lean_dec(x_1899);
lean_dec(x_21);
x_1900 = lean_ctor_get(x_1896, 1);
lean_inc(x_1900);
if (lean_is_exclusive(x_1896)) {
 lean_ctor_release(x_1896, 0);
 lean_ctor_release(x_1896, 1);
 x_1901 = x_1896;
} else {
 lean_dec_ref(x_1896);
 x_1901 = lean_box(0);
}
x_1902 = lean_ctor_get(x_1, 0);
lean_inc(x_1902);
x_1903 = l_Lake_Env_leanGithash(x_1902);
lean_dec(x_1902);
x_1904 = l_System_Platform_target;
lean_inc(x_1840);
x_1905 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1905, 0, x_1904);
lean_ctor_set(x_1905, 1, x_1903);
lean_ctor_set(x_1905, 2, x_27);
lean_ctor_set(x_1905, 3, x_1840);
x_1906 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1905);
x_1907 = lean_unsigned_to_nat(80u);
x_1908 = l_Lean_Json_pretty(x_1906, x_1907);
x_1909 = l_IO_FS_Handle_putStrLn(x_1834, x_1908, x_1897);
if (lean_obj_tag(x_1909) == 0)
{
lean_object* x_1910; lean_object* x_1911; 
x_1910 = lean_ctor_get(x_1909, 1);
lean_inc(x_1910);
lean_dec(x_1909);
x_1911 = lean_io_prim_handle_truncate(x_1834, x_1910);
if (lean_obj_tag(x_1911) == 0)
{
lean_object* x_1912; lean_object* x_1913; lean_object* x_1914; 
x_1912 = lean_ctor_get(x_1911, 0);
lean_inc(x_1912);
x_1913 = lean_ctor_get(x_1911, 1);
lean_inc(x_1913);
lean_dec(x_1911);
if (lean_is_scalar(x_1901)) {
 x_1914 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1914 = x_1901;
}
lean_ctor_set(x_1914, 0, x_1912);
lean_ctor_set(x_1914, 1, x_1900);
x_1841 = x_1914;
x_1842 = x_1913;
goto block_1895;
}
else
{
lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; uint8_t x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; 
x_1915 = lean_ctor_get(x_1911, 0);
lean_inc(x_1915);
x_1916 = lean_ctor_get(x_1911, 1);
lean_inc(x_1916);
lean_dec(x_1911);
x_1917 = lean_io_error_to_string(x_1915);
x_1918 = 3;
x_1919 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1919, 0, x_1917);
lean_ctor_set_uint8(x_1919, sizeof(void*)*1, x_1918);
x_1920 = lean_array_get_size(x_1900);
x_1921 = lean_array_push(x_1900, x_1919);
if (lean_is_scalar(x_1901)) {
 x_1922 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1922 = x_1901;
 lean_ctor_set_tag(x_1922, 1);
}
lean_ctor_set(x_1922, 0, x_1920);
lean_ctor_set(x_1922, 1, x_1921);
x_1841 = x_1922;
x_1842 = x_1916;
goto block_1895;
}
}
else
{
lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; uint8_t x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; lean_object* x_1931; lean_object* x_1932; 
lean_dec(x_1840);
lean_dec(x_1834);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1923 = lean_ctor_get(x_1909, 0);
lean_inc(x_1923);
x_1924 = lean_ctor_get(x_1909, 1);
lean_inc(x_1924);
if (lean_is_exclusive(x_1909)) {
 lean_ctor_release(x_1909, 0);
 lean_ctor_release(x_1909, 1);
 x_1925 = x_1909;
} else {
 lean_dec_ref(x_1909);
 x_1925 = lean_box(0);
}
x_1926 = lean_io_error_to_string(x_1923);
x_1927 = 3;
x_1928 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1928, 0, x_1926);
lean_ctor_set_uint8(x_1928, sizeof(void*)*1, x_1927);
x_1929 = lean_array_get_size(x_1900);
x_1930 = lean_array_push(x_1900, x_1928);
if (lean_is_scalar(x_1901)) {
 x_1931 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1931 = x_1901;
 lean_ctor_set_tag(x_1931, 1);
}
lean_ctor_set(x_1931, 0, x_1929);
lean_ctor_set(x_1931, 1, x_1930);
if (lean_is_scalar(x_1925)) {
 x_1932 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1932 = x_1925;
 lean_ctor_set_tag(x_1932, 0);
}
lean_ctor_set(x_1932, 0, x_1931);
lean_ctor_set(x_1932, 1, x_1924);
return x_1932;
}
}
else
{
lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; uint8_t x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; 
lean_dec(x_1840);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1933 = lean_ctor_get(x_1896, 1);
lean_inc(x_1933);
if (lean_is_exclusive(x_1896)) {
 lean_ctor_release(x_1896, 0);
 lean_ctor_release(x_1896, 1);
 x_1934 = x_1896;
} else {
 lean_dec_ref(x_1896);
 x_1934 = lean_box(0);
}
x_1935 = lean_io_error_to_string(x_1899);
x_1936 = 3;
x_1937 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1937, 0, x_1935);
lean_ctor_set_uint8(x_1937, sizeof(void*)*1, x_1936);
x_1938 = lean_array_get_size(x_1933);
x_1939 = lean_array_push(x_1933, x_1937);
x_1940 = lean_io_prim_handle_unlock(x_1834, x_1897);
lean_dec(x_1834);
if (lean_obj_tag(x_1940) == 0)
{
lean_object* x_1941; lean_object* x_1942; 
x_1941 = lean_ctor_get(x_1940, 1);
lean_inc(x_1941);
lean_dec(x_1940);
x_1942 = lean_io_remove_file(x_21, x_1941);
lean_dec(x_21);
if (lean_obj_tag(x_1942) == 0)
{
lean_object* x_1943; lean_object* x_1944; lean_object* x_1945; lean_object* x_1946; 
x_1943 = lean_ctor_get(x_1942, 1);
lean_inc(x_1943);
if (lean_is_exclusive(x_1942)) {
 lean_ctor_release(x_1942, 0);
 lean_ctor_release(x_1942, 1);
 x_1944 = x_1942;
} else {
 lean_dec_ref(x_1942);
 x_1944 = lean_box(0);
}
if (lean_is_scalar(x_1934)) {
 x_1945 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1945 = x_1934;
 lean_ctor_set_tag(x_1945, 1);
}
lean_ctor_set(x_1945, 0, x_1938);
lean_ctor_set(x_1945, 1, x_1939);
if (lean_is_scalar(x_1944)) {
 x_1946 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1946 = x_1944;
}
lean_ctor_set(x_1946, 0, x_1945);
lean_ctor_set(x_1946, 1, x_1943);
return x_1946;
}
else
{
lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; 
x_1947 = lean_ctor_get(x_1942, 0);
lean_inc(x_1947);
x_1948 = lean_ctor_get(x_1942, 1);
lean_inc(x_1948);
if (lean_is_exclusive(x_1942)) {
 lean_ctor_release(x_1942, 0);
 lean_ctor_release(x_1942, 1);
 x_1949 = x_1942;
} else {
 lean_dec_ref(x_1942);
 x_1949 = lean_box(0);
}
x_1950 = lean_io_error_to_string(x_1947);
x_1951 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1951, 0, x_1950);
lean_ctor_set_uint8(x_1951, sizeof(void*)*1, x_1936);
x_1952 = lean_array_push(x_1939, x_1951);
if (lean_is_scalar(x_1934)) {
 x_1953 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1953 = x_1934;
 lean_ctor_set_tag(x_1953, 1);
}
lean_ctor_set(x_1953, 0, x_1938);
lean_ctor_set(x_1953, 1, x_1952);
if (lean_is_scalar(x_1949)) {
 x_1954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1954 = x_1949;
 lean_ctor_set_tag(x_1954, 0);
}
lean_ctor_set(x_1954, 0, x_1953);
lean_ctor_set(x_1954, 1, x_1948);
return x_1954;
}
}
else
{
lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; 
lean_dec(x_21);
x_1955 = lean_ctor_get(x_1940, 0);
lean_inc(x_1955);
x_1956 = lean_ctor_get(x_1940, 1);
lean_inc(x_1956);
if (lean_is_exclusive(x_1940)) {
 lean_ctor_release(x_1940, 0);
 lean_ctor_release(x_1940, 1);
 x_1957 = x_1940;
} else {
 lean_dec_ref(x_1940);
 x_1957 = lean_box(0);
}
x_1958 = lean_io_error_to_string(x_1955);
x_1959 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1959, 0, x_1958);
lean_ctor_set_uint8(x_1959, sizeof(void*)*1, x_1936);
x_1960 = lean_array_push(x_1939, x_1959);
if (lean_is_scalar(x_1934)) {
 x_1961 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1961 = x_1934;
 lean_ctor_set_tag(x_1961, 1);
}
lean_ctor_set(x_1961, 0, x_1938);
lean_ctor_set(x_1961, 1, x_1960);
if (lean_is_scalar(x_1957)) {
 x_1962 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1962 = x_1957;
 lean_ctor_set_tag(x_1962, 0);
}
lean_ctor_set(x_1962, 0, x_1961);
lean_ctor_set(x_1962, 1, x_1956);
return x_1962;
}
}
}
else
{
lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; 
lean_dec(x_1898);
lean_dec(x_21);
x_1963 = lean_ctor_get(x_1896, 1);
lean_inc(x_1963);
if (lean_is_exclusive(x_1896)) {
 lean_ctor_release(x_1896, 0);
 lean_ctor_release(x_1896, 1);
 x_1964 = x_1896;
} else {
 lean_dec_ref(x_1896);
 x_1964 = lean_box(0);
}
x_1965 = lean_ctor_get(x_1, 0);
lean_inc(x_1965);
x_1966 = l_Lake_Env_leanGithash(x_1965);
lean_dec(x_1965);
x_1967 = l_System_Platform_target;
lean_inc(x_1840);
x_1968 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1968, 0, x_1967);
lean_ctor_set(x_1968, 1, x_1966);
lean_ctor_set(x_1968, 2, x_27);
lean_ctor_set(x_1968, 3, x_1840);
x_1969 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1968);
x_1970 = lean_unsigned_to_nat(80u);
x_1971 = l_Lean_Json_pretty(x_1969, x_1970);
x_1972 = l_IO_FS_Handle_putStrLn(x_1834, x_1971, x_1897);
if (lean_obj_tag(x_1972) == 0)
{
lean_object* x_1973; lean_object* x_1974; 
x_1973 = lean_ctor_get(x_1972, 1);
lean_inc(x_1973);
lean_dec(x_1972);
x_1974 = lean_io_prim_handle_truncate(x_1834, x_1973);
if (lean_obj_tag(x_1974) == 0)
{
lean_object* x_1975; lean_object* x_1976; lean_object* x_1977; 
x_1975 = lean_ctor_get(x_1974, 0);
lean_inc(x_1975);
x_1976 = lean_ctor_get(x_1974, 1);
lean_inc(x_1976);
lean_dec(x_1974);
if (lean_is_scalar(x_1964)) {
 x_1977 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1977 = x_1964;
}
lean_ctor_set(x_1977, 0, x_1975);
lean_ctor_set(x_1977, 1, x_1963);
x_1841 = x_1977;
x_1842 = x_1976;
goto block_1895;
}
else
{
lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; uint8_t x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; 
x_1978 = lean_ctor_get(x_1974, 0);
lean_inc(x_1978);
x_1979 = lean_ctor_get(x_1974, 1);
lean_inc(x_1979);
lean_dec(x_1974);
x_1980 = lean_io_error_to_string(x_1978);
x_1981 = 3;
x_1982 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1982, 0, x_1980);
lean_ctor_set_uint8(x_1982, sizeof(void*)*1, x_1981);
x_1983 = lean_array_get_size(x_1963);
x_1984 = lean_array_push(x_1963, x_1982);
if (lean_is_scalar(x_1964)) {
 x_1985 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1985 = x_1964;
 lean_ctor_set_tag(x_1985, 1);
}
lean_ctor_set(x_1985, 0, x_1983);
lean_ctor_set(x_1985, 1, x_1984);
x_1841 = x_1985;
x_1842 = x_1979;
goto block_1895;
}
}
else
{
lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; uint8_t x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; 
lean_dec(x_1840);
lean_dec(x_1834);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1986 = lean_ctor_get(x_1972, 0);
lean_inc(x_1986);
x_1987 = lean_ctor_get(x_1972, 1);
lean_inc(x_1987);
if (lean_is_exclusive(x_1972)) {
 lean_ctor_release(x_1972, 0);
 lean_ctor_release(x_1972, 1);
 x_1988 = x_1972;
} else {
 lean_dec_ref(x_1972);
 x_1988 = lean_box(0);
}
x_1989 = lean_io_error_to_string(x_1986);
x_1990 = 3;
x_1991 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1991, 0, x_1989);
lean_ctor_set_uint8(x_1991, sizeof(void*)*1, x_1990);
x_1992 = lean_array_get_size(x_1963);
x_1993 = lean_array_push(x_1963, x_1991);
if (lean_is_scalar(x_1964)) {
 x_1994 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1994 = x_1964;
 lean_ctor_set_tag(x_1994, 1);
}
lean_ctor_set(x_1994, 0, x_1992);
lean_ctor_set(x_1994, 1, x_1993);
if (lean_is_scalar(x_1988)) {
 x_1995 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1995 = x_1988;
 lean_ctor_set_tag(x_1995, 0);
}
lean_ctor_set(x_1995, 0, x_1994);
lean_ctor_set(x_1995, 1, x_1987);
return x_1995;
}
}
}
}
else
{
lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; 
lean_dec(x_1835);
lean_dec(x_1834);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_2006 = lean_ctor_get(x_1836, 0);
lean_inc(x_2006);
x_2007 = lean_ctor_get(x_1836, 1);
lean_inc(x_2007);
if (lean_is_exclusive(x_1836)) {
 lean_ctor_release(x_1836, 0);
 lean_ctor_release(x_1836, 1);
 x_2008 = x_1836;
} else {
 lean_dec_ref(x_1836);
 x_2008 = lean_box(0);
}
if (lean_is_scalar(x_2008)) {
 x_2009 = lean_alloc_ctor(1, 2, 0);
} else {
 x_2009 = x_2008;
}
lean_ctor_set(x_2009, 0, x_2006);
lean_ctor_set(x_2009, 1, x_2007);
x_2010 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2010, 0, x_2009);
lean_ctor_set(x_2010, 1, x_1837);
return x_2010;
}
}
}
}
}
}
else
{
uint8_t x_2116; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_2116 = !lean_is_exclusive(x_25);
if (x_2116 == 0)
{
lean_object* x_2117; 
x_2117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2117, 0, x_25);
lean_ctor_set(x_2117, 1, x_26);
return x_2117;
}
else
{
lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; 
x_2118 = lean_ctor_get(x_25, 0);
x_2119 = lean_ctor_get(x_25, 1);
lean_inc(x_2119);
lean_inc(x_2118);
lean_dec(x_25);
x_2120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2120, 0, x_2118);
lean_ctor_set(x_2120, 1, x_2119);
x_2121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2121, 0, x_2120);
lean_ctor_set(x_2121, 1, x_26);
return x_2121;
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
if (builtin) {res = l_Lake_initFn____x40_Lake_Load_Lean_Elab___hyg_121_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lake_importEnvCache = lean_io_result_get_value(res);
lean_mark_persistent(l_Lake_importEnvCache);
lean_dec_ref(res);
}l_Lake_importModulesUsingCache___lambda__1___closed__1 = _init_l_Lake_importModulesUsingCache___lambda__1___closed__1();
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
l_Lake_elabConfigFile___closed__1 = _init_l_Lake_elabConfigFile___closed__1();
lean_mark_persistent(l_Lake_elabConfigFile___closed__1);
l_Lake_elabConfigFile___closed__2 = _init_l_Lake_elabConfigFile___closed__2();
lean_mark_persistent(l_Lake_elabConfigFile___closed__2);
l_Lake_elabConfigFile___closed__3 = _init_l_Lake_elabConfigFile___closed__3();
lean_mark_persistent(l_Lake_elabConfigFile___closed__3);
l_Lake_elabConfigFile___closed__4 = _init_l_Lake_elabConfigFile___closed__4();
lean_mark_persistent(l_Lake_elabConfigFile___closed__4);
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
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__1 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__1();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__1);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__2 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__2();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__2);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__3 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__3();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__3);
l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__4 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__4();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870____closed__4);
l_Lake_instToJsonConfigTrace___closed__1 = _init_l_Lake_instToJsonConfigTrace___closed__1();
lean_mark_persistent(l_Lake_instToJsonConfigTrace___closed__1);
l_Lake_instToJsonConfigTrace = _init_l_Lake_instToJsonConfigTrace();
lean_mark_persistent(l_Lake_instToJsonConfigTrace);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__1 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__1();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__1);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__2 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__2();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__2);
l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__3 = _init_l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__3();
lean_mark_persistent(l_Lean_Json_getObjValAs_x3f___at___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____spec__1___closed__3);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__1 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__1();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__1);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__2 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__2();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__2);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__3);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__4 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__4();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__4);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__5 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__5();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__5);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__6 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__6();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__6);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__7 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__7();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__7);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__8 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__8();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__8);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__9 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__9();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__9);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__10 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__10();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__10);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__11 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__11();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__11);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__12 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__12();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__12);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__13 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__13();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__13);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__14 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__14();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__14);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__15 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__15();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__15);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__16 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__16();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__16);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__17 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__17();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__17);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__18 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__18();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__18);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__19 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__19();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__19);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__20 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__20();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__20);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__21 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__21();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__21);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__22 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__22();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__22);
l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__23 = _init_l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__23();
lean_mark_persistent(l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950____closed__23);
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
