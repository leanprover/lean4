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
lean_object* lean_read_module_data(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_importConfigFileCore___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_importModules(lean_object*, lean_object*, uint32_t, lean_object*, uint8_t, uint8_t, lean_object*);
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
lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lake_importModulesUsingCache___lambda__1___closed__1;
x_7 = 0;
x_8 = 1;
lean_inc(x_1);
x_9 = l_Lean_importModules(x_1, x_2, x_3, x_6, x_7, x_8, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; size_t x_28; uint64_t x_29; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lake_importModulesUsingCache___lambda__1___closed__2;
x_13 = lean_st_ref_take(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_18 = x_14;
} else {
 lean_dec_ref(x_14);
 x_18 = lean_box(0);
}
x_19 = lean_array_get_size(x_17);
x_20 = 7;
x_21 = lean_array_get_size(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
x_24 = 32;
x_25 = 16;
x_26 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_27 = 1;
x_28 = lean_usize_sub(x_26, x_27);
if (x_23 == 0)
{
lean_dec(x_21);
x_29 = x_20;
goto block_71;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_le(x_21, x_21);
if (x_72 == 0)
{
lean_dec(x_21);
x_29 = x_20;
goto block_71;
}
else
{
size_t x_73; size_t x_74; uint64_t x_75; 
x_73 = 0;
x_74 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_75 = l_Array_foldlMUnsafe_fold___at_Lake_importModulesUsingCache___spec__5(x_1, x_73, x_74, x_20);
x_29 = x_75;
goto block_71;
}
}
block_71:
{
uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_30 = lean_uint64_shift_right(x_29, x_24);
x_31 = lean_uint64_xor(x_29, x_30);
x_32 = lean_uint64_shift_right(x_31, x_25);
x_33 = lean_uint64_xor(x_31, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_land(x_34, x_28);
x_36 = lean_array_uget(x_17, x_35);
x_37 = l_Std_DHashMap_Internal_AssocList_contains___at_Lake_importModulesUsingCache___spec__1(x_1, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_16, x_38);
lean_dec(x_16);
lean_inc(x_10);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_10);
lean_ctor_set(x_40, 2, x_36);
x_41 = lean_array_uset(x_17, x_35, x_40);
x_42 = lean_unsigned_to_nat(4u);
x_43 = lean_nat_mul(x_39, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lake_importModulesUsingCache___spec__3(x_41);
if (lean_is_scalar(x_18)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_18;
}
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_st_ref_set(x_12, x_49, x_15);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
lean_ctor_set(x_50, 0, x_10);
return x_50;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_10);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
if (lean_is_scalar(x_18)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_18;
}
lean_ctor_set(x_55, 0, x_39);
lean_ctor_set(x_55, 1, x_41);
x_56 = lean_st_ref_set(x_12, x_55, x_15);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set(x_56, 0, x_10);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_10);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_61 = lean_box(0);
x_62 = lean_array_uset(x_17, x_35, x_61);
lean_inc(x_10);
x_63 = l_Std_DHashMap_Internal_AssocList_replace___at_Lake_importModulesUsingCache___spec__8(x_1, x_10, x_36);
x_64 = lean_array_uset(x_62, x_35, x_63);
if (lean_is_scalar(x_18)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_18;
}
lean_ctor_set(x_65, 0, x_16);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_st_ref_set(x_12, x_65, x_15);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_10);
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_10);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_9);
if (x_76 == 0)
{
return x_9;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_9, 0);
x_78 = lean_ctor_get(x_9, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_9);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_2113; 
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
x_2113 = l_Lake_computeTextFileHash(x_4, x_3);
if (lean_obj_tag(x_2113) == 0)
{
uint8_t x_2114; 
x_2114 = !lean_is_exclusive(x_2113);
if (x_2114 == 0)
{
lean_object* x_2115; 
x_2115 = lean_ctor_get(x_2113, 1);
lean_ctor_set(x_2113, 1, x_2);
x_25 = x_2113;
x_26 = x_2115;
goto block_2112;
}
else
{
lean_object* x_2116; lean_object* x_2117; lean_object* x_2118; 
x_2116 = lean_ctor_get(x_2113, 0);
x_2117 = lean_ctor_get(x_2113, 1);
lean_inc(x_2117);
lean_inc(x_2116);
lean_dec(x_2113);
x_2118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2118, 0, x_2116);
lean_ctor_set(x_2118, 1, x_2);
x_25 = x_2118;
x_26 = x_2117;
goto block_2112;
}
}
else
{
uint8_t x_2119; 
x_2119 = !lean_is_exclusive(x_2113);
if (x_2119 == 0)
{
lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; uint8_t x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; 
x_2120 = lean_ctor_get(x_2113, 0);
x_2121 = lean_ctor_get(x_2113, 1);
x_2122 = lean_io_error_to_string(x_2120);
x_2123 = 3;
x_2124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2124, 0, x_2122);
lean_ctor_set_uint8(x_2124, sizeof(void*)*1, x_2123);
x_2125 = lean_array_get_size(x_2);
x_2126 = lean_array_push(x_2, x_2124);
lean_ctor_set(x_2113, 1, x_2126);
lean_ctor_set(x_2113, 0, x_2125);
x_25 = x_2113;
x_26 = x_2121;
goto block_2112;
}
else
{
lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; uint8_t x_2130; lean_object* x_2131; lean_object* x_2132; lean_object* x_2133; lean_object* x_2134; 
x_2127 = lean_ctor_get(x_2113, 0);
x_2128 = lean_ctor_get(x_2113, 1);
lean_inc(x_2128);
lean_inc(x_2127);
lean_dec(x_2113);
x_2129 = lean_io_error_to_string(x_2127);
x_2130 = 3;
x_2131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2131, 0, x_2129);
lean_ctor_set_uint8(x_2131, sizeof(void*)*1, x_2130);
x_2132 = lean_array_get_size(x_2);
x_2133 = lean_array_push(x_2, x_2131);
x_2134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2134, 0, x_2132);
lean_ctor_set(x_2134, 1, x_2133);
x_25 = x_2134;
x_26 = x_2128;
goto block_2112;
}
}
block_2112:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_524; lean_object* x_525; lean_object* x_1266; lean_object* x_1267; lean_object* x_2016; lean_object* x_2017; uint8_t x_2018; 
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
x_2016 = l_System_FilePath_pathExists(x_21, x_26);
x_2017 = lean_ctor_get(x_2016, 0);
lean_inc(x_2017);
x_2018 = lean_unbox(x_2017);
lean_dec(x_2017);
if (x_2018 == 0)
{
uint8_t x_2019; 
x_2019 = !lean_is_exclusive(x_2016);
if (x_2019 == 0)
{
lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; 
x_2020 = lean_ctor_get(x_2016, 1);
x_2021 = lean_ctor_get(x_2016, 0);
lean_dec(x_2021);
x_2022 = l_IO_FS_createDirAll(x_15, x_2020);
lean_dec(x_15);
if (lean_obj_tag(x_2022) == 0)
{
lean_object* x_2023; uint8_t x_2024; lean_object* x_2025; 
lean_free_object(x_2016);
x_2023 = lean_ctor_get(x_2022, 1);
lean_inc(x_2023);
lean_dec(x_2022);
x_2024 = 2;
x_2025 = lean_io_prim_handle_mk(x_21, x_2024, x_2023);
if (lean_obj_tag(x_2025) == 0)
{
uint8_t x_2026; 
x_2026 = !lean_is_exclusive(x_2025);
if (x_2026 == 0)
{
lean_object* x_2027; lean_object* x_2028; lean_object* x_2029; 
x_2027 = lean_ctor_get(x_2025, 0);
x_2028 = lean_ctor_get(x_2025, 1);
x_2029 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2029, 0, x_2027);
lean_ctor_set(x_2025, 1, x_28);
lean_ctor_set(x_2025, 0, x_2029);
x_1266 = x_2025;
x_1267 = x_2028;
goto block_2015;
}
else
{
lean_object* x_2030; lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; 
x_2030 = lean_ctor_get(x_2025, 0);
x_2031 = lean_ctor_get(x_2025, 1);
lean_inc(x_2031);
lean_inc(x_2030);
lean_dec(x_2025);
x_2032 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2032, 0, x_2030);
x_2033 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2033, 0, x_2032);
lean_ctor_set(x_2033, 1, x_28);
x_1266 = x_2033;
x_1267 = x_2031;
goto block_2015;
}
}
else
{
uint8_t x_2034; 
x_2034 = !lean_is_exclusive(x_2025);
if (x_2034 == 0)
{
lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; 
x_2035 = lean_ctor_get(x_2025, 0);
x_2036 = lean_ctor_get(x_2025, 1);
x_2037 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2037, 0, x_2035);
lean_ctor_set_tag(x_2025, 0);
lean_ctor_set(x_2025, 1, x_28);
lean_ctor_set(x_2025, 0, x_2037);
x_1266 = x_2025;
x_1267 = x_2036;
goto block_2015;
}
else
{
lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; 
x_2038 = lean_ctor_get(x_2025, 0);
x_2039 = lean_ctor_get(x_2025, 1);
lean_inc(x_2039);
lean_inc(x_2038);
lean_dec(x_2025);
x_2040 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2040, 0, x_2038);
x_2041 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2041, 0, x_2040);
lean_ctor_set(x_2041, 1, x_28);
x_1266 = x_2041;
x_1267 = x_2039;
goto block_2015;
}
}
}
else
{
uint8_t x_2042; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_2042 = !lean_is_exclusive(x_2022);
if (x_2042 == 0)
{
lean_object* x_2043; lean_object* x_2044; uint8_t x_2045; lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; 
x_2043 = lean_ctor_get(x_2022, 0);
x_2044 = lean_io_error_to_string(x_2043);
x_2045 = 3;
x_2046 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2046, 0, x_2044);
lean_ctor_set_uint8(x_2046, sizeof(void*)*1, x_2045);
x_2047 = lean_array_get_size(x_28);
x_2048 = lean_array_push(x_28, x_2046);
lean_ctor_set_tag(x_2016, 1);
lean_ctor_set(x_2016, 1, x_2048);
lean_ctor_set(x_2016, 0, x_2047);
lean_ctor_set_tag(x_2022, 0);
lean_ctor_set(x_2022, 0, x_2016);
return x_2022;
}
else
{
lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; uint8_t x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; 
x_2049 = lean_ctor_get(x_2022, 0);
x_2050 = lean_ctor_get(x_2022, 1);
lean_inc(x_2050);
lean_inc(x_2049);
lean_dec(x_2022);
x_2051 = lean_io_error_to_string(x_2049);
x_2052 = 3;
x_2053 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2053, 0, x_2051);
lean_ctor_set_uint8(x_2053, sizeof(void*)*1, x_2052);
x_2054 = lean_array_get_size(x_28);
x_2055 = lean_array_push(x_28, x_2053);
lean_ctor_set_tag(x_2016, 1);
lean_ctor_set(x_2016, 1, x_2055);
lean_ctor_set(x_2016, 0, x_2054);
x_2056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2056, 0, x_2016);
lean_ctor_set(x_2056, 1, x_2050);
return x_2056;
}
}
}
else
{
lean_object* x_2057; lean_object* x_2058; 
x_2057 = lean_ctor_get(x_2016, 1);
lean_inc(x_2057);
lean_dec(x_2016);
x_2058 = l_IO_FS_createDirAll(x_15, x_2057);
lean_dec(x_15);
if (lean_obj_tag(x_2058) == 0)
{
lean_object* x_2059; uint8_t x_2060; lean_object* x_2061; 
x_2059 = lean_ctor_get(x_2058, 1);
lean_inc(x_2059);
lean_dec(x_2058);
x_2060 = 2;
x_2061 = lean_io_prim_handle_mk(x_21, x_2060, x_2059);
if (lean_obj_tag(x_2061) == 0)
{
lean_object* x_2062; lean_object* x_2063; lean_object* x_2064; lean_object* x_2065; lean_object* x_2066; 
x_2062 = lean_ctor_get(x_2061, 0);
lean_inc(x_2062);
x_2063 = lean_ctor_get(x_2061, 1);
lean_inc(x_2063);
if (lean_is_exclusive(x_2061)) {
 lean_ctor_release(x_2061, 0);
 lean_ctor_release(x_2061, 1);
 x_2064 = x_2061;
} else {
 lean_dec_ref(x_2061);
 x_2064 = lean_box(0);
}
x_2065 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2065, 0, x_2062);
if (lean_is_scalar(x_2064)) {
 x_2066 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2066 = x_2064;
}
lean_ctor_set(x_2066, 0, x_2065);
lean_ctor_set(x_2066, 1, x_28);
x_1266 = x_2066;
x_1267 = x_2063;
goto block_2015;
}
else
{
lean_object* x_2067; lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; lean_object* x_2071; 
x_2067 = lean_ctor_get(x_2061, 0);
lean_inc(x_2067);
x_2068 = lean_ctor_get(x_2061, 1);
lean_inc(x_2068);
if (lean_is_exclusive(x_2061)) {
 lean_ctor_release(x_2061, 0);
 lean_ctor_release(x_2061, 1);
 x_2069 = x_2061;
} else {
 lean_dec_ref(x_2061);
 x_2069 = lean_box(0);
}
x_2070 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2070, 0, x_2067);
if (lean_is_scalar(x_2069)) {
 x_2071 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2071 = x_2069;
 lean_ctor_set_tag(x_2071, 0);
}
lean_ctor_set(x_2071, 0, x_2070);
lean_ctor_set(x_2071, 1, x_28);
x_1266 = x_2071;
x_1267 = x_2068;
goto block_2015;
}
}
else
{
lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; uint8_t x_2076; lean_object* x_2077; lean_object* x_2078; lean_object* x_2079; lean_object* x_2080; lean_object* x_2081; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_2072 = lean_ctor_get(x_2058, 0);
lean_inc(x_2072);
x_2073 = lean_ctor_get(x_2058, 1);
lean_inc(x_2073);
if (lean_is_exclusive(x_2058)) {
 lean_ctor_release(x_2058, 0);
 lean_ctor_release(x_2058, 1);
 x_2074 = x_2058;
} else {
 lean_dec_ref(x_2058);
 x_2074 = lean_box(0);
}
x_2075 = lean_io_error_to_string(x_2072);
x_2076 = 3;
x_2077 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2077, 0, x_2075);
lean_ctor_set_uint8(x_2077, sizeof(void*)*1, x_2076);
x_2078 = lean_array_get_size(x_28);
x_2079 = lean_array_push(x_28, x_2077);
x_2080 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2080, 0, x_2078);
lean_ctor_set(x_2080, 1, x_2079);
if (lean_is_scalar(x_2074)) {
 x_2081 = lean_alloc_ctor(0, 2, 0);
} else {
 x_2081 = x_2074;
 lean_ctor_set_tag(x_2081, 0);
}
lean_ctor_set(x_2081, 0, x_2080);
lean_ctor_set(x_2081, 1, x_2073);
return x_2081;
}
}
}
else
{
lean_object* x_2082; uint8_t x_2083; lean_object* x_2084; 
lean_dec(x_15);
x_2082 = lean_ctor_get(x_2016, 1);
lean_inc(x_2082);
lean_dec(x_2016);
x_2083 = 0;
x_2084 = lean_io_prim_handle_mk(x_21, x_2083, x_2082);
if (lean_obj_tag(x_2084) == 0)
{
uint8_t x_2085; 
x_2085 = !lean_is_exclusive(x_2084);
if (x_2085 == 0)
{
lean_object* x_2086; 
x_2086 = lean_ctor_get(x_2084, 1);
lean_ctor_set(x_2084, 1, x_28);
x_524 = x_2084;
x_525 = x_2086;
goto block_1265;
}
else
{
lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; 
x_2087 = lean_ctor_get(x_2084, 0);
x_2088 = lean_ctor_get(x_2084, 1);
lean_inc(x_2088);
lean_inc(x_2087);
lean_dec(x_2084);
x_2089 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2089, 0, x_2087);
lean_ctor_set(x_2089, 1, x_28);
x_524 = x_2089;
x_525 = x_2088;
goto block_1265;
}
}
else
{
uint8_t x_2090; 
x_2090 = !lean_is_exclusive(x_2084);
if (x_2090 == 0)
{
lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; uint8_t x_2094; lean_object* x_2095; lean_object* x_2096; lean_object* x_2097; 
x_2091 = lean_ctor_get(x_2084, 0);
x_2092 = lean_ctor_get(x_2084, 1);
x_2093 = lean_io_error_to_string(x_2091);
x_2094 = 3;
x_2095 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2095, 0, x_2093);
lean_ctor_set_uint8(x_2095, sizeof(void*)*1, x_2094);
x_2096 = lean_array_get_size(x_28);
x_2097 = lean_array_push(x_28, x_2095);
lean_ctor_set(x_2084, 1, x_2097);
lean_ctor_set(x_2084, 0, x_2096);
x_524 = x_2084;
x_525 = x_2092;
goto block_1265;
}
else
{
lean_object* x_2098; lean_object* x_2099; lean_object* x_2100; uint8_t x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; 
x_2098 = lean_ctor_get(x_2084, 0);
x_2099 = lean_ctor_get(x_2084, 1);
lean_inc(x_2099);
lean_inc(x_2098);
lean_dec(x_2084);
x_2100 = lean_io_error_to_string(x_2098);
x_2101 = 3;
x_2102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2102, 0, x_2100);
lean_ctor_set_uint8(x_2102, sizeof(void*)*1, x_2101);
x_2103 = lean_array_get_size(x_28);
x_2104 = lean_array_push(x_28, x_2102);
x_2105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2105, 0, x_2103);
lean_ctor_set(x_2105, 1, x_2104);
x_524 = x_2105;
x_525 = x_2099;
goto block_1265;
}
}
}
block_523:
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_134; lean_object* x_135; lean_object* x_343; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_ctor_get(x_1, 8);
lean_inc(x_34);
x_343 = lean_io_remove_file(x_18, x_31);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec(x_343);
if (lean_is_scalar(x_12)) {
 x_346 = lean_alloc_ctor(1, 1, 0);
} else {
 x_346 = x_12;
}
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_30, 0, x_346);
x_134 = x_30;
x_135 = x_345;
goto block_342;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_343, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_343, 1);
lean_inc(x_348);
lean_dec(x_343);
if (lean_is_scalar(x_12)) {
 x_349 = lean_alloc_ctor(0, 1, 0);
} else {
 x_349 = x_12;
 lean_ctor_set_tag(x_349, 0);
}
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_30, 0, x_349);
x_134 = x_30;
x_135 = x_348;
goto block_342;
}
block_133:
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
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_40, 0);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
x_45 = lean_write_module(x_43, x_18, x_41);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_io_prim_handle_unlock(x_33, x_46);
lean_dec(x_33);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
lean_ctor_set(x_47, 0, x_40);
return x_47;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_43);
x_52 = !lean_is_exclusive(x_47);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_io_error_to_string(x_53);
x_55 = 3;
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_55);
x_57 = lean_array_get_size(x_44);
x_58 = lean_array_push(x_44, x_56);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_58);
lean_ctor_set(x_40, 0, x_57);
lean_ctor_set_tag(x_47, 0);
lean_ctor_set(x_47, 0, x_40);
return x_47;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_47, 0);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_47);
x_61 = lean_io_error_to_string(x_59);
x_62 = 3;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_get_size(x_44);
x_65 = lean_array_push(x_44, x_63);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_65);
lean_ctor_set(x_40, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_40);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_43);
lean_dec(x_33);
x_67 = !lean_is_exclusive(x_45);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_io_error_to_string(x_68);
x_70 = 3;
x_71 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_70);
x_72 = lean_array_get_size(x_44);
x_73 = lean_array_push(x_44, x_71);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_73);
lean_ctor_set(x_40, 0, x_72);
lean_ctor_set_tag(x_45, 0);
lean_ctor_set(x_45, 0, x_40);
return x_45;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_45, 0);
x_75 = lean_ctor_get(x_45, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_45);
x_76 = lean_io_error_to_string(x_74);
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_array_get_size(x_44);
x_80 = lean_array_push(x_44, x_78);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 1, x_80);
lean_ctor_set(x_40, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_40);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_40, 0);
x_83 = lean_ctor_get(x_40, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_40);
lean_inc(x_82);
x_84 = lean_write_module(x_82, x_18, x_41);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_io_prim_handle_unlock(x_33, x_85);
lean_dec(x_33);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_82);
lean_ctor_set(x_89, 1, x_83);
if (lean_is_scalar(x_88)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_88;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_82);
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
x_94 = lean_io_error_to_string(x_91);
x_95 = 3;
x_96 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_95);
x_97 = lean_array_get_size(x_83);
x_98 = lean_array_push(x_83, x_96);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
if (lean_is_scalar(x_93)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_93;
 lean_ctor_set_tag(x_100, 0);
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_82);
lean_dec(x_33);
x_101 = lean_ctor_get(x_84, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_84, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_103 = x_84;
} else {
 lean_dec_ref(x_84);
 x_103 = lean_box(0);
}
x_104 = lean_io_error_to_string(x_101);
x_105 = 3;
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_105);
x_107 = lean_array_get_size(x_83);
x_108 = lean_array_push(x_83, x_106);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
if (lean_is_scalar(x_103)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_103;
 lean_ctor_set_tag(x_110, 0);
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_102);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_33);
lean_dec(x_18);
x_111 = !lean_is_exclusive(x_39);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_39, 0);
lean_dec(x_112);
x_113 = !lean_is_exclusive(x_40);
if (x_113 == 0)
{
return x_39;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_40, 0);
x_115 = lean_ctor_get(x_40, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_40);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_39, 0, x_116);
return x_39;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_39, 1);
lean_inc(x_117);
lean_dec(x_39);
x_118 = lean_ctor_get(x_40, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_40, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_120 = x_40;
} else {
 lean_dec_ref(x_40);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_117);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_33);
lean_dec(x_18);
x_123 = !lean_is_exclusive(x_39);
if (x_123 == 0)
{
return x_39;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_39, 0);
x_125 = lean_ctor_get(x_39, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_39);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_35);
if (x_127 == 0)
{
lean_object* x_128; 
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_35);
lean_ctor_set(x_128, 1, x_36);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_35, 0);
x_130 = lean_ctor_get(x_35, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_35);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_36);
return x_132;
}
}
}
block_342:
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
if (lean_obj_tag(x_137) == 11)
{
uint8_t x_138; 
lean_dec(x_137);
lean_dec(x_21);
x_138 = !lean_is_exclusive(x_134);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_139 = lean_ctor_get(x_134, 1);
x_140 = lean_ctor_get(x_134, 0);
lean_dec(x_140);
x_141 = lean_ctor_get(x_1, 0);
lean_inc(x_141);
x_142 = l_Lake_Env_leanGithash(x_141);
lean_dec(x_141);
x_143 = l_System_Platform_target;
lean_inc(x_34);
x_144 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set(x_144, 2, x_27);
lean_ctor_set(x_144, 3, x_34);
x_145 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_144);
x_146 = lean_unsigned_to_nat(80u);
x_147 = l_Lean_Json_pretty(x_145, x_146);
x_148 = l_IO_FS_Handle_putStrLn(x_33, x_147, x_135);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_io_prim_handle_truncate(x_33, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
lean_ctor_set(x_134, 0, x_151);
x_35 = x_134;
x_36 = x_152;
goto block_133;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
lean_dec(x_150);
x_155 = lean_io_error_to_string(x_153);
x_156 = 3;
x_157 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set_uint8(x_157, sizeof(void*)*1, x_156);
x_158 = lean_array_get_size(x_139);
x_159 = lean_array_push(x_139, x_157);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_159);
lean_ctor_set(x_134, 0, x_158);
x_35 = x_134;
x_36 = x_154;
goto block_133;
}
}
else
{
uint8_t x_160; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_160 = !lean_is_exclusive(x_148);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_148, 0);
x_162 = lean_io_error_to_string(x_161);
x_163 = 3;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
x_165 = lean_array_get_size(x_139);
x_166 = lean_array_push(x_139, x_164);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_166);
lean_ctor_set(x_134, 0, x_165);
lean_ctor_set_tag(x_148, 0);
lean_ctor_set(x_148, 0, x_134);
return x_148;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_167 = lean_ctor_get(x_148, 0);
x_168 = lean_ctor_get(x_148, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_148);
x_169 = lean_io_error_to_string(x_167);
x_170 = 3;
x_171 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set_uint8(x_171, sizeof(void*)*1, x_170);
x_172 = lean_array_get_size(x_139);
x_173 = lean_array_push(x_139, x_171);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_173);
lean_ctor_set(x_134, 0, x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_134);
lean_ctor_set(x_174, 1, x_168);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_175 = lean_ctor_get(x_134, 1);
lean_inc(x_175);
lean_dec(x_134);
x_176 = lean_ctor_get(x_1, 0);
lean_inc(x_176);
x_177 = l_Lake_Env_leanGithash(x_176);
lean_dec(x_176);
x_178 = l_System_Platform_target;
lean_inc(x_34);
x_179 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_179, 2, x_27);
lean_ctor_set(x_179, 3, x_34);
x_180 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_179);
x_181 = lean_unsigned_to_nat(80u);
x_182 = l_Lean_Json_pretty(x_180, x_181);
x_183 = l_IO_FS_Handle_putStrLn(x_33, x_182, x_135);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_io_prim_handle_truncate(x_33, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_175);
x_35 = x_188;
x_36 = x_187;
goto block_133;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_189 = lean_ctor_get(x_185, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_185, 1);
lean_inc(x_190);
lean_dec(x_185);
x_191 = lean_io_error_to_string(x_189);
x_192 = 3;
x_193 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set_uint8(x_193, sizeof(void*)*1, x_192);
x_194 = lean_array_get_size(x_175);
x_195 = lean_array_push(x_175, x_193);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_35 = x_196;
x_36 = x_190;
goto block_133;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_197 = lean_ctor_get(x_183, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_183, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_199 = x_183;
} else {
 lean_dec_ref(x_183);
 x_199 = lean_box(0);
}
x_200 = lean_io_error_to_string(x_197);
x_201 = 3;
x_202 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set_uint8(x_202, sizeof(void*)*1, x_201);
x_203 = lean_array_get_size(x_175);
x_204 = lean_array_push(x_175, x_202);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
if (lean_is_scalar(x_199)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_199;
 lean_ctor_set_tag(x_206, 0);
}
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_198);
return x_206;
}
}
}
else
{
uint8_t x_207; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_207 = !lean_is_exclusive(x_134);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_208 = lean_ctor_get(x_134, 1);
x_209 = lean_ctor_get(x_134, 0);
lean_dec(x_209);
x_210 = lean_io_error_to_string(x_137);
x_211 = 3;
x_212 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_211);
x_213 = lean_array_get_size(x_208);
x_214 = lean_array_push(x_208, x_212);
x_215 = lean_io_prim_handle_unlock(x_33, x_135);
lean_dec(x_33);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_io_remove_file(x_21, x_216);
lean_dec(x_21);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_217, 0);
lean_dec(x_219);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_214);
lean_ctor_set(x_134, 0, x_213);
lean_ctor_set(x_217, 0, x_134);
return x_217;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_217, 1);
lean_inc(x_220);
lean_dec(x_217);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_214);
lean_ctor_set(x_134, 0, x_213);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_134);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
else
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_217);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_217, 0);
x_224 = lean_io_error_to_string(x_223);
x_225 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set_uint8(x_225, sizeof(void*)*1, x_211);
x_226 = lean_array_push(x_214, x_225);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_226);
lean_ctor_set(x_134, 0, x_213);
lean_ctor_set_tag(x_217, 0);
lean_ctor_set(x_217, 0, x_134);
return x_217;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_227 = lean_ctor_get(x_217, 0);
x_228 = lean_ctor_get(x_217, 1);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_217);
x_229 = lean_io_error_to_string(x_227);
x_230 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_211);
x_231 = lean_array_push(x_214, x_230);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_231);
lean_ctor_set(x_134, 0, x_213);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_134);
lean_ctor_set(x_232, 1, x_228);
return x_232;
}
}
}
else
{
uint8_t x_233; 
lean_dec(x_21);
x_233 = !lean_is_exclusive(x_215);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_234 = lean_ctor_get(x_215, 0);
x_235 = lean_io_error_to_string(x_234);
x_236 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set_uint8(x_236, sizeof(void*)*1, x_211);
x_237 = lean_array_push(x_214, x_236);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_237);
lean_ctor_set(x_134, 0, x_213);
lean_ctor_set_tag(x_215, 0);
lean_ctor_set(x_215, 0, x_134);
return x_215;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_238 = lean_ctor_get(x_215, 0);
x_239 = lean_ctor_get(x_215, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_215);
x_240 = lean_io_error_to_string(x_238);
x_241 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set_uint8(x_241, sizeof(void*)*1, x_211);
x_242 = lean_array_push(x_214, x_241);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_242);
lean_ctor_set(x_134, 0, x_213);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_134);
lean_ctor_set(x_243, 1, x_239);
return x_243;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_134, 1);
lean_inc(x_244);
lean_dec(x_134);
x_245 = lean_io_error_to_string(x_137);
x_246 = 3;
x_247 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set_uint8(x_247, sizeof(void*)*1, x_246);
x_248 = lean_array_get_size(x_244);
x_249 = lean_array_push(x_244, x_247);
x_250 = lean_io_prim_handle_unlock(x_33, x_135);
lean_dec(x_33);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_io_remove_file(x_21, x_251);
lean_dec(x_21);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_254 = x_252;
} else {
 lean_dec_ref(x_252);
 x_254 = lean_box(0);
}
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_248);
lean_ctor_set(x_255, 1, x_249);
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_253);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_257 = lean_ctor_get(x_252, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_252, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_259 = x_252;
} else {
 lean_dec_ref(x_252);
 x_259 = lean_box(0);
}
x_260 = lean_io_error_to_string(x_257);
x_261 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set_uint8(x_261, sizeof(void*)*1, x_246);
x_262 = lean_array_push(x_249, x_261);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_248);
lean_ctor_set(x_263, 1, x_262);
if (lean_is_scalar(x_259)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_259;
 lean_ctor_set_tag(x_264, 0);
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_258);
return x_264;
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_21);
x_265 = lean_ctor_get(x_250, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_250, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_267 = x_250;
} else {
 lean_dec_ref(x_250);
 x_267 = lean_box(0);
}
x_268 = lean_io_error_to_string(x_265);
x_269 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set_uint8(x_269, sizeof(void*)*1, x_246);
x_270 = lean_array_push(x_249, x_269);
x_271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_271, 0, x_248);
lean_ctor_set(x_271, 1, x_270);
if (lean_is_scalar(x_267)) {
 x_272 = lean_alloc_ctor(0, 2, 0);
} else {
 x_272 = x_267;
 lean_ctor_set_tag(x_272, 0);
}
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_266);
return x_272;
}
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_136);
lean_dec(x_21);
x_273 = !lean_is_exclusive(x_134);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_274 = lean_ctor_get(x_134, 1);
x_275 = lean_ctor_get(x_134, 0);
lean_dec(x_275);
x_276 = lean_ctor_get(x_1, 0);
lean_inc(x_276);
x_277 = l_Lake_Env_leanGithash(x_276);
lean_dec(x_276);
x_278 = l_System_Platform_target;
lean_inc(x_34);
x_279 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_279, 0, x_278);
lean_ctor_set(x_279, 1, x_277);
lean_ctor_set(x_279, 2, x_27);
lean_ctor_set(x_279, 3, x_34);
x_280 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_279);
x_281 = lean_unsigned_to_nat(80u);
x_282 = l_Lean_Json_pretty(x_280, x_281);
x_283 = l_IO_FS_Handle_putStrLn(x_33, x_282, x_135);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_283, 1);
lean_inc(x_284);
lean_dec(x_283);
x_285 = lean_io_prim_handle_truncate(x_33, x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
lean_ctor_set(x_134, 0, x_286);
x_35 = x_134;
x_36 = x_287;
goto block_133;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_288 = lean_ctor_get(x_285, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_285, 1);
lean_inc(x_289);
lean_dec(x_285);
x_290 = lean_io_error_to_string(x_288);
x_291 = 3;
x_292 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set_uint8(x_292, sizeof(void*)*1, x_291);
x_293 = lean_array_get_size(x_274);
x_294 = lean_array_push(x_274, x_292);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_294);
lean_ctor_set(x_134, 0, x_293);
x_35 = x_134;
x_36 = x_289;
goto block_133;
}
}
else
{
uint8_t x_295; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_295 = !lean_is_exclusive(x_283);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_296 = lean_ctor_get(x_283, 0);
x_297 = lean_io_error_to_string(x_296);
x_298 = 3;
x_299 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set_uint8(x_299, sizeof(void*)*1, x_298);
x_300 = lean_array_get_size(x_274);
x_301 = lean_array_push(x_274, x_299);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_301);
lean_ctor_set(x_134, 0, x_300);
lean_ctor_set_tag(x_283, 0);
lean_ctor_set(x_283, 0, x_134);
return x_283;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_283, 0);
x_303 = lean_ctor_get(x_283, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_283);
x_304 = lean_io_error_to_string(x_302);
x_305 = 3;
x_306 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set_uint8(x_306, sizeof(void*)*1, x_305);
x_307 = lean_array_get_size(x_274);
x_308 = lean_array_push(x_274, x_306);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_308);
lean_ctor_set(x_134, 0, x_307);
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_134);
lean_ctor_set(x_309, 1, x_303);
return x_309;
}
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_310 = lean_ctor_get(x_134, 1);
lean_inc(x_310);
lean_dec(x_134);
x_311 = lean_ctor_get(x_1, 0);
lean_inc(x_311);
x_312 = l_Lake_Env_leanGithash(x_311);
lean_dec(x_311);
x_313 = l_System_Platform_target;
lean_inc(x_34);
x_314 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_312);
lean_ctor_set(x_314, 2, x_27);
lean_ctor_set(x_314, 3, x_34);
x_315 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_314);
x_316 = lean_unsigned_to_nat(80u);
x_317 = l_Lean_Json_pretty(x_315, x_316);
x_318 = l_IO_FS_Handle_putStrLn(x_33, x_317, x_135);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_io_prim_handle_truncate(x_33, x_319);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_310);
x_35 = x_323;
x_36 = x_322;
goto block_133;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_324 = lean_ctor_get(x_320, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_320, 1);
lean_inc(x_325);
lean_dec(x_320);
x_326 = lean_io_error_to_string(x_324);
x_327 = 3;
x_328 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set_uint8(x_328, sizeof(void*)*1, x_327);
x_329 = lean_array_get_size(x_310);
x_330 = lean_array_push(x_310, x_328);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
x_35 = x_331;
x_36 = x_325;
goto block_133;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_332 = lean_ctor_get(x_318, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_318, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 lean_ctor_release(x_318, 1);
 x_334 = x_318;
} else {
 lean_dec_ref(x_318);
 x_334 = lean_box(0);
}
x_335 = lean_io_error_to_string(x_332);
x_336 = 3;
x_337 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_337, 0, x_335);
lean_ctor_set_uint8(x_337, sizeof(void*)*1, x_336);
x_338 = lean_array_get_size(x_310);
x_339 = lean_array_push(x_310, x_337);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
if (lean_is_scalar(x_334)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_334;
 lean_ctor_set_tag(x_341, 0);
}
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_333);
return x_341;
}
}
}
}
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_407; lean_object* x_408; lean_object* x_508; 
x_350 = lean_ctor_get(x_30, 0);
x_351 = lean_ctor_get(x_30, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_30);
x_352 = lean_ctor_get(x_1, 8);
lean_inc(x_352);
x_508 = lean_io_remove_file(x_18, x_31);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
if (lean_is_scalar(x_12)) {
 x_511 = lean_alloc_ctor(1, 1, 0);
} else {
 x_511 = x_12;
}
lean_ctor_set(x_511, 0, x_509);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_351);
x_407 = x_512;
x_408 = x_510;
goto block_507;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_513 = lean_ctor_get(x_508, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_508, 1);
lean_inc(x_514);
lean_dec(x_508);
if (lean_is_scalar(x_12)) {
 x_515 = lean_alloc_ctor(0, 1, 0);
} else {
 x_515 = x_12;
 lean_ctor_set_tag(x_515, 0);
}
lean_ctor_set(x_515, 0, x_513);
x_516 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_516, 0, x_515);
lean_ctor_set(x_516, 1, x_351);
x_407 = x_516;
x_408 = x_514;
goto block_507;
}
block_406:
{
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_ctor_get(x_1, 9);
lean_inc(x_356);
lean_dec(x_1);
x_357 = l_Lake_elabConfigFile(x_13, x_352, x_356, x_4, x_355, x_354);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_ctor_get(x_358, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_358, 1);
lean_inc(x_361);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_362 = x_358;
} else {
 lean_dec_ref(x_358);
 x_362 = lean_box(0);
}
lean_inc(x_360);
x_363 = lean_write_module(x_360, x_18, x_359);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec(x_363);
x_365 = lean_io_prim_handle_unlock(x_350, x_364);
lean_dec(x_350);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_368 = lean_alloc_ctor(0, 2, 0);
} else {
 x_368 = x_362;
}
lean_ctor_set(x_368, 0, x_360);
lean_ctor_set(x_368, 1, x_361);
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_366);
return x_369;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_360);
x_370 = lean_ctor_get(x_365, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_365, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_372 = x_365;
} else {
 lean_dec_ref(x_365);
 x_372 = lean_box(0);
}
x_373 = lean_io_error_to_string(x_370);
x_374 = 3;
x_375 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_375, 0, x_373);
lean_ctor_set_uint8(x_375, sizeof(void*)*1, x_374);
x_376 = lean_array_get_size(x_361);
x_377 = lean_array_push(x_361, x_375);
if (lean_is_scalar(x_362)) {
 x_378 = lean_alloc_ctor(1, 2, 0);
} else {
 x_378 = x_362;
 lean_ctor_set_tag(x_378, 1);
}
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
if (lean_is_scalar(x_372)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_372;
 lean_ctor_set_tag(x_379, 0);
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_371);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_360);
lean_dec(x_350);
x_380 = lean_ctor_get(x_363, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_363, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_382 = x_363;
} else {
 lean_dec_ref(x_363);
 x_382 = lean_box(0);
}
x_383 = lean_io_error_to_string(x_380);
x_384 = 3;
x_385 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set_uint8(x_385, sizeof(void*)*1, x_384);
x_386 = lean_array_get_size(x_361);
x_387 = lean_array_push(x_361, x_385);
if (lean_is_scalar(x_362)) {
 x_388 = lean_alloc_ctor(1, 2, 0);
} else {
 x_388 = x_362;
 lean_ctor_set_tag(x_388, 1);
}
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
if (lean_is_scalar(x_382)) {
 x_389 = lean_alloc_ctor(0, 2, 0);
} else {
 x_389 = x_382;
 lean_ctor_set_tag(x_389, 0);
}
lean_ctor_set(x_389, 0, x_388);
lean_ctor_set(x_389, 1, x_381);
return x_389;
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_350);
lean_dec(x_18);
x_390 = lean_ctor_get(x_357, 1);
lean_inc(x_390);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_391 = x_357;
} else {
 lean_dec_ref(x_357);
 x_391 = lean_box(0);
}
x_392 = lean_ctor_get(x_358, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_358, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_394 = x_358;
} else {
 lean_dec_ref(x_358);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
if (lean_is_scalar(x_391)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_391;
}
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_390);
return x_396;
}
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_350);
lean_dec(x_18);
x_397 = lean_ctor_get(x_357, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_357, 1);
lean_inc(x_398);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_399 = x_357;
} else {
 lean_dec_ref(x_357);
 x_399 = lean_box(0);
}
if (lean_is_scalar(x_399)) {
 x_400 = lean_alloc_ctor(1, 2, 0);
} else {
 x_400 = x_399;
}
lean_ctor_set(x_400, 0, x_397);
lean_ctor_set(x_400, 1, x_398);
return x_400;
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_401 = lean_ctor_get(x_353, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_353, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_403 = x_353;
} else {
 lean_dec_ref(x_353);
 x_403 = lean_box(0);
}
if (lean_is_scalar(x_403)) {
 x_404 = lean_alloc_ctor(1, 2, 0);
} else {
 x_404 = x_403;
}
lean_ctor_set(x_404, 0, x_401);
lean_ctor_set(x_404, 1, x_402);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_354);
return x_405;
}
}
block_507:
{
lean_object* x_409; 
x_409 = lean_ctor_get(x_407, 0);
lean_inc(x_409);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
lean_dec(x_409);
if (lean_obj_tag(x_410) == 11)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_410);
lean_dec(x_21);
x_411 = lean_ctor_get(x_407, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_412 = x_407;
} else {
 lean_dec_ref(x_407);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_1, 0);
lean_inc(x_413);
x_414 = l_Lake_Env_leanGithash(x_413);
lean_dec(x_413);
x_415 = l_System_Platform_target;
lean_inc(x_352);
x_416 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_414);
lean_ctor_set(x_416, 2, x_27);
lean_ctor_set(x_416, 3, x_352);
x_417 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_416);
x_418 = lean_unsigned_to_nat(80u);
x_419 = l_Lean_Json_pretty(x_417, x_418);
x_420 = l_IO_FS_Handle_putStrLn(x_350, x_419, x_408);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_422 = lean_io_prim_handle_truncate(x_350, x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_422, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_422, 1);
lean_inc(x_424);
lean_dec(x_422);
if (lean_is_scalar(x_412)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_412;
}
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_411);
x_353 = x_425;
x_354 = x_424;
goto block_406;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_426 = lean_ctor_get(x_422, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_422, 1);
lean_inc(x_427);
lean_dec(x_422);
x_428 = lean_io_error_to_string(x_426);
x_429 = 3;
x_430 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_430, 0, x_428);
lean_ctor_set_uint8(x_430, sizeof(void*)*1, x_429);
x_431 = lean_array_get_size(x_411);
x_432 = lean_array_push(x_411, x_430);
if (lean_is_scalar(x_412)) {
 x_433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_433 = x_412;
 lean_ctor_set_tag(x_433, 1);
}
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
x_353 = x_433;
x_354 = x_427;
goto block_406;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_434 = lean_ctor_get(x_420, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_420, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_436 = x_420;
} else {
 lean_dec_ref(x_420);
 x_436 = lean_box(0);
}
x_437 = lean_io_error_to_string(x_434);
x_438 = 3;
x_439 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*1, x_438);
x_440 = lean_array_get_size(x_411);
x_441 = lean_array_push(x_411, x_439);
if (lean_is_scalar(x_412)) {
 x_442 = lean_alloc_ctor(1, 2, 0);
} else {
 x_442 = x_412;
 lean_ctor_set_tag(x_442, 1);
}
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
if (lean_is_scalar(x_436)) {
 x_443 = lean_alloc_ctor(0, 2, 0);
} else {
 x_443 = x_436;
 lean_ctor_set_tag(x_443, 0);
}
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_435);
return x_443;
}
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_352);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_444 = lean_ctor_get(x_407, 1);
lean_inc(x_444);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_445 = x_407;
} else {
 lean_dec_ref(x_407);
 x_445 = lean_box(0);
}
x_446 = lean_io_error_to_string(x_410);
x_447 = 3;
x_448 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_448, 0, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*1, x_447);
x_449 = lean_array_get_size(x_444);
x_450 = lean_array_push(x_444, x_448);
x_451 = lean_io_prim_handle_unlock(x_350, x_408);
lean_dec(x_350);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_453 = lean_io_remove_file(x_21, x_452);
lean_dec(x_21);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_454 = lean_ctor_get(x_453, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_455 = x_453;
} else {
 lean_dec_ref(x_453);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_445)) {
 x_456 = lean_alloc_ctor(1, 2, 0);
} else {
 x_456 = x_445;
 lean_ctor_set_tag(x_456, 1);
}
lean_ctor_set(x_456, 0, x_449);
lean_ctor_set(x_456, 1, x_450);
if (lean_is_scalar(x_455)) {
 x_457 = lean_alloc_ctor(0, 2, 0);
} else {
 x_457 = x_455;
}
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_454);
return x_457;
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_458 = lean_ctor_get(x_453, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_453, 1);
lean_inc(x_459);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_460 = x_453;
} else {
 lean_dec_ref(x_453);
 x_460 = lean_box(0);
}
x_461 = lean_io_error_to_string(x_458);
x_462 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_462, 0, x_461);
lean_ctor_set_uint8(x_462, sizeof(void*)*1, x_447);
x_463 = lean_array_push(x_450, x_462);
if (lean_is_scalar(x_445)) {
 x_464 = lean_alloc_ctor(1, 2, 0);
} else {
 x_464 = x_445;
 lean_ctor_set_tag(x_464, 1);
}
lean_ctor_set(x_464, 0, x_449);
lean_ctor_set(x_464, 1, x_463);
if (lean_is_scalar(x_460)) {
 x_465 = lean_alloc_ctor(0, 2, 0);
} else {
 x_465 = x_460;
 lean_ctor_set_tag(x_465, 0);
}
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_465, 1, x_459);
return x_465;
}
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_21);
x_466 = lean_ctor_get(x_451, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_451, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_468 = x_451;
} else {
 lean_dec_ref(x_451);
 x_468 = lean_box(0);
}
x_469 = lean_io_error_to_string(x_466);
x_470 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set_uint8(x_470, sizeof(void*)*1, x_447);
x_471 = lean_array_push(x_450, x_470);
if (lean_is_scalar(x_445)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_445;
 lean_ctor_set_tag(x_472, 1);
}
lean_ctor_set(x_472, 0, x_449);
lean_ctor_set(x_472, 1, x_471);
if (lean_is_scalar(x_468)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_468;
 lean_ctor_set_tag(x_473, 0);
}
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_467);
return x_473;
}
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_409);
lean_dec(x_21);
x_474 = lean_ctor_get(x_407, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_475 = x_407;
} else {
 lean_dec_ref(x_407);
 x_475 = lean_box(0);
}
x_476 = lean_ctor_get(x_1, 0);
lean_inc(x_476);
x_477 = l_Lake_Env_leanGithash(x_476);
lean_dec(x_476);
x_478 = l_System_Platform_target;
lean_inc(x_352);
x_479 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_479, 0, x_478);
lean_ctor_set(x_479, 1, x_477);
lean_ctor_set(x_479, 2, x_27);
lean_ctor_set(x_479, 3, x_352);
x_480 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_479);
x_481 = lean_unsigned_to_nat(80u);
x_482 = l_Lean_Json_pretty(x_480, x_481);
x_483 = l_IO_FS_Handle_putStrLn(x_350, x_482, x_408);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; 
x_484 = lean_ctor_get(x_483, 1);
lean_inc(x_484);
lean_dec(x_483);
x_485 = lean_io_prim_handle_truncate(x_350, x_484);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
if (lean_is_scalar(x_475)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_475;
}
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_474);
x_353 = x_488;
x_354 = x_487;
goto block_406;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; uint8_t x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_489 = lean_ctor_get(x_485, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_485, 1);
lean_inc(x_490);
lean_dec(x_485);
x_491 = lean_io_error_to_string(x_489);
x_492 = 3;
x_493 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set_uint8(x_493, sizeof(void*)*1, x_492);
x_494 = lean_array_get_size(x_474);
x_495 = lean_array_push(x_474, x_493);
if (lean_is_scalar(x_475)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_475;
 lean_ctor_set_tag(x_496, 1);
}
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
x_353 = x_496;
x_354 = x_490;
goto block_406;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_352);
lean_dec(x_350);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_497 = lean_ctor_get(x_483, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_483, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_483)) {
 lean_ctor_release(x_483, 0);
 lean_ctor_release(x_483, 1);
 x_499 = x_483;
} else {
 lean_dec_ref(x_483);
 x_499 = lean_box(0);
}
x_500 = lean_io_error_to_string(x_497);
x_501 = 3;
x_502 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_502, 0, x_500);
lean_ctor_set_uint8(x_502, sizeof(void*)*1, x_501);
x_503 = lean_array_get_size(x_474);
x_504 = lean_array_push(x_474, x_502);
if (lean_is_scalar(x_475)) {
 x_505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_505 = x_475;
 lean_ctor_set_tag(x_505, 1);
}
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
if (lean_is_scalar(x_499)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_499;
 lean_ctor_set_tag(x_506, 0);
}
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_498);
return x_506;
}
}
}
}
}
else
{
uint8_t x_517; 
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_517 = !lean_is_exclusive(x_30);
if (x_517 == 0)
{
lean_object* x_518; 
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_30);
lean_ctor_set(x_518, 1, x_31);
return x_518;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_519 = lean_ctor_get(x_30, 0);
x_520 = lean_ctor_get(x_30, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_30);
x_521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_521);
lean_ctor_set(x_522, 1, x_31);
return x_522;
}
}
}
block_1265:
{
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; uint8_t x_1166; 
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
x_1166 = lean_ctor_get_uint8(x_1, sizeof(void*)*12);
if (x_1166 == 0)
{
uint8_t x_1167; lean_object* x_1168; 
lean_dec(x_12);
x_1167 = 0;
x_1168 = lean_io_prim_handle_lock(x_526, x_1167, x_525);
if (lean_obj_tag(x_1168) == 0)
{
lean_object* x_1169; lean_object* x_1170; 
x_1169 = lean_ctor_get(x_1168, 1);
lean_inc(x_1169);
lean_dec(x_1168);
x_1170 = l_IO_FS_Handle_readToEnd(x_526, x_1169);
if (lean_obj_tag(x_1170) == 0)
{
uint8_t x_1171; 
x_1171 = !lean_is_exclusive(x_1170);
if (x_1171 == 0)
{
lean_object* x_1172; 
x_1172 = lean_ctor_get(x_1170, 1);
lean_ctor_set(x_1170, 1, x_527);
x_529 = x_1170;
x_530 = x_1172;
goto block_1165;
}
else
{
lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1173 = lean_ctor_get(x_1170, 0);
x_1174 = lean_ctor_get(x_1170, 1);
lean_inc(x_1174);
lean_inc(x_1173);
lean_dec(x_1170);
x_1175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1175, 0, x_1173);
lean_ctor_set(x_1175, 1, x_527);
x_529 = x_1175;
x_530 = x_1174;
goto block_1165;
}
}
else
{
uint8_t x_1176; 
x_1176 = !lean_is_exclusive(x_1170);
if (x_1176 == 0)
{
lean_object* x_1177; lean_object* x_1178; lean_object* x_1179; uint8_t x_1180; lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; 
x_1177 = lean_ctor_get(x_1170, 0);
x_1178 = lean_ctor_get(x_1170, 1);
x_1179 = lean_io_error_to_string(x_1177);
x_1180 = 3;
x_1181 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1181, 0, x_1179);
lean_ctor_set_uint8(x_1181, sizeof(void*)*1, x_1180);
x_1182 = lean_array_get_size(x_527);
x_1183 = lean_array_push(x_527, x_1181);
lean_ctor_set(x_1170, 1, x_1183);
lean_ctor_set(x_1170, 0, x_1182);
x_529 = x_1170;
x_530 = x_1178;
goto block_1165;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; uint8_t x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1184 = lean_ctor_get(x_1170, 0);
x_1185 = lean_ctor_get(x_1170, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1170);
x_1186 = lean_io_error_to_string(x_1184);
x_1187 = 3;
x_1188 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1188, 0, x_1186);
lean_ctor_set_uint8(x_1188, sizeof(void*)*1, x_1187);
x_1189 = lean_array_get_size(x_527);
x_1190 = lean_array_push(x_527, x_1188);
x_1191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1191, 0, x_1189);
lean_ctor_set(x_1191, 1, x_1190);
x_529 = x_1191;
x_530 = x_1185;
goto block_1165;
}
}
}
else
{
uint8_t x_1192; 
lean_dec(x_528);
lean_dec(x_526);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1192 = !lean_is_exclusive(x_1168);
if (x_1192 == 0)
{
lean_object* x_1193; lean_object* x_1194; uint8_t x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1193 = lean_ctor_get(x_1168, 0);
x_1194 = lean_io_error_to_string(x_1193);
x_1195 = 3;
x_1196 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1196, 0, x_1194);
lean_ctor_set_uint8(x_1196, sizeof(void*)*1, x_1195);
x_1197 = lean_array_get_size(x_527);
x_1198 = lean_array_push(x_527, x_1196);
x_1199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1199, 0, x_1197);
lean_ctor_set(x_1199, 1, x_1198);
lean_ctor_set_tag(x_1168, 0);
lean_ctor_set(x_1168, 0, x_1199);
return x_1168;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; uint8_t x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
x_1200 = lean_ctor_get(x_1168, 0);
x_1201 = lean_ctor_get(x_1168, 1);
lean_inc(x_1201);
lean_inc(x_1200);
lean_dec(x_1168);
x_1202 = lean_io_error_to_string(x_1200);
x_1203 = 3;
x_1204 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1204, 0, x_1202);
lean_ctor_set_uint8(x_1204, sizeof(void*)*1, x_1203);
x_1205 = lean_array_get_size(x_527);
x_1206 = lean_array_push(x_527, x_1204);
x_1207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1207, 0, x_1205);
lean_ctor_set(x_1207, 1, x_1206);
x_1208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1208, 0, x_1207);
lean_ctor_set(x_1208, 1, x_1201);
return x_1208;
}
}
}
else
{
lean_object* x_1209; lean_object* x_1210; uint8_t x_1218; lean_object* x_1219; 
lean_dec(x_528);
lean_dec(x_29);
x_1218 = 1;
x_1219 = lean_io_prim_handle_mk(x_24, x_1218, x_525);
lean_dec(x_24);
if (lean_obj_tag(x_1219) == 0)
{
lean_object* x_1220; lean_object* x_1221; uint8_t x_1222; lean_object* x_1223; 
x_1220 = lean_ctor_get(x_1219, 0);
lean_inc(x_1220);
x_1221 = lean_ctor_get(x_1219, 1);
lean_inc(x_1221);
lean_dec(x_1219);
x_1222 = 1;
x_1223 = lean_io_prim_handle_try_lock(x_1220, x_1222, x_1221);
if (lean_obj_tag(x_1223) == 0)
{
lean_object* x_1224; uint8_t x_1225; 
x_1224 = lean_ctor_get(x_1223, 0);
lean_inc(x_1224);
x_1225 = lean_unbox(x_1224);
lean_dec(x_1224);
if (x_1225 == 0)
{
lean_object* x_1226; lean_object* x_1227; 
lean_dec(x_1220);
x_1226 = lean_ctor_get(x_1223, 1);
lean_inc(x_1226);
lean_dec(x_1223);
x_1227 = lean_io_prim_handle_unlock(x_526, x_1226);
lean_dec(x_526);
if (lean_obj_tag(x_1227) == 0)
{
lean_object* x_1228; lean_object* x_1229; 
x_1228 = lean_ctor_get(x_1227, 1);
lean_inc(x_1228);
lean_dec(x_1227);
x_1229 = l_Lake_importConfigFile___closed__12;
x_1209 = x_1229;
x_1210 = x_1228;
goto block_1217;
}
else
{
lean_object* x_1230; lean_object* x_1231; 
x_1230 = lean_ctor_get(x_1227, 0);
lean_inc(x_1230);
x_1231 = lean_ctor_get(x_1227, 1);
lean_inc(x_1231);
lean_dec(x_1227);
x_1209 = x_1230;
x_1210 = x_1231;
goto block_1217;
}
}
else
{
lean_object* x_1232; lean_object* x_1233; 
x_1232 = lean_ctor_get(x_1223, 1);
lean_inc(x_1232);
lean_dec(x_1223);
x_1233 = lean_io_prim_handle_unlock(x_526, x_1232);
lean_dec(x_526);
if (lean_obj_tag(x_1233) == 0)
{
lean_object* x_1234; uint8_t x_1235; lean_object* x_1236; 
x_1234 = lean_ctor_get(x_1233, 1);
lean_inc(x_1234);
lean_dec(x_1233);
x_1235 = 3;
x_1236 = lean_io_prim_handle_mk(x_21, x_1235, x_1234);
if (lean_obj_tag(x_1236) == 0)
{
lean_object* x_1237; lean_object* x_1238; lean_object* x_1239; 
x_1237 = lean_ctor_get(x_1236, 0);
lean_inc(x_1237);
x_1238 = lean_ctor_get(x_1236, 1);
lean_inc(x_1238);
lean_dec(x_1236);
x_1239 = lean_io_prim_handle_lock(x_1237, x_1222, x_1238);
if (lean_obj_tag(x_1239) == 0)
{
lean_object* x_1240; lean_object* x_1241; 
x_1240 = lean_ctor_get(x_1239, 1);
lean_inc(x_1240);
lean_dec(x_1239);
x_1241 = lean_io_prim_handle_unlock(x_1220, x_1240);
lean_dec(x_1220);
if (lean_obj_tag(x_1241) == 0)
{
uint8_t x_1242; 
x_1242 = !lean_is_exclusive(x_1241);
if (x_1242 == 0)
{
lean_object* x_1243; lean_object* x_1244; 
x_1243 = lean_ctor_get(x_1241, 1);
x_1244 = lean_ctor_get(x_1241, 0);
lean_dec(x_1244);
lean_ctor_set(x_1241, 1, x_527);
lean_ctor_set(x_1241, 0, x_1237);
x_30 = x_1241;
x_31 = x_1243;
goto block_523;
}
else
{
lean_object* x_1245; lean_object* x_1246; 
x_1245 = lean_ctor_get(x_1241, 1);
lean_inc(x_1245);
lean_dec(x_1241);
x_1246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1246, 0, x_1237);
lean_ctor_set(x_1246, 1, x_527);
x_30 = x_1246;
x_31 = x_1245;
goto block_523;
}
}
else
{
lean_object* x_1247; lean_object* x_1248; 
lean_dec(x_1237);
x_1247 = lean_ctor_get(x_1241, 0);
lean_inc(x_1247);
x_1248 = lean_ctor_get(x_1241, 1);
lean_inc(x_1248);
lean_dec(x_1241);
x_1209 = x_1247;
x_1210 = x_1248;
goto block_1217;
}
}
else
{
lean_object* x_1249; lean_object* x_1250; 
lean_dec(x_1237);
lean_dec(x_1220);
x_1249 = lean_ctor_get(x_1239, 0);
lean_inc(x_1249);
x_1250 = lean_ctor_get(x_1239, 1);
lean_inc(x_1250);
lean_dec(x_1239);
x_1209 = x_1249;
x_1210 = x_1250;
goto block_1217;
}
}
else
{
lean_object* x_1251; lean_object* x_1252; 
lean_dec(x_1220);
x_1251 = lean_ctor_get(x_1236, 0);
lean_inc(x_1251);
x_1252 = lean_ctor_get(x_1236, 1);
lean_inc(x_1252);
lean_dec(x_1236);
x_1209 = x_1251;
x_1210 = x_1252;
goto block_1217;
}
}
else
{
lean_object* x_1253; lean_object* x_1254; 
lean_dec(x_1220);
x_1253 = lean_ctor_get(x_1233, 0);
lean_inc(x_1253);
x_1254 = lean_ctor_get(x_1233, 1);
lean_inc(x_1254);
lean_dec(x_1233);
x_1209 = x_1253;
x_1210 = x_1254;
goto block_1217;
}
}
}
else
{
lean_object* x_1255; lean_object* x_1256; 
lean_dec(x_1220);
lean_dec(x_526);
x_1255 = lean_ctor_get(x_1223, 0);
lean_inc(x_1255);
x_1256 = lean_ctor_get(x_1223, 1);
lean_inc(x_1256);
lean_dec(x_1223);
x_1209 = x_1255;
x_1210 = x_1256;
goto block_1217;
}
}
else
{
lean_object* x_1257; lean_object* x_1258; 
lean_dec(x_526);
x_1257 = lean_ctor_get(x_1219, 0);
lean_inc(x_1257);
x_1258 = lean_ctor_get(x_1219, 1);
lean_inc(x_1258);
lean_dec(x_1219);
x_1209 = x_1257;
x_1210 = x_1258;
goto block_1217;
}
block_1217:
{
lean_object* x_1211; uint8_t x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; 
x_1211 = lean_io_error_to_string(x_1209);
x_1212 = 3;
x_1213 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1213, 0, x_1211);
lean_ctor_set_uint8(x_1213, sizeof(void*)*1, x_1212);
x_1214 = lean_array_get_size(x_527);
x_1215 = lean_array_push(x_527, x_1213);
x_1216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1216, 0, x_1214);
lean_ctor_set(x_1216, 1, x_1215);
x_30 = x_1216;
x_31 = x_1210;
goto block_523;
}
}
block_1165:
{
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_531 = lean_ctor_get(x_529, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_529, 1);
lean_inc(x_532);
if (lean_is_exclusive(x_529)) {
 lean_ctor_release(x_529, 0);
 lean_ctor_release(x_529, 1);
 x_533 = x_529;
} else {
 lean_dec_ref(x_529);
 x_533 = lean_box(0);
}
x_534 = l_Lake_importConfigFile___closed__6;
x_535 = l_Std_Internal_Parsec_String_Parser_run___rarg(x_534, x_531);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_535);
lean_dec(x_528);
lean_dec(x_526);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_536 = lean_array_get_size(x_532);
x_537 = l_Lake_importConfigFile___closed__8;
x_538 = lean_array_push(x_532, x_537);
if (lean_is_scalar(x_533)) {
 x_539 = lean_alloc_ctor(1, 2, 0);
} else {
 x_539 = x_533;
 lean_ctor_set_tag(x_539, 1);
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_538);
x_540 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_540, 0, x_539);
lean_ctor_set(x_540, 1, x_530);
return x_540;
}
else
{
lean_object* x_541; lean_object* x_542; 
x_541 = lean_ctor_get(x_535, 0);
lean_inc(x_541);
lean_dec(x_535);
x_542 = l___private_Lake_Load_Lean_Elab_0__Lake_fromJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_950_(x_541);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_542);
lean_dec(x_528);
lean_dec(x_526);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_543 = lean_array_get_size(x_532);
x_544 = l_Lake_importConfigFile___closed__8;
x_545 = lean_array_push(x_532, x_544);
if (lean_is_scalar(x_533)) {
 x_546 = lean_alloc_ctor(1, 2, 0);
} else {
 x_546 = x_533;
 lean_ctor_set_tag(x_546, 1);
}
lean_ctor_set(x_546, 0, x_543);
lean_ctor_set(x_546, 1, x_545);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_530);
return x_547;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; uint8_t x_1098; 
x_548 = lean_ctor_get(x_542, 0);
lean_inc(x_548);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 x_549 = x_542;
} else {
 lean_dec_ref(x_542);
 x_549 = lean_box(0);
}
x_1046 = l_System_FilePath_pathExists(x_18, x_530);
x_1047 = lean_ctor_get(x_1046, 0);
lean_inc(x_1047);
x_1048 = lean_ctor_get(x_1046, 1);
lean_inc(x_1048);
lean_dec(x_1046);
x_1098 = lean_unbox(x_1047);
lean_dec(x_1047);
if (x_1098 == 0)
{
lean_object* x_1099; 
lean_dec(x_29);
x_1099 = lean_box(0);
x_1049 = x_1099;
goto block_1097;
}
else
{
lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; uint8_t x_1104; 
x_1100 = lean_ctor_get(x_548, 0);
lean_inc(x_1100);
x_1101 = lean_ctor_get(x_548, 1);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_548, 2);
lean_inc(x_1102);
x_1103 = l_System_Platform_target;
x_1104 = lean_string_dec_eq(x_1100, x_1103);
lean_dec(x_1100);
if (x_1104 == 0)
{
lean_object* x_1105; 
lean_dec(x_1102);
lean_dec(x_1101);
lean_dec(x_29);
x_1105 = lean_box(0);
x_1049 = x_1105;
goto block_1097;
}
else
{
lean_object* x_1106; lean_object* x_1107; uint8_t x_1108; 
x_1106 = lean_ctor_get(x_1, 0);
lean_inc(x_1106);
x_1107 = l_Lake_Env_leanGithash(x_1106);
lean_dec(x_1106);
x_1108 = lean_string_dec_eq(x_1101, x_1107);
lean_dec(x_1107);
lean_dec(x_1101);
if (x_1108 == 0)
{
lean_object* x_1109; 
lean_dec(x_1102);
lean_dec(x_29);
x_1109 = lean_box(0);
x_1049 = x_1109;
goto block_1097;
}
else
{
uint64_t x_1110; uint64_t x_1111; uint8_t x_1112; 
x_1110 = lean_unbox_uint64(x_1102);
lean_dec(x_1102);
x_1111 = lean_unbox_uint64(x_27);
x_1112 = lean_uint64_dec_eq(x_1110, x_1111);
if (x_1112 == 0)
{
lean_object* x_1113; 
lean_dec(x_29);
x_1113 = lean_box(0);
x_1049 = x_1113;
goto block_1097;
}
else
{
lean_object* x_1114; lean_object* x_1115; 
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_533);
lean_dec(x_528);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_4);
x_1114 = lean_ctor_get(x_1, 9);
lean_inc(x_1114);
lean_dec(x_1);
x_1115 = l_Lake_importConfigFileCore(x_18, x_1114, x_1048);
lean_dec(x_18);
if (lean_obj_tag(x_1115) == 0)
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1116 = lean_ctor_get(x_1115, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1115, 1);
lean_inc(x_1117);
lean_dec(x_1115);
x_1118 = lean_io_prim_handle_unlock(x_526, x_1117);
lean_dec(x_526);
if (lean_obj_tag(x_1118) == 0)
{
uint8_t x_1119; 
x_1119 = !lean_is_exclusive(x_1118);
if (x_1119 == 0)
{
lean_object* x_1120; lean_object* x_1121; 
x_1120 = lean_ctor_get(x_1118, 0);
lean_dec(x_1120);
if (lean_is_scalar(x_29)) {
 x_1121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1121 = x_29;
}
lean_ctor_set(x_1121, 0, x_1116);
lean_ctor_set(x_1121, 1, x_532);
lean_ctor_set(x_1118, 0, x_1121);
return x_1118;
}
else
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1122 = lean_ctor_get(x_1118, 1);
lean_inc(x_1122);
lean_dec(x_1118);
if (lean_is_scalar(x_29)) {
 x_1123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1123 = x_29;
}
lean_ctor_set(x_1123, 0, x_1116);
lean_ctor_set(x_1123, 1, x_532);
x_1124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1124, 0, x_1123);
lean_ctor_set(x_1124, 1, x_1122);
return x_1124;
}
}
else
{
uint8_t x_1125; 
lean_dec(x_1116);
x_1125 = !lean_is_exclusive(x_1118);
if (x_1125 == 0)
{
lean_object* x_1126; lean_object* x_1127; uint8_t x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1126 = lean_ctor_get(x_1118, 0);
x_1127 = lean_io_error_to_string(x_1126);
x_1128 = 3;
x_1129 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1129, 0, x_1127);
lean_ctor_set_uint8(x_1129, sizeof(void*)*1, x_1128);
x_1130 = lean_array_get_size(x_532);
x_1131 = lean_array_push(x_532, x_1129);
if (lean_is_scalar(x_29)) {
 x_1132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1132 = x_29;
 lean_ctor_set_tag(x_1132, 1);
}
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set(x_1132, 1, x_1131);
lean_ctor_set_tag(x_1118, 0);
lean_ctor_set(x_1118, 0, x_1132);
return x_1118;
}
else
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; uint8_t x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; 
x_1133 = lean_ctor_get(x_1118, 0);
x_1134 = lean_ctor_get(x_1118, 1);
lean_inc(x_1134);
lean_inc(x_1133);
lean_dec(x_1118);
x_1135 = lean_io_error_to_string(x_1133);
x_1136 = 3;
x_1137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1137, 0, x_1135);
lean_ctor_set_uint8(x_1137, sizeof(void*)*1, x_1136);
x_1138 = lean_array_get_size(x_532);
x_1139 = lean_array_push(x_532, x_1137);
if (lean_is_scalar(x_29)) {
 x_1140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1140 = x_29;
 lean_ctor_set_tag(x_1140, 1);
}
lean_ctor_set(x_1140, 0, x_1138);
lean_ctor_set(x_1140, 1, x_1139);
x_1141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1141, 0, x_1140);
lean_ctor_set(x_1141, 1, x_1134);
return x_1141;
}
}
}
else
{
uint8_t x_1142; 
lean_dec(x_526);
x_1142 = !lean_is_exclusive(x_1115);
if (x_1142 == 0)
{
lean_object* x_1143; lean_object* x_1144; uint8_t x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; 
x_1143 = lean_ctor_get(x_1115, 0);
x_1144 = lean_io_error_to_string(x_1143);
x_1145 = 3;
x_1146 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1146, 0, x_1144);
lean_ctor_set_uint8(x_1146, sizeof(void*)*1, x_1145);
x_1147 = lean_array_get_size(x_532);
x_1148 = lean_array_push(x_532, x_1146);
if (lean_is_scalar(x_29)) {
 x_1149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1149 = x_29;
 lean_ctor_set_tag(x_1149, 1);
}
lean_ctor_set(x_1149, 0, x_1147);
lean_ctor_set(x_1149, 1, x_1148);
lean_ctor_set_tag(x_1115, 0);
lean_ctor_set(x_1115, 0, x_1149);
return x_1115;
}
else
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; uint8_t x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
x_1150 = lean_ctor_get(x_1115, 0);
x_1151 = lean_ctor_get(x_1115, 1);
lean_inc(x_1151);
lean_inc(x_1150);
lean_dec(x_1115);
x_1152 = lean_io_error_to_string(x_1150);
x_1153 = 3;
x_1154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1154, 0, x_1152);
lean_ctor_set_uint8(x_1154, sizeof(void*)*1, x_1153);
x_1155 = lean_array_get_size(x_532);
x_1156 = lean_array_push(x_532, x_1154);
if (lean_is_scalar(x_29)) {
 x_1157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1157 = x_29;
 lean_ctor_set_tag(x_1157, 1);
}
lean_ctor_set(x_1157, 0, x_1155);
lean_ctor_set(x_1157, 1, x_1156);
x_1158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1158, 0, x_1157);
lean_ctor_set(x_1158, 1, x_1151);
return x_1158;
}
}
}
}
}
}
block_1045:
{
if (lean_obj_tag(x_550) == 0)
{
uint8_t x_552; 
x_552 = !lean_is_exclusive(x_550);
if (x_552 == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_655; lean_object* x_656; lean_object* x_864; 
x_553 = lean_ctor_get(x_550, 0);
x_554 = lean_ctor_get(x_548, 3);
lean_inc(x_554);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 lean_ctor_release(x_548, 2);
 lean_ctor_release(x_548, 3);
 x_555 = x_548;
} else {
 lean_dec_ref(x_548);
 x_555 = lean_box(0);
}
x_864 = lean_io_remove_file(x_18, x_551);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
lean_dec(x_864);
if (lean_is_scalar(x_549)) {
 x_867 = lean_alloc_ctor(1, 1, 0);
} else {
 x_867 = x_549;
}
lean_ctor_set(x_867, 0, x_865);
lean_ctor_set(x_550, 0, x_867);
x_655 = x_550;
x_656 = x_866;
goto block_863;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_864, 0);
lean_inc(x_868);
x_869 = lean_ctor_get(x_864, 1);
lean_inc(x_869);
lean_dec(x_864);
if (lean_is_scalar(x_549)) {
 x_870 = lean_alloc_ctor(0, 1, 0);
} else {
 x_870 = x_549;
 lean_ctor_set_tag(x_870, 0);
}
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_550, 0, x_870);
x_655 = x_550;
x_656 = x_869;
goto block_863;
}
block_654:
{
if (lean_obj_tag(x_556) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_558 = lean_ctor_get(x_556, 1);
lean_inc(x_558);
lean_dec(x_556);
x_559 = lean_ctor_get(x_1, 9);
lean_inc(x_559);
lean_dec(x_1);
x_560 = l_Lake_elabConfigFile(x_13, x_554, x_559, x_4, x_558, x_557);
if (lean_obj_tag(x_560) == 0)
{
lean_object* x_561; 
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; uint8_t x_563; 
x_562 = lean_ctor_get(x_560, 1);
lean_inc(x_562);
lean_dec(x_560);
x_563 = !lean_is_exclusive(x_561);
if (x_563 == 0)
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_561, 0);
x_565 = lean_ctor_get(x_561, 1);
lean_inc(x_564);
x_566 = lean_write_module(x_564, x_18, x_562);
if (lean_obj_tag(x_566) == 0)
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_566, 1);
lean_inc(x_567);
lean_dec(x_566);
x_568 = lean_io_prim_handle_unlock(x_553, x_567);
lean_dec(x_553);
if (lean_obj_tag(x_568) == 0)
{
uint8_t x_569; 
x_569 = !lean_is_exclusive(x_568);
if (x_569 == 0)
{
lean_object* x_570; 
x_570 = lean_ctor_get(x_568, 0);
lean_dec(x_570);
lean_ctor_set(x_568, 0, x_561);
return x_568;
}
else
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_ctor_get(x_568, 1);
lean_inc(x_571);
lean_dec(x_568);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_561);
lean_ctor_set(x_572, 1, x_571);
return x_572;
}
}
else
{
uint8_t x_573; 
lean_dec(x_564);
x_573 = !lean_is_exclusive(x_568);
if (x_573 == 0)
{
lean_object* x_574; lean_object* x_575; uint8_t x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_574 = lean_ctor_get(x_568, 0);
x_575 = lean_io_error_to_string(x_574);
x_576 = 3;
x_577 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_577, 0, x_575);
lean_ctor_set_uint8(x_577, sizeof(void*)*1, x_576);
x_578 = lean_array_get_size(x_565);
x_579 = lean_array_push(x_565, x_577);
lean_ctor_set_tag(x_561, 1);
lean_ctor_set(x_561, 1, x_579);
lean_ctor_set(x_561, 0, x_578);
lean_ctor_set_tag(x_568, 0);
lean_ctor_set(x_568, 0, x_561);
return x_568;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; uint8_t x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_580 = lean_ctor_get(x_568, 0);
x_581 = lean_ctor_get(x_568, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_568);
x_582 = lean_io_error_to_string(x_580);
x_583 = 3;
x_584 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set_uint8(x_584, sizeof(void*)*1, x_583);
x_585 = lean_array_get_size(x_565);
x_586 = lean_array_push(x_565, x_584);
lean_ctor_set_tag(x_561, 1);
lean_ctor_set(x_561, 1, x_586);
lean_ctor_set(x_561, 0, x_585);
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_561);
lean_ctor_set(x_587, 1, x_581);
return x_587;
}
}
}
else
{
uint8_t x_588; 
lean_dec(x_564);
lean_dec(x_553);
x_588 = !lean_is_exclusive(x_566);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; uint8_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_589 = lean_ctor_get(x_566, 0);
x_590 = lean_io_error_to_string(x_589);
x_591 = 3;
x_592 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set_uint8(x_592, sizeof(void*)*1, x_591);
x_593 = lean_array_get_size(x_565);
x_594 = lean_array_push(x_565, x_592);
lean_ctor_set_tag(x_561, 1);
lean_ctor_set(x_561, 1, x_594);
lean_ctor_set(x_561, 0, x_593);
lean_ctor_set_tag(x_566, 0);
lean_ctor_set(x_566, 0, x_561);
return x_566;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_595 = lean_ctor_get(x_566, 0);
x_596 = lean_ctor_get(x_566, 1);
lean_inc(x_596);
lean_inc(x_595);
lean_dec(x_566);
x_597 = lean_io_error_to_string(x_595);
x_598 = 3;
x_599 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set_uint8(x_599, sizeof(void*)*1, x_598);
x_600 = lean_array_get_size(x_565);
x_601 = lean_array_push(x_565, x_599);
lean_ctor_set_tag(x_561, 1);
lean_ctor_set(x_561, 1, x_601);
lean_ctor_set(x_561, 0, x_600);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_561);
lean_ctor_set(x_602, 1, x_596);
return x_602;
}
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_603 = lean_ctor_get(x_561, 0);
x_604 = lean_ctor_get(x_561, 1);
lean_inc(x_604);
lean_inc(x_603);
lean_dec(x_561);
lean_inc(x_603);
x_605 = lean_write_module(x_603, x_18, x_562);
if (lean_obj_tag(x_605) == 0)
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_ctor_get(x_605, 1);
lean_inc(x_606);
lean_dec(x_605);
x_607 = lean_io_prim_handle_unlock(x_553, x_606);
lean_dec(x_553);
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_608 = lean_ctor_get(x_607, 1);
lean_inc(x_608);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_609 = x_607;
} else {
 lean_dec_ref(x_607);
 x_609 = lean_box(0);
}
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_603);
lean_ctor_set(x_610, 1, x_604);
if (lean_is_scalar(x_609)) {
 x_611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_611 = x_609;
}
lean_ctor_set(x_611, 0, x_610);
lean_ctor_set(x_611, 1, x_608);
return x_611;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_603);
x_612 = lean_ctor_get(x_607, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_607, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_607)) {
 lean_ctor_release(x_607, 0);
 lean_ctor_release(x_607, 1);
 x_614 = x_607;
} else {
 lean_dec_ref(x_607);
 x_614 = lean_box(0);
}
x_615 = lean_io_error_to_string(x_612);
x_616 = 3;
x_617 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set_uint8(x_617, sizeof(void*)*1, x_616);
x_618 = lean_array_get_size(x_604);
x_619 = lean_array_push(x_604, x_617);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
if (lean_is_scalar(x_614)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_614;
 lean_ctor_set_tag(x_621, 0);
}
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_613);
return x_621;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_603);
lean_dec(x_553);
x_622 = lean_ctor_get(x_605, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_605, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_605)) {
 lean_ctor_release(x_605, 0);
 lean_ctor_release(x_605, 1);
 x_624 = x_605;
} else {
 lean_dec_ref(x_605);
 x_624 = lean_box(0);
}
x_625 = lean_io_error_to_string(x_622);
x_626 = 3;
x_627 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_627, 0, x_625);
lean_ctor_set_uint8(x_627, sizeof(void*)*1, x_626);
x_628 = lean_array_get_size(x_604);
x_629 = lean_array_push(x_604, x_627);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
if (lean_is_scalar(x_624)) {
 x_631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_631 = x_624;
 lean_ctor_set_tag(x_631, 0);
}
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_623);
return x_631;
}
}
}
else
{
uint8_t x_632; 
lean_dec(x_553);
lean_dec(x_18);
x_632 = !lean_is_exclusive(x_560);
if (x_632 == 0)
{
lean_object* x_633; uint8_t x_634; 
x_633 = lean_ctor_get(x_560, 0);
lean_dec(x_633);
x_634 = !lean_is_exclusive(x_561);
if (x_634 == 0)
{
return x_560;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_635 = lean_ctor_get(x_561, 0);
x_636 = lean_ctor_get(x_561, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_561);
x_637 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_637, 0, x_635);
lean_ctor_set(x_637, 1, x_636);
lean_ctor_set(x_560, 0, x_637);
return x_560;
}
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_638 = lean_ctor_get(x_560, 1);
lean_inc(x_638);
lean_dec(x_560);
x_639 = lean_ctor_get(x_561, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_561, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_561)) {
 lean_ctor_release(x_561, 0);
 lean_ctor_release(x_561, 1);
 x_641 = x_561;
} else {
 lean_dec_ref(x_561);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(1, 2, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_640);
x_643 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_638);
return x_643;
}
}
}
else
{
uint8_t x_644; 
lean_dec(x_553);
lean_dec(x_18);
x_644 = !lean_is_exclusive(x_560);
if (x_644 == 0)
{
return x_560;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_645 = lean_ctor_get(x_560, 0);
x_646 = lean_ctor_get(x_560, 1);
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_560);
x_647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_647, 0, x_645);
lean_ctor_set(x_647, 1, x_646);
return x_647;
}
}
}
else
{
uint8_t x_648; 
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_648 = !lean_is_exclusive(x_556);
if (x_648 == 0)
{
lean_object* x_649; 
x_649 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_649, 0, x_556);
lean_ctor_set(x_649, 1, x_557);
return x_649;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_650 = lean_ctor_get(x_556, 0);
x_651 = lean_ctor_get(x_556, 1);
lean_inc(x_651);
lean_inc(x_650);
lean_dec(x_556);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_650);
lean_ctor_set(x_652, 1, x_651);
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_557);
return x_653;
}
}
}
block_863:
{
lean_object* x_657; 
x_657 = lean_ctor_get(x_655, 0);
lean_inc(x_657);
if (lean_obj_tag(x_657) == 0)
{
lean_object* x_658; 
x_658 = lean_ctor_get(x_657, 0);
lean_inc(x_658);
lean_dec(x_657);
if (lean_obj_tag(x_658) == 11)
{
uint8_t x_659; 
lean_dec(x_658);
lean_dec(x_21);
x_659 = !lean_is_exclusive(x_655);
if (x_659 == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_660 = lean_ctor_get(x_655, 1);
x_661 = lean_ctor_get(x_655, 0);
lean_dec(x_661);
x_662 = lean_ctor_get(x_1, 0);
lean_inc(x_662);
x_663 = l_Lake_Env_leanGithash(x_662);
lean_dec(x_662);
x_664 = l_System_Platform_target;
lean_inc(x_554);
if (lean_is_scalar(x_555)) {
 x_665 = lean_alloc_ctor(0, 4, 0);
} else {
 x_665 = x_555;
}
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_663);
lean_ctor_set(x_665, 2, x_27);
lean_ctor_set(x_665, 3, x_554);
x_666 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_665);
x_667 = lean_unsigned_to_nat(80u);
x_668 = l_Lean_Json_pretty(x_666, x_667);
x_669 = l_IO_FS_Handle_putStrLn(x_553, x_668, x_656);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; 
x_670 = lean_ctor_get(x_669, 1);
lean_inc(x_670);
lean_dec(x_669);
x_671 = lean_io_prim_handle_truncate(x_553, x_670);
if (lean_obj_tag(x_671) == 0)
{
lean_object* x_672; lean_object* x_673; 
x_672 = lean_ctor_get(x_671, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_671, 1);
lean_inc(x_673);
lean_dec(x_671);
lean_ctor_set(x_655, 0, x_672);
x_556 = x_655;
x_557 = x_673;
goto block_654;
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_674 = lean_ctor_get(x_671, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_671, 1);
lean_inc(x_675);
lean_dec(x_671);
x_676 = lean_io_error_to_string(x_674);
x_677 = 3;
x_678 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set_uint8(x_678, sizeof(void*)*1, x_677);
x_679 = lean_array_get_size(x_660);
x_680 = lean_array_push(x_660, x_678);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_680);
lean_ctor_set(x_655, 0, x_679);
x_556 = x_655;
x_557 = x_675;
goto block_654;
}
}
else
{
uint8_t x_681; 
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_681 = !lean_is_exclusive(x_669);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; uint8_t x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_682 = lean_ctor_get(x_669, 0);
x_683 = lean_io_error_to_string(x_682);
x_684 = 3;
x_685 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_685, 0, x_683);
lean_ctor_set_uint8(x_685, sizeof(void*)*1, x_684);
x_686 = lean_array_get_size(x_660);
x_687 = lean_array_push(x_660, x_685);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_687);
lean_ctor_set(x_655, 0, x_686);
lean_ctor_set_tag(x_669, 0);
lean_ctor_set(x_669, 0, x_655);
return x_669;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_688 = lean_ctor_get(x_669, 0);
x_689 = lean_ctor_get(x_669, 1);
lean_inc(x_689);
lean_inc(x_688);
lean_dec(x_669);
x_690 = lean_io_error_to_string(x_688);
x_691 = 3;
x_692 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_692, 0, x_690);
lean_ctor_set_uint8(x_692, sizeof(void*)*1, x_691);
x_693 = lean_array_get_size(x_660);
x_694 = lean_array_push(x_660, x_692);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_694);
lean_ctor_set(x_655, 0, x_693);
x_695 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_695, 0, x_655);
lean_ctor_set(x_695, 1, x_689);
return x_695;
}
}
}
else
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_696 = lean_ctor_get(x_655, 1);
lean_inc(x_696);
lean_dec(x_655);
x_697 = lean_ctor_get(x_1, 0);
lean_inc(x_697);
x_698 = l_Lake_Env_leanGithash(x_697);
lean_dec(x_697);
x_699 = l_System_Platform_target;
lean_inc(x_554);
if (lean_is_scalar(x_555)) {
 x_700 = lean_alloc_ctor(0, 4, 0);
} else {
 x_700 = x_555;
}
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_698);
lean_ctor_set(x_700, 2, x_27);
lean_ctor_set(x_700, 3, x_554);
x_701 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_700);
x_702 = lean_unsigned_to_nat(80u);
x_703 = l_Lean_Json_pretty(x_701, x_702);
x_704 = l_IO_FS_Handle_putStrLn(x_553, x_703, x_656);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; lean_object* x_706; 
x_705 = lean_ctor_get(x_704, 1);
lean_inc(x_705);
lean_dec(x_704);
x_706 = lean_io_prim_handle_truncate(x_553, x_705);
if (lean_obj_tag(x_706) == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_707 = lean_ctor_get(x_706, 0);
lean_inc(x_707);
x_708 = lean_ctor_get(x_706, 1);
lean_inc(x_708);
lean_dec(x_706);
x_709 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_709, 0, x_707);
lean_ctor_set(x_709, 1, x_696);
x_556 = x_709;
x_557 = x_708;
goto block_654;
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_710 = lean_ctor_get(x_706, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_706, 1);
lean_inc(x_711);
lean_dec(x_706);
x_712 = lean_io_error_to_string(x_710);
x_713 = 3;
x_714 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_714, 0, x_712);
lean_ctor_set_uint8(x_714, sizeof(void*)*1, x_713);
x_715 = lean_array_get_size(x_696);
x_716 = lean_array_push(x_696, x_714);
x_717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
x_556 = x_717;
x_557 = x_711;
goto block_654;
}
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_718 = lean_ctor_get(x_704, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_704, 1);
lean_inc(x_719);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 lean_ctor_release(x_704, 1);
 x_720 = x_704;
} else {
 lean_dec_ref(x_704);
 x_720 = lean_box(0);
}
x_721 = lean_io_error_to_string(x_718);
x_722 = 3;
x_723 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set_uint8(x_723, sizeof(void*)*1, x_722);
x_724 = lean_array_get_size(x_696);
x_725 = lean_array_push(x_696, x_723);
x_726 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_726, 0, x_724);
lean_ctor_set(x_726, 1, x_725);
if (lean_is_scalar(x_720)) {
 x_727 = lean_alloc_ctor(0, 2, 0);
} else {
 x_727 = x_720;
 lean_ctor_set_tag(x_727, 0);
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_719);
return x_727;
}
}
}
else
{
uint8_t x_728; 
lean_dec(x_555);
lean_dec(x_554);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_728 = !lean_is_exclusive(x_655);
if (x_728 == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; uint8_t x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_729 = lean_ctor_get(x_655, 1);
x_730 = lean_ctor_get(x_655, 0);
lean_dec(x_730);
x_731 = lean_io_error_to_string(x_658);
x_732 = 3;
x_733 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_733, 0, x_731);
lean_ctor_set_uint8(x_733, sizeof(void*)*1, x_732);
x_734 = lean_array_get_size(x_729);
x_735 = lean_array_push(x_729, x_733);
x_736 = lean_io_prim_handle_unlock(x_553, x_656);
lean_dec(x_553);
if (lean_obj_tag(x_736) == 0)
{
lean_object* x_737; lean_object* x_738; 
x_737 = lean_ctor_get(x_736, 1);
lean_inc(x_737);
lean_dec(x_736);
x_738 = lean_io_remove_file(x_21, x_737);
lean_dec(x_21);
if (lean_obj_tag(x_738) == 0)
{
uint8_t x_739; 
x_739 = !lean_is_exclusive(x_738);
if (x_739 == 0)
{
lean_object* x_740; 
x_740 = lean_ctor_get(x_738, 0);
lean_dec(x_740);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_735);
lean_ctor_set(x_655, 0, x_734);
lean_ctor_set(x_738, 0, x_655);
return x_738;
}
else
{
lean_object* x_741; lean_object* x_742; 
x_741 = lean_ctor_get(x_738, 1);
lean_inc(x_741);
lean_dec(x_738);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_735);
lean_ctor_set(x_655, 0, x_734);
x_742 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_742, 0, x_655);
lean_ctor_set(x_742, 1, x_741);
return x_742;
}
}
else
{
uint8_t x_743; 
x_743 = !lean_is_exclusive(x_738);
if (x_743 == 0)
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_744 = lean_ctor_get(x_738, 0);
x_745 = lean_io_error_to_string(x_744);
x_746 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_746, 0, x_745);
lean_ctor_set_uint8(x_746, sizeof(void*)*1, x_732);
x_747 = lean_array_push(x_735, x_746);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_747);
lean_ctor_set(x_655, 0, x_734);
lean_ctor_set_tag(x_738, 0);
lean_ctor_set(x_738, 0, x_655);
return x_738;
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_748 = lean_ctor_get(x_738, 0);
x_749 = lean_ctor_get(x_738, 1);
lean_inc(x_749);
lean_inc(x_748);
lean_dec(x_738);
x_750 = lean_io_error_to_string(x_748);
x_751 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_751, 0, x_750);
lean_ctor_set_uint8(x_751, sizeof(void*)*1, x_732);
x_752 = lean_array_push(x_735, x_751);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_752);
lean_ctor_set(x_655, 0, x_734);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_655);
lean_ctor_set(x_753, 1, x_749);
return x_753;
}
}
}
else
{
uint8_t x_754; 
lean_dec(x_21);
x_754 = !lean_is_exclusive(x_736);
if (x_754 == 0)
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_755 = lean_ctor_get(x_736, 0);
x_756 = lean_io_error_to_string(x_755);
x_757 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set_uint8(x_757, sizeof(void*)*1, x_732);
x_758 = lean_array_push(x_735, x_757);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_758);
lean_ctor_set(x_655, 0, x_734);
lean_ctor_set_tag(x_736, 0);
lean_ctor_set(x_736, 0, x_655);
return x_736;
}
else
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_759 = lean_ctor_get(x_736, 0);
x_760 = lean_ctor_get(x_736, 1);
lean_inc(x_760);
lean_inc(x_759);
lean_dec(x_736);
x_761 = lean_io_error_to_string(x_759);
x_762 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_762, 0, x_761);
lean_ctor_set_uint8(x_762, sizeof(void*)*1, x_732);
x_763 = lean_array_push(x_735, x_762);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_763);
lean_ctor_set(x_655, 0, x_734);
x_764 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_764, 0, x_655);
lean_ctor_set(x_764, 1, x_760);
return x_764;
}
}
}
else
{
lean_object* x_765; lean_object* x_766; uint8_t x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
x_765 = lean_ctor_get(x_655, 1);
lean_inc(x_765);
lean_dec(x_655);
x_766 = lean_io_error_to_string(x_658);
x_767 = 3;
x_768 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_768, 0, x_766);
lean_ctor_set_uint8(x_768, sizeof(void*)*1, x_767);
x_769 = lean_array_get_size(x_765);
x_770 = lean_array_push(x_765, x_768);
x_771 = lean_io_prim_handle_unlock(x_553, x_656);
lean_dec(x_553);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; 
x_772 = lean_ctor_get(x_771, 1);
lean_inc(x_772);
lean_dec(x_771);
x_773 = lean_io_remove_file(x_21, x_772);
lean_dec(x_21);
if (lean_obj_tag(x_773) == 0)
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_774 = lean_ctor_get(x_773, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_775 = x_773;
} else {
 lean_dec_ref(x_773);
 x_775 = lean_box(0);
}
x_776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_776, 0, x_769);
lean_ctor_set(x_776, 1, x_770);
if (lean_is_scalar(x_775)) {
 x_777 = lean_alloc_ctor(0, 2, 0);
} else {
 x_777 = x_775;
}
lean_ctor_set(x_777, 0, x_776);
lean_ctor_set(x_777, 1, x_774);
return x_777;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_778 = lean_ctor_get(x_773, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_773, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_773)) {
 lean_ctor_release(x_773, 0);
 lean_ctor_release(x_773, 1);
 x_780 = x_773;
} else {
 lean_dec_ref(x_773);
 x_780 = lean_box(0);
}
x_781 = lean_io_error_to_string(x_778);
x_782 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set_uint8(x_782, sizeof(void*)*1, x_767);
x_783 = lean_array_push(x_770, x_782);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_769);
lean_ctor_set(x_784, 1, x_783);
if (lean_is_scalar(x_780)) {
 x_785 = lean_alloc_ctor(0, 2, 0);
} else {
 x_785 = x_780;
 lean_ctor_set_tag(x_785, 0);
}
lean_ctor_set(x_785, 0, x_784);
lean_ctor_set(x_785, 1, x_779);
return x_785;
}
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; 
lean_dec(x_21);
x_786 = lean_ctor_get(x_771, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_771, 1);
lean_inc(x_787);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_788 = x_771;
} else {
 lean_dec_ref(x_771);
 x_788 = lean_box(0);
}
x_789 = lean_io_error_to_string(x_786);
x_790 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_790, 0, x_789);
lean_ctor_set_uint8(x_790, sizeof(void*)*1, x_767);
x_791 = lean_array_push(x_770, x_790);
x_792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_792, 0, x_769);
lean_ctor_set(x_792, 1, x_791);
if (lean_is_scalar(x_788)) {
 x_793 = lean_alloc_ctor(0, 2, 0);
} else {
 x_793 = x_788;
 lean_ctor_set_tag(x_793, 0);
}
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set(x_793, 1, x_787);
return x_793;
}
}
}
}
else
{
uint8_t x_794; 
lean_dec(x_657);
lean_dec(x_21);
x_794 = !lean_is_exclusive(x_655);
if (x_794 == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_795 = lean_ctor_get(x_655, 1);
x_796 = lean_ctor_get(x_655, 0);
lean_dec(x_796);
x_797 = lean_ctor_get(x_1, 0);
lean_inc(x_797);
x_798 = l_Lake_Env_leanGithash(x_797);
lean_dec(x_797);
x_799 = l_System_Platform_target;
lean_inc(x_554);
if (lean_is_scalar(x_555)) {
 x_800 = lean_alloc_ctor(0, 4, 0);
} else {
 x_800 = x_555;
}
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_798);
lean_ctor_set(x_800, 2, x_27);
lean_ctor_set(x_800, 3, x_554);
x_801 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_800);
x_802 = lean_unsigned_to_nat(80u);
x_803 = l_Lean_Json_pretty(x_801, x_802);
x_804 = l_IO_FS_Handle_putStrLn(x_553, x_803, x_656);
if (lean_obj_tag(x_804) == 0)
{
lean_object* x_805; lean_object* x_806; 
x_805 = lean_ctor_get(x_804, 1);
lean_inc(x_805);
lean_dec(x_804);
x_806 = lean_io_prim_handle_truncate(x_553, x_805);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
lean_dec(x_806);
lean_ctor_set(x_655, 0, x_807);
x_556 = x_655;
x_557 = x_808;
goto block_654;
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; uint8_t x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; 
x_809 = lean_ctor_get(x_806, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_806, 1);
lean_inc(x_810);
lean_dec(x_806);
x_811 = lean_io_error_to_string(x_809);
x_812 = 3;
x_813 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_813, 0, x_811);
lean_ctor_set_uint8(x_813, sizeof(void*)*1, x_812);
x_814 = lean_array_get_size(x_795);
x_815 = lean_array_push(x_795, x_813);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_815);
lean_ctor_set(x_655, 0, x_814);
x_556 = x_655;
x_557 = x_810;
goto block_654;
}
}
else
{
uint8_t x_816; 
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_816 = !lean_is_exclusive(x_804);
if (x_816 == 0)
{
lean_object* x_817; lean_object* x_818; uint8_t x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_817 = lean_ctor_get(x_804, 0);
x_818 = lean_io_error_to_string(x_817);
x_819 = 3;
x_820 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_820, 0, x_818);
lean_ctor_set_uint8(x_820, sizeof(void*)*1, x_819);
x_821 = lean_array_get_size(x_795);
x_822 = lean_array_push(x_795, x_820);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_822);
lean_ctor_set(x_655, 0, x_821);
lean_ctor_set_tag(x_804, 0);
lean_ctor_set(x_804, 0, x_655);
return x_804;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; uint8_t x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_823 = lean_ctor_get(x_804, 0);
x_824 = lean_ctor_get(x_804, 1);
lean_inc(x_824);
lean_inc(x_823);
lean_dec(x_804);
x_825 = lean_io_error_to_string(x_823);
x_826 = 3;
x_827 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_827, 0, x_825);
lean_ctor_set_uint8(x_827, sizeof(void*)*1, x_826);
x_828 = lean_array_get_size(x_795);
x_829 = lean_array_push(x_795, x_827);
lean_ctor_set_tag(x_655, 1);
lean_ctor_set(x_655, 1, x_829);
lean_ctor_set(x_655, 0, x_828);
x_830 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_830, 0, x_655);
lean_ctor_set(x_830, 1, x_824);
return x_830;
}
}
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_831 = lean_ctor_get(x_655, 1);
lean_inc(x_831);
lean_dec(x_655);
x_832 = lean_ctor_get(x_1, 0);
lean_inc(x_832);
x_833 = l_Lake_Env_leanGithash(x_832);
lean_dec(x_832);
x_834 = l_System_Platform_target;
lean_inc(x_554);
if (lean_is_scalar(x_555)) {
 x_835 = lean_alloc_ctor(0, 4, 0);
} else {
 x_835 = x_555;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_833);
lean_ctor_set(x_835, 2, x_27);
lean_ctor_set(x_835, 3, x_554);
x_836 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_835);
x_837 = lean_unsigned_to_nat(80u);
x_838 = l_Lean_Json_pretty(x_836, x_837);
x_839 = l_IO_FS_Handle_putStrLn(x_553, x_838, x_656);
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_840; lean_object* x_841; 
x_840 = lean_ctor_get(x_839, 1);
lean_inc(x_840);
lean_dec(x_839);
x_841 = lean_io_prim_handle_truncate(x_553, x_840);
if (lean_obj_tag(x_841) == 0)
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_842 = lean_ctor_get(x_841, 0);
lean_inc(x_842);
x_843 = lean_ctor_get(x_841, 1);
lean_inc(x_843);
lean_dec(x_841);
x_844 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_844, 0, x_842);
lean_ctor_set(x_844, 1, x_831);
x_556 = x_844;
x_557 = x_843;
goto block_654;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; uint8_t x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_845 = lean_ctor_get(x_841, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_841, 1);
lean_inc(x_846);
lean_dec(x_841);
x_847 = lean_io_error_to_string(x_845);
x_848 = 3;
x_849 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_849, 0, x_847);
lean_ctor_set_uint8(x_849, sizeof(void*)*1, x_848);
x_850 = lean_array_get_size(x_831);
x_851 = lean_array_push(x_831, x_849);
x_852 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_852, 0, x_850);
lean_ctor_set(x_852, 1, x_851);
x_556 = x_852;
x_557 = x_846;
goto block_654;
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; uint8_t x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_853 = lean_ctor_get(x_839, 0);
lean_inc(x_853);
x_854 = lean_ctor_get(x_839, 1);
lean_inc(x_854);
if (lean_is_exclusive(x_839)) {
 lean_ctor_release(x_839, 0);
 lean_ctor_release(x_839, 1);
 x_855 = x_839;
} else {
 lean_dec_ref(x_839);
 x_855 = lean_box(0);
}
x_856 = lean_io_error_to_string(x_853);
x_857 = 3;
x_858 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_858, 0, x_856);
lean_ctor_set_uint8(x_858, sizeof(void*)*1, x_857);
x_859 = lean_array_get_size(x_831);
x_860 = lean_array_push(x_831, x_858);
x_861 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_861, 0, x_859);
lean_ctor_set(x_861, 1, x_860);
if (lean_is_scalar(x_855)) {
 x_862 = lean_alloc_ctor(0, 2, 0);
} else {
 x_862 = x_855;
 lean_ctor_set_tag(x_862, 0);
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_854);
return x_862;
}
}
}
}
}
else
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_929; lean_object* x_930; lean_object* x_1030; 
x_871 = lean_ctor_get(x_550, 0);
x_872 = lean_ctor_get(x_550, 1);
lean_inc(x_872);
lean_inc(x_871);
lean_dec(x_550);
x_873 = lean_ctor_get(x_548, 3);
lean_inc(x_873);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 lean_ctor_release(x_548, 2);
 lean_ctor_release(x_548, 3);
 x_874 = x_548;
} else {
 lean_dec_ref(x_548);
 x_874 = lean_box(0);
}
x_1030 = lean_io_remove_file(x_18, x_551);
if (lean_obj_tag(x_1030) == 0)
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1031 = lean_ctor_get(x_1030, 0);
lean_inc(x_1031);
x_1032 = lean_ctor_get(x_1030, 1);
lean_inc(x_1032);
lean_dec(x_1030);
if (lean_is_scalar(x_549)) {
 x_1033 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1033 = x_549;
}
lean_ctor_set(x_1033, 0, x_1031);
x_1034 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1034, 0, x_1033);
lean_ctor_set(x_1034, 1, x_872);
x_929 = x_1034;
x_930 = x_1032;
goto block_1029;
}
else
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; 
x_1035 = lean_ctor_get(x_1030, 0);
lean_inc(x_1035);
x_1036 = lean_ctor_get(x_1030, 1);
lean_inc(x_1036);
lean_dec(x_1030);
if (lean_is_scalar(x_549)) {
 x_1037 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1037 = x_549;
 lean_ctor_set_tag(x_1037, 0);
}
lean_ctor_set(x_1037, 0, x_1035);
x_1038 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1038, 0, x_1037);
lean_ctor_set(x_1038, 1, x_872);
x_929 = x_1038;
x_930 = x_1036;
goto block_1029;
}
block_928:
{
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
x_878 = lean_ctor_get(x_1, 9);
lean_inc(x_878);
lean_dec(x_1);
x_879 = l_Lake_elabConfigFile(x_13, x_873, x_878, x_4, x_877, x_876);
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_880; 
x_880 = lean_ctor_get(x_879, 0);
lean_inc(x_880);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
x_881 = lean_ctor_get(x_879, 1);
lean_inc(x_881);
lean_dec(x_879);
x_882 = lean_ctor_get(x_880, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_880, 1);
lean_inc(x_883);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_884 = x_880;
} else {
 lean_dec_ref(x_880);
 x_884 = lean_box(0);
}
lean_inc(x_882);
x_885 = lean_write_module(x_882, x_18, x_881);
if (lean_obj_tag(x_885) == 0)
{
lean_object* x_886; lean_object* x_887; 
x_886 = lean_ctor_get(x_885, 1);
lean_inc(x_886);
lean_dec(x_885);
x_887 = lean_io_prim_handle_unlock(x_871, x_886);
lean_dec(x_871);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_888 = lean_ctor_get(x_887, 1);
lean_inc(x_888);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_889 = x_887;
} else {
 lean_dec_ref(x_887);
 x_889 = lean_box(0);
}
if (lean_is_scalar(x_884)) {
 x_890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_890 = x_884;
}
lean_ctor_set(x_890, 0, x_882);
lean_ctor_set(x_890, 1, x_883);
if (lean_is_scalar(x_889)) {
 x_891 = lean_alloc_ctor(0, 2, 0);
} else {
 x_891 = x_889;
}
lean_ctor_set(x_891, 0, x_890);
lean_ctor_set(x_891, 1, x_888);
return x_891;
}
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; uint8_t x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; 
lean_dec(x_882);
x_892 = lean_ctor_get(x_887, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_887, 1);
lean_inc(x_893);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_894 = x_887;
} else {
 lean_dec_ref(x_887);
 x_894 = lean_box(0);
}
x_895 = lean_io_error_to_string(x_892);
x_896 = 3;
x_897 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_897, 0, x_895);
lean_ctor_set_uint8(x_897, sizeof(void*)*1, x_896);
x_898 = lean_array_get_size(x_883);
x_899 = lean_array_push(x_883, x_897);
if (lean_is_scalar(x_884)) {
 x_900 = lean_alloc_ctor(1, 2, 0);
} else {
 x_900 = x_884;
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
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; uint8_t x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
lean_dec(x_882);
lean_dec(x_871);
x_902 = lean_ctor_get(x_885, 0);
lean_inc(x_902);
x_903 = lean_ctor_get(x_885, 1);
lean_inc(x_903);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_904 = x_885;
} else {
 lean_dec_ref(x_885);
 x_904 = lean_box(0);
}
x_905 = lean_io_error_to_string(x_902);
x_906 = 3;
x_907 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_907, 0, x_905);
lean_ctor_set_uint8(x_907, sizeof(void*)*1, x_906);
x_908 = lean_array_get_size(x_883);
x_909 = lean_array_push(x_883, x_907);
if (lean_is_scalar(x_884)) {
 x_910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_910 = x_884;
 lean_ctor_set_tag(x_910, 1);
}
lean_ctor_set(x_910, 0, x_908);
lean_ctor_set(x_910, 1, x_909);
if (lean_is_scalar(x_904)) {
 x_911 = lean_alloc_ctor(0, 2, 0);
} else {
 x_911 = x_904;
 lean_ctor_set_tag(x_911, 0);
}
lean_ctor_set(x_911, 0, x_910);
lean_ctor_set(x_911, 1, x_903);
return x_911;
}
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
lean_dec(x_871);
lean_dec(x_18);
x_912 = lean_ctor_get(x_879, 1);
lean_inc(x_912);
if (lean_is_exclusive(x_879)) {
 lean_ctor_release(x_879, 0);
 lean_ctor_release(x_879, 1);
 x_913 = x_879;
} else {
 lean_dec_ref(x_879);
 x_913 = lean_box(0);
}
x_914 = lean_ctor_get(x_880, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_880, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_916 = x_880;
} else {
 lean_dec_ref(x_880);
 x_916 = lean_box(0);
}
if (lean_is_scalar(x_916)) {
 x_917 = lean_alloc_ctor(1, 2, 0);
} else {
 x_917 = x_916;
}
lean_ctor_set(x_917, 0, x_914);
lean_ctor_set(x_917, 1, x_915);
if (lean_is_scalar(x_913)) {
 x_918 = lean_alloc_ctor(0, 2, 0);
} else {
 x_918 = x_913;
}
lean_ctor_set(x_918, 0, x_917);
lean_ctor_set(x_918, 1, x_912);
return x_918;
}
}
else
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
lean_dec(x_871);
lean_dec(x_18);
x_919 = lean_ctor_get(x_879, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_879, 1);
lean_inc(x_920);
if (lean_is_exclusive(x_879)) {
 lean_ctor_release(x_879, 0);
 lean_ctor_release(x_879, 1);
 x_921 = x_879;
} else {
 lean_dec_ref(x_879);
 x_921 = lean_box(0);
}
if (lean_is_scalar(x_921)) {
 x_922 = lean_alloc_ctor(1, 2, 0);
} else {
 x_922 = x_921;
}
lean_ctor_set(x_922, 0, x_919);
lean_ctor_set(x_922, 1, x_920);
return x_922;
}
}
else
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_923 = lean_ctor_get(x_875, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_875, 1);
lean_inc(x_924);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_925 = x_875;
} else {
 lean_dec_ref(x_875);
 x_925 = lean_box(0);
}
if (lean_is_scalar(x_925)) {
 x_926 = lean_alloc_ctor(1, 2, 0);
} else {
 x_926 = x_925;
}
lean_ctor_set(x_926, 0, x_923);
lean_ctor_set(x_926, 1, x_924);
x_927 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_927, 0, x_926);
lean_ctor_set(x_927, 1, x_876);
return x_927;
}
}
block_1029:
{
lean_object* x_931; 
x_931 = lean_ctor_get(x_929, 0);
lean_inc(x_931);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
lean_dec(x_931);
if (lean_obj_tag(x_932) == 11)
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_932);
lean_dec(x_21);
x_933 = lean_ctor_get(x_929, 1);
lean_inc(x_933);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_934 = x_929;
} else {
 lean_dec_ref(x_929);
 x_934 = lean_box(0);
}
x_935 = lean_ctor_get(x_1, 0);
lean_inc(x_935);
x_936 = l_Lake_Env_leanGithash(x_935);
lean_dec(x_935);
x_937 = l_System_Platform_target;
lean_inc(x_873);
if (lean_is_scalar(x_874)) {
 x_938 = lean_alloc_ctor(0, 4, 0);
} else {
 x_938 = x_874;
}
lean_ctor_set(x_938, 0, x_937);
lean_ctor_set(x_938, 1, x_936);
lean_ctor_set(x_938, 2, x_27);
lean_ctor_set(x_938, 3, x_873);
x_939 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_938);
x_940 = lean_unsigned_to_nat(80u);
x_941 = l_Lean_Json_pretty(x_939, x_940);
x_942 = l_IO_FS_Handle_putStrLn(x_871, x_941, x_930);
if (lean_obj_tag(x_942) == 0)
{
lean_object* x_943; lean_object* x_944; 
x_943 = lean_ctor_get(x_942, 1);
lean_inc(x_943);
lean_dec(x_942);
x_944 = lean_io_prim_handle_truncate(x_871, x_943);
if (lean_obj_tag(x_944) == 0)
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_945 = lean_ctor_get(x_944, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_944, 1);
lean_inc(x_946);
lean_dec(x_944);
if (lean_is_scalar(x_934)) {
 x_947 = lean_alloc_ctor(0, 2, 0);
} else {
 x_947 = x_934;
}
lean_ctor_set(x_947, 0, x_945);
lean_ctor_set(x_947, 1, x_933);
x_875 = x_947;
x_876 = x_946;
goto block_928;
}
else
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; uint8_t x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_948 = lean_ctor_get(x_944, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_944, 1);
lean_inc(x_949);
lean_dec(x_944);
x_950 = lean_io_error_to_string(x_948);
x_951 = 3;
x_952 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_952, 0, x_950);
lean_ctor_set_uint8(x_952, sizeof(void*)*1, x_951);
x_953 = lean_array_get_size(x_933);
x_954 = lean_array_push(x_933, x_952);
if (lean_is_scalar(x_934)) {
 x_955 = lean_alloc_ctor(1, 2, 0);
} else {
 x_955 = x_934;
 lean_ctor_set_tag(x_955, 1);
}
lean_ctor_set(x_955, 0, x_953);
lean_ctor_set(x_955, 1, x_954);
x_875 = x_955;
x_876 = x_949;
goto block_928;
}
}
else
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; uint8_t x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; 
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_956 = lean_ctor_get(x_942, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_942, 1);
lean_inc(x_957);
if (lean_is_exclusive(x_942)) {
 lean_ctor_release(x_942, 0);
 lean_ctor_release(x_942, 1);
 x_958 = x_942;
} else {
 lean_dec_ref(x_942);
 x_958 = lean_box(0);
}
x_959 = lean_io_error_to_string(x_956);
x_960 = 3;
x_961 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_961, 0, x_959);
lean_ctor_set_uint8(x_961, sizeof(void*)*1, x_960);
x_962 = lean_array_get_size(x_933);
x_963 = lean_array_push(x_933, x_961);
if (lean_is_scalar(x_934)) {
 x_964 = lean_alloc_ctor(1, 2, 0);
} else {
 x_964 = x_934;
 lean_ctor_set_tag(x_964, 1);
}
lean_ctor_set(x_964, 0, x_962);
lean_ctor_set(x_964, 1, x_963);
if (lean_is_scalar(x_958)) {
 x_965 = lean_alloc_ctor(0, 2, 0);
} else {
 x_965 = x_958;
 lean_ctor_set_tag(x_965, 0);
}
lean_ctor_set(x_965, 0, x_964);
lean_ctor_set(x_965, 1, x_957);
return x_965;
}
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; uint8_t x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
lean_dec(x_874);
lean_dec(x_873);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_966 = lean_ctor_get(x_929, 1);
lean_inc(x_966);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_967 = x_929;
} else {
 lean_dec_ref(x_929);
 x_967 = lean_box(0);
}
x_968 = lean_io_error_to_string(x_932);
x_969 = 3;
x_970 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_970, 0, x_968);
lean_ctor_set_uint8(x_970, sizeof(void*)*1, x_969);
x_971 = lean_array_get_size(x_966);
x_972 = lean_array_push(x_966, x_970);
x_973 = lean_io_prim_handle_unlock(x_871, x_930);
lean_dec(x_871);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; lean_object* x_975; 
x_974 = lean_ctor_get(x_973, 1);
lean_inc(x_974);
lean_dec(x_973);
x_975 = lean_io_remove_file(x_21, x_974);
lean_dec(x_21);
if (lean_obj_tag(x_975) == 0)
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; 
x_976 = lean_ctor_get(x_975, 1);
lean_inc(x_976);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_977 = x_975;
} else {
 lean_dec_ref(x_975);
 x_977 = lean_box(0);
}
if (lean_is_scalar(x_967)) {
 x_978 = lean_alloc_ctor(1, 2, 0);
} else {
 x_978 = x_967;
 lean_ctor_set_tag(x_978, 1);
}
lean_ctor_set(x_978, 0, x_971);
lean_ctor_set(x_978, 1, x_972);
if (lean_is_scalar(x_977)) {
 x_979 = lean_alloc_ctor(0, 2, 0);
} else {
 x_979 = x_977;
}
lean_ctor_set(x_979, 0, x_978);
lean_ctor_set(x_979, 1, x_976);
return x_979;
}
else
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_980 = lean_ctor_get(x_975, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_975, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_975)) {
 lean_ctor_release(x_975, 0);
 lean_ctor_release(x_975, 1);
 x_982 = x_975;
} else {
 lean_dec_ref(x_975);
 x_982 = lean_box(0);
}
x_983 = lean_io_error_to_string(x_980);
x_984 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_984, 0, x_983);
lean_ctor_set_uint8(x_984, sizeof(void*)*1, x_969);
x_985 = lean_array_push(x_972, x_984);
if (lean_is_scalar(x_967)) {
 x_986 = lean_alloc_ctor(1, 2, 0);
} else {
 x_986 = x_967;
 lean_ctor_set_tag(x_986, 1);
}
lean_ctor_set(x_986, 0, x_971);
lean_ctor_set(x_986, 1, x_985);
if (lean_is_scalar(x_982)) {
 x_987 = lean_alloc_ctor(0, 2, 0);
} else {
 x_987 = x_982;
 lean_ctor_set_tag(x_987, 0);
}
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set(x_987, 1, x_981);
return x_987;
}
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; 
lean_dec(x_21);
x_988 = lean_ctor_get(x_973, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_973, 1);
lean_inc(x_989);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 x_990 = x_973;
} else {
 lean_dec_ref(x_973);
 x_990 = lean_box(0);
}
x_991 = lean_io_error_to_string(x_988);
x_992 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_992, 0, x_991);
lean_ctor_set_uint8(x_992, sizeof(void*)*1, x_969);
x_993 = lean_array_push(x_972, x_992);
if (lean_is_scalar(x_967)) {
 x_994 = lean_alloc_ctor(1, 2, 0);
} else {
 x_994 = x_967;
 lean_ctor_set_tag(x_994, 1);
}
lean_ctor_set(x_994, 0, x_971);
lean_ctor_set(x_994, 1, x_993);
if (lean_is_scalar(x_990)) {
 x_995 = lean_alloc_ctor(0, 2, 0);
} else {
 x_995 = x_990;
 lean_ctor_set_tag(x_995, 0);
}
lean_ctor_set(x_995, 0, x_994);
lean_ctor_set(x_995, 1, x_989);
return x_995;
}
}
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
lean_dec(x_931);
lean_dec(x_21);
x_996 = lean_ctor_get(x_929, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_997 = x_929;
} else {
 lean_dec_ref(x_929);
 x_997 = lean_box(0);
}
x_998 = lean_ctor_get(x_1, 0);
lean_inc(x_998);
x_999 = l_Lake_Env_leanGithash(x_998);
lean_dec(x_998);
x_1000 = l_System_Platform_target;
lean_inc(x_873);
if (lean_is_scalar(x_874)) {
 x_1001 = lean_alloc_ctor(0, 4, 0);
} else {
 x_1001 = x_874;
}
lean_ctor_set(x_1001, 0, x_1000);
lean_ctor_set(x_1001, 1, x_999);
lean_ctor_set(x_1001, 2, x_27);
lean_ctor_set(x_1001, 3, x_873);
x_1002 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1001);
x_1003 = lean_unsigned_to_nat(80u);
x_1004 = l_Lean_Json_pretty(x_1002, x_1003);
x_1005 = l_IO_FS_Handle_putStrLn(x_871, x_1004, x_930);
if (lean_obj_tag(x_1005) == 0)
{
lean_object* x_1006; lean_object* x_1007; 
x_1006 = lean_ctor_get(x_1005, 1);
lean_inc(x_1006);
lean_dec(x_1005);
x_1007 = lean_io_prim_handle_truncate(x_871, x_1006);
if (lean_obj_tag(x_1007) == 0)
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
x_1008 = lean_ctor_get(x_1007, 0);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_1007, 1);
lean_inc(x_1009);
lean_dec(x_1007);
if (lean_is_scalar(x_997)) {
 x_1010 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1010 = x_997;
}
lean_ctor_set(x_1010, 0, x_1008);
lean_ctor_set(x_1010, 1, x_996);
x_875 = x_1010;
x_876 = x_1009;
goto block_928;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; uint8_t x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1011 = lean_ctor_get(x_1007, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_1007, 1);
lean_inc(x_1012);
lean_dec(x_1007);
x_1013 = lean_io_error_to_string(x_1011);
x_1014 = 3;
x_1015 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1015, 0, x_1013);
lean_ctor_set_uint8(x_1015, sizeof(void*)*1, x_1014);
x_1016 = lean_array_get_size(x_996);
x_1017 = lean_array_push(x_996, x_1015);
if (lean_is_scalar(x_997)) {
 x_1018 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1018 = x_997;
 lean_ctor_set_tag(x_1018, 1);
}
lean_ctor_set(x_1018, 0, x_1016);
lean_ctor_set(x_1018, 1, x_1017);
x_875 = x_1018;
x_876 = x_1012;
goto block_928;
}
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; uint8_t x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
lean_dec(x_873);
lean_dec(x_871);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1019 = lean_ctor_get(x_1005, 0);
lean_inc(x_1019);
x_1020 = lean_ctor_get(x_1005, 1);
lean_inc(x_1020);
if (lean_is_exclusive(x_1005)) {
 lean_ctor_release(x_1005, 0);
 lean_ctor_release(x_1005, 1);
 x_1021 = x_1005;
} else {
 lean_dec_ref(x_1005);
 x_1021 = lean_box(0);
}
x_1022 = lean_io_error_to_string(x_1019);
x_1023 = 3;
x_1024 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1024, 0, x_1022);
lean_ctor_set_uint8(x_1024, sizeof(void*)*1, x_1023);
x_1025 = lean_array_get_size(x_996);
x_1026 = lean_array_push(x_996, x_1024);
if (lean_is_scalar(x_997)) {
 x_1027 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1027 = x_997;
 lean_ctor_set_tag(x_1027, 1);
}
lean_ctor_set(x_1027, 0, x_1025);
lean_ctor_set(x_1027, 1, x_1026);
if (lean_is_scalar(x_1021)) {
 x_1028 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1028 = x_1021;
 lean_ctor_set_tag(x_1028, 0);
}
lean_ctor_set(x_1028, 0, x_1027);
lean_ctor_set(x_1028, 1, x_1020);
return x_1028;
}
}
}
}
}
else
{
uint8_t x_1039; 
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1039 = !lean_is_exclusive(x_550);
if (x_1039 == 0)
{
lean_object* x_1040; 
x_1040 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1040, 0, x_550);
lean_ctor_set(x_1040, 1, x_551);
return x_1040;
}
else
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1041 = lean_ctor_get(x_550, 0);
x_1042 = lean_ctor_get(x_550, 1);
lean_inc(x_1042);
lean_inc(x_1041);
lean_dec(x_550);
x_1043 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1043, 0, x_1041);
lean_ctor_set(x_1043, 1, x_1042);
x_1044 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1044, 0, x_1043);
lean_ctor_set(x_1044, 1, x_551);
return x_1044;
}
}
}
block_1097:
{
lean_object* x_1050; lean_object* x_1051; uint8_t x_1059; lean_object* x_1060; 
lean_dec(x_1049);
x_1059 = 1;
x_1060 = lean_io_prim_handle_mk(x_24, x_1059, x_1048);
lean_dec(x_24);
if (lean_obj_tag(x_1060) == 0)
{
lean_object* x_1061; lean_object* x_1062; uint8_t x_1063; lean_object* x_1064; 
x_1061 = lean_ctor_get(x_1060, 0);
lean_inc(x_1061);
x_1062 = lean_ctor_get(x_1060, 1);
lean_inc(x_1062);
lean_dec(x_1060);
x_1063 = 1;
x_1064 = lean_io_prim_handle_try_lock(x_1061, x_1063, x_1062);
if (lean_obj_tag(x_1064) == 0)
{
lean_object* x_1065; uint8_t x_1066; 
x_1065 = lean_ctor_get(x_1064, 0);
lean_inc(x_1065);
x_1066 = lean_unbox(x_1065);
lean_dec(x_1065);
if (x_1066 == 0)
{
lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_1061);
lean_dec(x_528);
x_1067 = lean_ctor_get(x_1064, 1);
lean_inc(x_1067);
lean_dec(x_1064);
x_1068 = lean_io_prim_handle_unlock(x_526, x_1067);
lean_dec(x_526);
if (lean_obj_tag(x_1068) == 0)
{
lean_object* x_1069; lean_object* x_1070; 
x_1069 = lean_ctor_get(x_1068, 1);
lean_inc(x_1069);
lean_dec(x_1068);
x_1070 = l_Lake_importConfigFile___closed__12;
x_1050 = x_1070;
x_1051 = x_1069;
goto block_1058;
}
else
{
lean_object* x_1071; lean_object* x_1072; 
x_1071 = lean_ctor_get(x_1068, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1068, 1);
lean_inc(x_1072);
lean_dec(x_1068);
x_1050 = x_1071;
x_1051 = x_1072;
goto block_1058;
}
}
else
{
lean_object* x_1073; lean_object* x_1074; 
x_1073 = lean_ctor_get(x_1064, 1);
lean_inc(x_1073);
lean_dec(x_1064);
x_1074 = lean_io_prim_handle_unlock(x_526, x_1073);
lean_dec(x_526);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; uint8_t x_1076; lean_object* x_1077; 
x_1075 = lean_ctor_get(x_1074, 1);
lean_inc(x_1075);
lean_dec(x_1074);
x_1076 = 3;
x_1077 = lean_io_prim_handle_mk(x_21, x_1076, x_1075);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
lean_dec(x_1077);
x_1080 = lean_io_prim_handle_lock(x_1078, x_1063, x_1079);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; lean_object* x_1082; 
x_1081 = lean_ctor_get(x_1080, 1);
lean_inc(x_1081);
lean_dec(x_1080);
x_1082 = lean_io_prim_handle_unlock(x_1061, x_1081);
lean_dec(x_1061);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; lean_object* x_1084; 
lean_dec(x_533);
x_1083 = lean_ctor_get(x_1082, 1);
lean_inc(x_1083);
lean_dec(x_1082);
if (lean_is_scalar(x_528)) {
 x_1084 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1084 = x_528;
}
lean_ctor_set(x_1084, 0, x_1078);
lean_ctor_set(x_1084, 1, x_532);
x_550 = x_1084;
x_551 = x_1083;
goto block_1045;
}
else
{
lean_object* x_1085; lean_object* x_1086; 
lean_dec(x_1078);
lean_dec(x_528);
x_1085 = lean_ctor_get(x_1082, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1082, 1);
lean_inc(x_1086);
lean_dec(x_1082);
x_1050 = x_1085;
x_1051 = x_1086;
goto block_1058;
}
}
else
{
lean_object* x_1087; lean_object* x_1088; 
lean_dec(x_1078);
lean_dec(x_1061);
lean_dec(x_528);
x_1087 = lean_ctor_get(x_1080, 0);
lean_inc(x_1087);
x_1088 = lean_ctor_get(x_1080, 1);
lean_inc(x_1088);
lean_dec(x_1080);
x_1050 = x_1087;
x_1051 = x_1088;
goto block_1058;
}
}
else
{
lean_object* x_1089; lean_object* x_1090; 
lean_dec(x_1061);
lean_dec(x_528);
x_1089 = lean_ctor_get(x_1077, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1077, 1);
lean_inc(x_1090);
lean_dec(x_1077);
x_1050 = x_1089;
x_1051 = x_1090;
goto block_1058;
}
}
else
{
lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_1061);
lean_dec(x_528);
x_1091 = lean_ctor_get(x_1074, 0);
lean_inc(x_1091);
x_1092 = lean_ctor_get(x_1074, 1);
lean_inc(x_1092);
lean_dec(x_1074);
x_1050 = x_1091;
x_1051 = x_1092;
goto block_1058;
}
}
}
else
{
lean_object* x_1093; lean_object* x_1094; 
lean_dec(x_1061);
lean_dec(x_528);
lean_dec(x_526);
x_1093 = lean_ctor_get(x_1064, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1064, 1);
lean_inc(x_1094);
lean_dec(x_1064);
x_1050 = x_1093;
x_1051 = x_1094;
goto block_1058;
}
}
else
{
lean_object* x_1095; lean_object* x_1096; 
lean_dec(x_528);
lean_dec(x_526);
x_1095 = lean_ctor_get(x_1060, 0);
lean_inc(x_1095);
x_1096 = lean_ctor_get(x_1060, 1);
lean_inc(x_1096);
lean_dec(x_1060);
x_1050 = x_1095;
x_1051 = x_1096;
goto block_1058;
}
block_1058:
{
lean_object* x_1052; uint8_t x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; 
x_1052 = lean_io_error_to_string(x_1050);
x_1053 = 3;
x_1054 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1054, 0, x_1052);
lean_ctor_set_uint8(x_1054, sizeof(void*)*1, x_1053);
x_1055 = lean_array_get_size(x_532);
x_1056 = lean_array_push(x_532, x_1054);
if (lean_is_scalar(x_533)) {
 x_1057 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1057 = x_533;
 lean_ctor_set_tag(x_1057, 1);
}
lean_ctor_set(x_1057, 0, x_1055);
lean_ctor_set(x_1057, 1, x_1056);
x_550 = x_1057;
x_551 = x_1051;
goto block_1045;
}
}
}
}
}
else
{
uint8_t x_1159; 
lean_dec(x_528);
lean_dec(x_526);
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1159 = !lean_is_exclusive(x_529);
if (x_1159 == 0)
{
lean_object* x_1160; 
x_1160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1160, 0, x_529);
lean_ctor_set(x_1160, 1, x_530);
return x_1160;
}
else
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1161 = lean_ctor_get(x_529, 0);
x_1162 = lean_ctor_get(x_529, 1);
lean_inc(x_1162);
lean_inc(x_1161);
lean_dec(x_529);
x_1163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1163, 0, x_1161);
lean_ctor_set(x_1163, 1, x_1162);
x_1164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1164, 0, x_1163);
lean_ctor_set(x_1164, 1, x_530);
return x_1164;
}
}
}
}
else
{
uint8_t x_1259; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_1259 = !lean_is_exclusive(x_524);
if (x_1259 == 0)
{
lean_object* x_1260; 
x_1260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1260, 0, x_524);
lean_ctor_set(x_1260, 1, x_525);
return x_1260;
}
else
{
lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; 
x_1261 = lean_ctor_get(x_524, 0);
x_1262 = lean_ctor_get(x_524, 1);
lean_inc(x_1262);
lean_inc(x_1261);
lean_dec(x_524);
x_1263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1263, 0, x_1261);
lean_ctor_set(x_1263, 1, x_1262);
x_1264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1264, 0, x_1263);
lean_ctor_set(x_1264, 1, x_525);
return x_1264;
}
}
}
block_2015:
{
lean_object* x_1268; 
x_1268 = lean_ctor_get(x_1266, 0);
lean_inc(x_1268);
if (lean_obj_tag(x_1268) == 0)
{
lean_object* x_1269; 
x_1269 = lean_ctor_get(x_1268, 0);
lean_inc(x_1269);
lean_dec(x_1268);
if (lean_obj_tag(x_1269) == 0)
{
uint8_t x_1270; 
lean_dec(x_1269);
x_1270 = !lean_is_exclusive(x_1266);
if (x_1270 == 0)
{
lean_object* x_1271; lean_object* x_1272; uint8_t x_1273; lean_object* x_1274; 
x_1271 = lean_ctor_get(x_1266, 1);
x_1272 = lean_ctor_get(x_1266, 0);
lean_dec(x_1272);
x_1273 = 0;
x_1274 = lean_io_prim_handle_mk(x_21, x_1273, x_1267);
if (lean_obj_tag(x_1274) == 0)
{
lean_object* x_1275; lean_object* x_1276; 
x_1275 = lean_ctor_get(x_1274, 0);
lean_inc(x_1275);
x_1276 = lean_ctor_get(x_1274, 1);
lean_inc(x_1276);
lean_dec(x_1274);
lean_ctor_set(x_1266, 0, x_1275);
x_524 = x_1266;
x_525 = x_1276;
goto block_1265;
}
else
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; uint8_t x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; 
x_1277 = lean_ctor_get(x_1274, 0);
lean_inc(x_1277);
x_1278 = lean_ctor_get(x_1274, 1);
lean_inc(x_1278);
lean_dec(x_1274);
x_1279 = lean_io_error_to_string(x_1277);
x_1280 = 3;
x_1281 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1281, 0, x_1279);
lean_ctor_set_uint8(x_1281, sizeof(void*)*1, x_1280);
x_1282 = lean_array_get_size(x_1271);
x_1283 = lean_array_push(x_1271, x_1281);
lean_ctor_set_tag(x_1266, 1);
lean_ctor_set(x_1266, 1, x_1283);
lean_ctor_set(x_1266, 0, x_1282);
x_524 = x_1266;
x_525 = x_1278;
goto block_1265;
}
}
else
{
lean_object* x_1284; uint8_t x_1285; lean_object* x_1286; 
x_1284 = lean_ctor_get(x_1266, 1);
lean_inc(x_1284);
lean_dec(x_1266);
x_1285 = 0;
x_1286 = lean_io_prim_handle_mk(x_21, x_1285, x_1267);
if (lean_obj_tag(x_1286) == 0)
{
lean_object* x_1287; lean_object* x_1288; lean_object* x_1289; 
x_1287 = lean_ctor_get(x_1286, 0);
lean_inc(x_1287);
x_1288 = lean_ctor_get(x_1286, 1);
lean_inc(x_1288);
lean_dec(x_1286);
x_1289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1289, 0, x_1287);
lean_ctor_set(x_1289, 1, x_1284);
x_524 = x_1289;
x_525 = x_1288;
goto block_1265;
}
else
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; uint8_t x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; 
x_1290 = lean_ctor_get(x_1286, 0);
lean_inc(x_1290);
x_1291 = lean_ctor_get(x_1286, 1);
lean_inc(x_1291);
lean_dec(x_1286);
x_1292 = lean_io_error_to_string(x_1290);
x_1293 = 3;
x_1294 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1294, 0, x_1292);
lean_ctor_set_uint8(x_1294, sizeof(void*)*1, x_1293);
x_1295 = lean_array_get_size(x_1284);
x_1296 = lean_array_push(x_1284, x_1294);
x_1297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1297, 0, x_1295);
lean_ctor_set(x_1297, 1, x_1296);
x_524 = x_1297;
x_525 = x_1291;
goto block_1265;
}
}
}
else
{
uint8_t x_1298; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_1298 = !lean_is_exclusive(x_1266);
if (x_1298 == 0)
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; uint8_t x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1299 = lean_ctor_get(x_1266, 1);
x_1300 = lean_ctor_get(x_1266, 0);
lean_dec(x_1300);
x_1301 = lean_io_error_to_string(x_1269);
x_1302 = 3;
x_1303 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1303, 0, x_1301);
lean_ctor_set_uint8(x_1303, sizeof(void*)*1, x_1302);
x_1304 = lean_array_get_size(x_1299);
x_1305 = lean_array_push(x_1299, x_1303);
lean_ctor_set_tag(x_1266, 1);
lean_ctor_set(x_1266, 1, x_1305);
lean_ctor_set(x_1266, 0, x_1304);
x_1306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1306, 0, x_1266);
lean_ctor_set(x_1306, 1, x_1267);
return x_1306;
}
else
{
lean_object* x_1307; lean_object* x_1308; uint8_t x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1307 = lean_ctor_get(x_1266, 1);
lean_inc(x_1307);
lean_dec(x_1266);
x_1308 = lean_io_error_to_string(x_1269);
x_1309 = 3;
x_1310 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1310, 0, x_1308);
lean_ctor_set_uint8(x_1310, sizeof(void*)*1, x_1309);
x_1311 = lean_array_get_size(x_1307);
x_1312 = lean_array_push(x_1307, x_1310);
x_1313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1313, 0, x_1311);
lean_ctor_set(x_1313, 1, x_1312);
x_1314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1314, 0, x_1313);
lean_ctor_set(x_1314, 1, x_1267);
return x_1314;
}
}
}
else
{
uint8_t x_1315; 
lean_dec(x_29);
lean_dec(x_24);
lean_dec(x_12);
x_1315 = !lean_is_exclusive(x_1266);
if (x_1315 == 0)
{
lean_object* x_1316; lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; uint8_t x_1813; lean_object* x_1814; 
x_1316 = lean_ctor_get(x_1266, 1);
x_1317 = lean_ctor_get(x_1266, 0);
lean_dec(x_1317);
x_1318 = lean_ctor_get(x_1268, 0);
lean_inc(x_1318);
if (lean_is_exclusive(x_1268)) {
 lean_ctor_release(x_1268, 0);
 x_1319 = x_1268;
} else {
 lean_dec_ref(x_1268);
 x_1319 = lean_box(0);
}
x_1813 = 1;
x_1814 = lean_io_prim_handle_lock(x_1318, x_1813, x_1267);
if (lean_obj_tag(x_1814) == 0)
{
lean_object* x_1815; lean_object* x_1816; 
x_1815 = lean_ctor_get(x_1814, 0);
lean_inc(x_1815);
x_1816 = lean_ctor_get(x_1814, 1);
lean_inc(x_1816);
lean_dec(x_1814);
lean_ctor_set(x_1266, 0, x_1815);
x_1320 = x_1266;
x_1321 = x_1816;
goto block_1812;
}
else
{
lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; uint8_t x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; 
x_1817 = lean_ctor_get(x_1814, 0);
lean_inc(x_1817);
x_1818 = lean_ctor_get(x_1814, 1);
lean_inc(x_1818);
lean_dec(x_1814);
x_1819 = lean_io_error_to_string(x_1817);
x_1820 = 3;
x_1821 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1821, 0, x_1819);
lean_ctor_set_uint8(x_1821, sizeof(void*)*1, x_1820);
x_1822 = lean_array_get_size(x_1316);
x_1823 = lean_array_push(x_1316, x_1821);
lean_ctor_set_tag(x_1266, 1);
lean_ctor_set(x_1266, 1, x_1823);
lean_ctor_set(x_1266, 0, x_1822);
x_1320 = x_1266;
x_1321 = x_1818;
goto block_1812;
}
block_1812:
{
if (lean_obj_tag(x_1320) == 0)
{
uint8_t x_1322; 
x_1322 = !lean_is_exclusive(x_1320);
if (x_1322 == 0)
{
lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1424; lean_object* x_1425; lean_object* x_1633; 
x_1323 = lean_ctor_get(x_1320, 0);
lean_dec(x_1323);
x_1324 = lean_ctor_get(x_1, 8);
lean_inc(x_1324);
x_1633 = lean_io_remove_file(x_18, x_1321);
if (lean_obj_tag(x_1633) == 0)
{
lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; 
x_1634 = lean_ctor_get(x_1633, 0);
lean_inc(x_1634);
x_1635 = lean_ctor_get(x_1633, 1);
lean_inc(x_1635);
lean_dec(x_1633);
if (lean_is_scalar(x_1319)) {
 x_1636 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1636 = x_1319;
}
lean_ctor_set(x_1636, 0, x_1634);
lean_ctor_set(x_1320, 0, x_1636);
x_1424 = x_1320;
x_1425 = x_1635;
goto block_1632;
}
else
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; 
x_1637 = lean_ctor_get(x_1633, 0);
lean_inc(x_1637);
x_1638 = lean_ctor_get(x_1633, 1);
lean_inc(x_1638);
lean_dec(x_1633);
if (lean_is_scalar(x_1319)) {
 x_1639 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1639 = x_1319;
 lean_ctor_set_tag(x_1639, 0);
}
lean_ctor_set(x_1639, 0, x_1637);
lean_ctor_set(x_1320, 0, x_1639);
x_1424 = x_1320;
x_1425 = x_1638;
goto block_1632;
}
block_1423:
{
if (lean_obj_tag(x_1325) == 0)
{
lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; 
x_1327 = lean_ctor_get(x_1325, 1);
lean_inc(x_1327);
lean_dec(x_1325);
x_1328 = lean_ctor_get(x_1, 9);
lean_inc(x_1328);
lean_dec(x_1);
x_1329 = l_Lake_elabConfigFile(x_13, x_1324, x_1328, x_4, x_1327, x_1326);
if (lean_obj_tag(x_1329) == 0)
{
lean_object* x_1330; 
x_1330 = lean_ctor_get(x_1329, 0);
lean_inc(x_1330);
if (lean_obj_tag(x_1330) == 0)
{
lean_object* x_1331; uint8_t x_1332; 
x_1331 = lean_ctor_get(x_1329, 1);
lean_inc(x_1331);
lean_dec(x_1329);
x_1332 = !lean_is_exclusive(x_1330);
if (x_1332 == 0)
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
x_1333 = lean_ctor_get(x_1330, 0);
x_1334 = lean_ctor_get(x_1330, 1);
lean_inc(x_1333);
x_1335 = lean_write_module(x_1333, x_18, x_1331);
if (lean_obj_tag(x_1335) == 0)
{
lean_object* x_1336; lean_object* x_1337; 
x_1336 = lean_ctor_get(x_1335, 1);
lean_inc(x_1336);
lean_dec(x_1335);
x_1337 = lean_io_prim_handle_unlock(x_1318, x_1336);
lean_dec(x_1318);
if (lean_obj_tag(x_1337) == 0)
{
uint8_t x_1338; 
x_1338 = !lean_is_exclusive(x_1337);
if (x_1338 == 0)
{
lean_object* x_1339; 
x_1339 = lean_ctor_get(x_1337, 0);
lean_dec(x_1339);
lean_ctor_set(x_1337, 0, x_1330);
return x_1337;
}
else
{
lean_object* x_1340; lean_object* x_1341; 
x_1340 = lean_ctor_get(x_1337, 1);
lean_inc(x_1340);
lean_dec(x_1337);
x_1341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1341, 0, x_1330);
lean_ctor_set(x_1341, 1, x_1340);
return x_1341;
}
}
else
{
uint8_t x_1342; 
lean_dec(x_1333);
x_1342 = !lean_is_exclusive(x_1337);
if (x_1342 == 0)
{
lean_object* x_1343; lean_object* x_1344; uint8_t x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
x_1343 = lean_ctor_get(x_1337, 0);
x_1344 = lean_io_error_to_string(x_1343);
x_1345 = 3;
x_1346 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1346, 0, x_1344);
lean_ctor_set_uint8(x_1346, sizeof(void*)*1, x_1345);
x_1347 = lean_array_get_size(x_1334);
x_1348 = lean_array_push(x_1334, x_1346);
lean_ctor_set_tag(x_1330, 1);
lean_ctor_set(x_1330, 1, x_1348);
lean_ctor_set(x_1330, 0, x_1347);
lean_ctor_set_tag(x_1337, 0);
lean_ctor_set(x_1337, 0, x_1330);
return x_1337;
}
else
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; uint8_t x_1352; lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
x_1349 = lean_ctor_get(x_1337, 0);
x_1350 = lean_ctor_get(x_1337, 1);
lean_inc(x_1350);
lean_inc(x_1349);
lean_dec(x_1337);
x_1351 = lean_io_error_to_string(x_1349);
x_1352 = 3;
x_1353 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1353, 0, x_1351);
lean_ctor_set_uint8(x_1353, sizeof(void*)*1, x_1352);
x_1354 = lean_array_get_size(x_1334);
x_1355 = lean_array_push(x_1334, x_1353);
lean_ctor_set_tag(x_1330, 1);
lean_ctor_set(x_1330, 1, x_1355);
lean_ctor_set(x_1330, 0, x_1354);
x_1356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1356, 0, x_1330);
lean_ctor_set(x_1356, 1, x_1350);
return x_1356;
}
}
}
else
{
uint8_t x_1357; 
lean_dec(x_1333);
lean_dec(x_1318);
x_1357 = !lean_is_exclusive(x_1335);
if (x_1357 == 0)
{
lean_object* x_1358; lean_object* x_1359; uint8_t x_1360; lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
x_1358 = lean_ctor_get(x_1335, 0);
x_1359 = lean_io_error_to_string(x_1358);
x_1360 = 3;
x_1361 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1361, 0, x_1359);
lean_ctor_set_uint8(x_1361, sizeof(void*)*1, x_1360);
x_1362 = lean_array_get_size(x_1334);
x_1363 = lean_array_push(x_1334, x_1361);
lean_ctor_set_tag(x_1330, 1);
lean_ctor_set(x_1330, 1, x_1363);
lean_ctor_set(x_1330, 0, x_1362);
lean_ctor_set_tag(x_1335, 0);
lean_ctor_set(x_1335, 0, x_1330);
return x_1335;
}
else
{
lean_object* x_1364; lean_object* x_1365; lean_object* x_1366; uint8_t x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
x_1364 = lean_ctor_get(x_1335, 0);
x_1365 = lean_ctor_get(x_1335, 1);
lean_inc(x_1365);
lean_inc(x_1364);
lean_dec(x_1335);
x_1366 = lean_io_error_to_string(x_1364);
x_1367 = 3;
x_1368 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1368, 0, x_1366);
lean_ctor_set_uint8(x_1368, sizeof(void*)*1, x_1367);
x_1369 = lean_array_get_size(x_1334);
x_1370 = lean_array_push(x_1334, x_1368);
lean_ctor_set_tag(x_1330, 1);
lean_ctor_set(x_1330, 1, x_1370);
lean_ctor_set(x_1330, 0, x_1369);
x_1371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1371, 0, x_1330);
lean_ctor_set(x_1371, 1, x_1365);
return x_1371;
}
}
}
else
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; 
x_1372 = lean_ctor_get(x_1330, 0);
x_1373 = lean_ctor_get(x_1330, 1);
lean_inc(x_1373);
lean_inc(x_1372);
lean_dec(x_1330);
lean_inc(x_1372);
x_1374 = lean_write_module(x_1372, x_18, x_1331);
if (lean_obj_tag(x_1374) == 0)
{
lean_object* x_1375; lean_object* x_1376; 
x_1375 = lean_ctor_get(x_1374, 1);
lean_inc(x_1375);
lean_dec(x_1374);
x_1376 = lean_io_prim_handle_unlock(x_1318, x_1375);
lean_dec(x_1318);
if (lean_obj_tag(x_1376) == 0)
{
lean_object* x_1377; lean_object* x_1378; lean_object* x_1379; lean_object* x_1380; 
x_1377 = lean_ctor_get(x_1376, 1);
lean_inc(x_1377);
if (lean_is_exclusive(x_1376)) {
 lean_ctor_release(x_1376, 0);
 lean_ctor_release(x_1376, 1);
 x_1378 = x_1376;
} else {
 lean_dec_ref(x_1376);
 x_1378 = lean_box(0);
}
x_1379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1379, 0, x_1372);
lean_ctor_set(x_1379, 1, x_1373);
if (lean_is_scalar(x_1378)) {
 x_1380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1380 = x_1378;
}
lean_ctor_set(x_1380, 0, x_1379);
lean_ctor_set(x_1380, 1, x_1377);
return x_1380;
}
else
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; uint8_t x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; 
lean_dec(x_1372);
x_1381 = lean_ctor_get(x_1376, 0);
lean_inc(x_1381);
x_1382 = lean_ctor_get(x_1376, 1);
lean_inc(x_1382);
if (lean_is_exclusive(x_1376)) {
 lean_ctor_release(x_1376, 0);
 lean_ctor_release(x_1376, 1);
 x_1383 = x_1376;
} else {
 lean_dec_ref(x_1376);
 x_1383 = lean_box(0);
}
x_1384 = lean_io_error_to_string(x_1381);
x_1385 = 3;
x_1386 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1386, 0, x_1384);
lean_ctor_set_uint8(x_1386, sizeof(void*)*1, x_1385);
x_1387 = lean_array_get_size(x_1373);
x_1388 = lean_array_push(x_1373, x_1386);
x_1389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1389, 0, x_1387);
lean_ctor_set(x_1389, 1, x_1388);
if (lean_is_scalar(x_1383)) {
 x_1390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1390 = x_1383;
 lean_ctor_set_tag(x_1390, 0);
}
lean_ctor_set(x_1390, 0, x_1389);
lean_ctor_set(x_1390, 1, x_1382);
return x_1390;
}
}
else
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; lean_object* x_1394; uint8_t x_1395; lean_object* x_1396; lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; 
lean_dec(x_1372);
lean_dec(x_1318);
x_1391 = lean_ctor_get(x_1374, 0);
lean_inc(x_1391);
x_1392 = lean_ctor_get(x_1374, 1);
lean_inc(x_1392);
if (lean_is_exclusive(x_1374)) {
 lean_ctor_release(x_1374, 0);
 lean_ctor_release(x_1374, 1);
 x_1393 = x_1374;
} else {
 lean_dec_ref(x_1374);
 x_1393 = lean_box(0);
}
x_1394 = lean_io_error_to_string(x_1391);
x_1395 = 3;
x_1396 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1396, 0, x_1394);
lean_ctor_set_uint8(x_1396, sizeof(void*)*1, x_1395);
x_1397 = lean_array_get_size(x_1373);
x_1398 = lean_array_push(x_1373, x_1396);
x_1399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1399, 0, x_1397);
lean_ctor_set(x_1399, 1, x_1398);
if (lean_is_scalar(x_1393)) {
 x_1400 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1400 = x_1393;
 lean_ctor_set_tag(x_1400, 0);
}
lean_ctor_set(x_1400, 0, x_1399);
lean_ctor_set(x_1400, 1, x_1392);
return x_1400;
}
}
}
else
{
uint8_t x_1401; 
lean_dec(x_1318);
lean_dec(x_18);
x_1401 = !lean_is_exclusive(x_1329);
if (x_1401 == 0)
{
lean_object* x_1402; uint8_t x_1403; 
x_1402 = lean_ctor_get(x_1329, 0);
lean_dec(x_1402);
x_1403 = !lean_is_exclusive(x_1330);
if (x_1403 == 0)
{
return x_1329;
}
else
{
lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_1404 = lean_ctor_get(x_1330, 0);
x_1405 = lean_ctor_get(x_1330, 1);
lean_inc(x_1405);
lean_inc(x_1404);
lean_dec(x_1330);
x_1406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1406, 0, x_1404);
lean_ctor_set(x_1406, 1, x_1405);
lean_ctor_set(x_1329, 0, x_1406);
return x_1329;
}
}
else
{
lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; 
x_1407 = lean_ctor_get(x_1329, 1);
lean_inc(x_1407);
lean_dec(x_1329);
x_1408 = lean_ctor_get(x_1330, 0);
lean_inc(x_1408);
x_1409 = lean_ctor_get(x_1330, 1);
lean_inc(x_1409);
if (lean_is_exclusive(x_1330)) {
 lean_ctor_release(x_1330, 0);
 lean_ctor_release(x_1330, 1);
 x_1410 = x_1330;
} else {
 lean_dec_ref(x_1330);
 x_1410 = lean_box(0);
}
if (lean_is_scalar(x_1410)) {
 x_1411 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1411 = x_1410;
}
lean_ctor_set(x_1411, 0, x_1408);
lean_ctor_set(x_1411, 1, x_1409);
x_1412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1412, 0, x_1411);
lean_ctor_set(x_1412, 1, x_1407);
return x_1412;
}
}
}
else
{
uint8_t x_1413; 
lean_dec(x_1318);
lean_dec(x_18);
x_1413 = !lean_is_exclusive(x_1329);
if (x_1413 == 0)
{
return x_1329;
}
else
{
lean_object* x_1414; lean_object* x_1415; lean_object* x_1416; 
x_1414 = lean_ctor_get(x_1329, 0);
x_1415 = lean_ctor_get(x_1329, 1);
lean_inc(x_1415);
lean_inc(x_1414);
lean_dec(x_1329);
x_1416 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1416, 0, x_1414);
lean_ctor_set(x_1416, 1, x_1415);
return x_1416;
}
}
}
else
{
uint8_t x_1417; 
lean_dec(x_1324);
lean_dec(x_1318);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1417 = !lean_is_exclusive(x_1325);
if (x_1417 == 0)
{
lean_object* x_1418; 
x_1418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1418, 0, x_1325);
lean_ctor_set(x_1418, 1, x_1326);
return x_1418;
}
else
{
lean_object* x_1419; lean_object* x_1420; lean_object* x_1421; lean_object* x_1422; 
x_1419 = lean_ctor_get(x_1325, 0);
x_1420 = lean_ctor_get(x_1325, 1);
lean_inc(x_1420);
lean_inc(x_1419);
lean_dec(x_1325);
x_1421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1421, 0, x_1419);
lean_ctor_set(x_1421, 1, x_1420);
x_1422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1422, 0, x_1421);
lean_ctor_set(x_1422, 1, x_1326);
return x_1422;
}
}
}
block_1632:
{
lean_object* x_1426; 
x_1426 = lean_ctor_get(x_1424, 0);
lean_inc(x_1426);
if (lean_obj_tag(x_1426) == 0)
{
lean_object* x_1427; 
x_1427 = lean_ctor_get(x_1426, 0);
lean_inc(x_1427);
lean_dec(x_1426);
if (lean_obj_tag(x_1427) == 11)
{
uint8_t x_1428; 
lean_dec(x_1427);
lean_dec(x_21);
x_1428 = !lean_is_exclusive(x_1424);
if (x_1428 == 0)
{
lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1432; lean_object* x_1433; lean_object* x_1434; lean_object* x_1435; lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; 
x_1429 = lean_ctor_get(x_1424, 1);
x_1430 = lean_ctor_get(x_1424, 0);
lean_dec(x_1430);
x_1431 = lean_ctor_get(x_1, 0);
lean_inc(x_1431);
x_1432 = l_Lake_Env_leanGithash(x_1431);
lean_dec(x_1431);
x_1433 = l_System_Platform_target;
lean_inc(x_1324);
x_1434 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1434, 0, x_1433);
lean_ctor_set(x_1434, 1, x_1432);
lean_ctor_set(x_1434, 2, x_27);
lean_ctor_set(x_1434, 3, x_1324);
x_1435 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1434);
x_1436 = lean_unsigned_to_nat(80u);
x_1437 = l_Lean_Json_pretty(x_1435, x_1436);
x_1438 = l_IO_FS_Handle_putStrLn(x_1318, x_1437, x_1425);
if (lean_obj_tag(x_1438) == 0)
{
lean_object* x_1439; lean_object* x_1440; 
x_1439 = lean_ctor_get(x_1438, 1);
lean_inc(x_1439);
lean_dec(x_1438);
x_1440 = lean_io_prim_handle_truncate(x_1318, x_1439);
if (lean_obj_tag(x_1440) == 0)
{
lean_object* x_1441; lean_object* x_1442; 
x_1441 = lean_ctor_get(x_1440, 0);
lean_inc(x_1441);
x_1442 = lean_ctor_get(x_1440, 1);
lean_inc(x_1442);
lean_dec(x_1440);
lean_ctor_set(x_1424, 0, x_1441);
x_1325 = x_1424;
x_1326 = x_1442;
goto block_1423;
}
else
{
lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; uint8_t x_1446; lean_object* x_1447; lean_object* x_1448; lean_object* x_1449; 
x_1443 = lean_ctor_get(x_1440, 0);
lean_inc(x_1443);
x_1444 = lean_ctor_get(x_1440, 1);
lean_inc(x_1444);
lean_dec(x_1440);
x_1445 = lean_io_error_to_string(x_1443);
x_1446 = 3;
x_1447 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1447, 0, x_1445);
lean_ctor_set_uint8(x_1447, sizeof(void*)*1, x_1446);
x_1448 = lean_array_get_size(x_1429);
x_1449 = lean_array_push(x_1429, x_1447);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1449);
lean_ctor_set(x_1424, 0, x_1448);
x_1325 = x_1424;
x_1326 = x_1444;
goto block_1423;
}
}
else
{
uint8_t x_1450; 
lean_dec(x_1324);
lean_dec(x_1318);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1450 = !lean_is_exclusive(x_1438);
if (x_1450 == 0)
{
lean_object* x_1451; lean_object* x_1452; uint8_t x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; 
x_1451 = lean_ctor_get(x_1438, 0);
x_1452 = lean_io_error_to_string(x_1451);
x_1453 = 3;
x_1454 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1454, 0, x_1452);
lean_ctor_set_uint8(x_1454, sizeof(void*)*1, x_1453);
x_1455 = lean_array_get_size(x_1429);
x_1456 = lean_array_push(x_1429, x_1454);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1456);
lean_ctor_set(x_1424, 0, x_1455);
lean_ctor_set_tag(x_1438, 0);
lean_ctor_set(x_1438, 0, x_1424);
return x_1438;
}
else
{
lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; uint8_t x_1460; lean_object* x_1461; lean_object* x_1462; lean_object* x_1463; lean_object* x_1464; 
x_1457 = lean_ctor_get(x_1438, 0);
x_1458 = lean_ctor_get(x_1438, 1);
lean_inc(x_1458);
lean_inc(x_1457);
lean_dec(x_1438);
x_1459 = lean_io_error_to_string(x_1457);
x_1460 = 3;
x_1461 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1461, 0, x_1459);
lean_ctor_set_uint8(x_1461, sizeof(void*)*1, x_1460);
x_1462 = lean_array_get_size(x_1429);
x_1463 = lean_array_push(x_1429, x_1461);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1463);
lean_ctor_set(x_1424, 0, x_1462);
x_1464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1464, 0, x_1424);
lean_ctor_set(x_1464, 1, x_1458);
return x_1464;
}
}
}
else
{
lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; 
x_1465 = lean_ctor_get(x_1424, 1);
lean_inc(x_1465);
lean_dec(x_1424);
x_1466 = lean_ctor_get(x_1, 0);
lean_inc(x_1466);
x_1467 = l_Lake_Env_leanGithash(x_1466);
lean_dec(x_1466);
x_1468 = l_System_Platform_target;
lean_inc(x_1324);
x_1469 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1469, 0, x_1468);
lean_ctor_set(x_1469, 1, x_1467);
lean_ctor_set(x_1469, 2, x_27);
lean_ctor_set(x_1469, 3, x_1324);
x_1470 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1469);
x_1471 = lean_unsigned_to_nat(80u);
x_1472 = l_Lean_Json_pretty(x_1470, x_1471);
x_1473 = l_IO_FS_Handle_putStrLn(x_1318, x_1472, x_1425);
if (lean_obj_tag(x_1473) == 0)
{
lean_object* x_1474; lean_object* x_1475; 
x_1474 = lean_ctor_get(x_1473, 1);
lean_inc(x_1474);
lean_dec(x_1473);
x_1475 = lean_io_prim_handle_truncate(x_1318, x_1474);
if (lean_obj_tag(x_1475) == 0)
{
lean_object* x_1476; lean_object* x_1477; lean_object* x_1478; 
x_1476 = lean_ctor_get(x_1475, 0);
lean_inc(x_1476);
x_1477 = lean_ctor_get(x_1475, 1);
lean_inc(x_1477);
lean_dec(x_1475);
x_1478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1478, 0, x_1476);
lean_ctor_set(x_1478, 1, x_1465);
x_1325 = x_1478;
x_1326 = x_1477;
goto block_1423;
}
else
{
lean_object* x_1479; lean_object* x_1480; lean_object* x_1481; uint8_t x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; 
x_1479 = lean_ctor_get(x_1475, 0);
lean_inc(x_1479);
x_1480 = lean_ctor_get(x_1475, 1);
lean_inc(x_1480);
lean_dec(x_1475);
x_1481 = lean_io_error_to_string(x_1479);
x_1482 = 3;
x_1483 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1483, 0, x_1481);
lean_ctor_set_uint8(x_1483, sizeof(void*)*1, x_1482);
x_1484 = lean_array_get_size(x_1465);
x_1485 = lean_array_push(x_1465, x_1483);
x_1486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1486, 0, x_1484);
lean_ctor_set(x_1486, 1, x_1485);
x_1325 = x_1486;
x_1326 = x_1480;
goto block_1423;
}
}
else
{
lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; uint8_t x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; lean_object* x_1495; lean_object* x_1496; 
lean_dec(x_1324);
lean_dec(x_1318);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1487 = lean_ctor_get(x_1473, 0);
lean_inc(x_1487);
x_1488 = lean_ctor_get(x_1473, 1);
lean_inc(x_1488);
if (lean_is_exclusive(x_1473)) {
 lean_ctor_release(x_1473, 0);
 lean_ctor_release(x_1473, 1);
 x_1489 = x_1473;
} else {
 lean_dec_ref(x_1473);
 x_1489 = lean_box(0);
}
x_1490 = lean_io_error_to_string(x_1487);
x_1491 = 3;
x_1492 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1492, 0, x_1490);
lean_ctor_set_uint8(x_1492, sizeof(void*)*1, x_1491);
x_1493 = lean_array_get_size(x_1465);
x_1494 = lean_array_push(x_1465, x_1492);
x_1495 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1495, 0, x_1493);
lean_ctor_set(x_1495, 1, x_1494);
if (lean_is_scalar(x_1489)) {
 x_1496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1496 = x_1489;
 lean_ctor_set_tag(x_1496, 0);
}
lean_ctor_set(x_1496, 0, x_1495);
lean_ctor_set(x_1496, 1, x_1488);
return x_1496;
}
}
}
else
{
uint8_t x_1497; 
lean_dec(x_1324);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1497 = !lean_is_exclusive(x_1424);
if (x_1497 == 0)
{
lean_object* x_1498; lean_object* x_1499; lean_object* x_1500; uint8_t x_1501; lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
x_1498 = lean_ctor_get(x_1424, 1);
x_1499 = lean_ctor_get(x_1424, 0);
lean_dec(x_1499);
x_1500 = lean_io_error_to_string(x_1427);
x_1501 = 3;
x_1502 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1502, 0, x_1500);
lean_ctor_set_uint8(x_1502, sizeof(void*)*1, x_1501);
x_1503 = lean_array_get_size(x_1498);
x_1504 = lean_array_push(x_1498, x_1502);
x_1505 = lean_io_prim_handle_unlock(x_1318, x_1425);
lean_dec(x_1318);
if (lean_obj_tag(x_1505) == 0)
{
lean_object* x_1506; lean_object* x_1507; 
x_1506 = lean_ctor_get(x_1505, 1);
lean_inc(x_1506);
lean_dec(x_1505);
x_1507 = lean_io_remove_file(x_21, x_1506);
lean_dec(x_21);
if (lean_obj_tag(x_1507) == 0)
{
uint8_t x_1508; 
x_1508 = !lean_is_exclusive(x_1507);
if (x_1508 == 0)
{
lean_object* x_1509; 
x_1509 = lean_ctor_get(x_1507, 0);
lean_dec(x_1509);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1504);
lean_ctor_set(x_1424, 0, x_1503);
lean_ctor_set(x_1507, 0, x_1424);
return x_1507;
}
else
{
lean_object* x_1510; lean_object* x_1511; 
x_1510 = lean_ctor_get(x_1507, 1);
lean_inc(x_1510);
lean_dec(x_1507);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1504);
lean_ctor_set(x_1424, 0, x_1503);
x_1511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1511, 0, x_1424);
lean_ctor_set(x_1511, 1, x_1510);
return x_1511;
}
}
else
{
uint8_t x_1512; 
x_1512 = !lean_is_exclusive(x_1507);
if (x_1512 == 0)
{
lean_object* x_1513; lean_object* x_1514; lean_object* x_1515; lean_object* x_1516; 
x_1513 = lean_ctor_get(x_1507, 0);
x_1514 = lean_io_error_to_string(x_1513);
x_1515 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1515, 0, x_1514);
lean_ctor_set_uint8(x_1515, sizeof(void*)*1, x_1501);
x_1516 = lean_array_push(x_1504, x_1515);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1516);
lean_ctor_set(x_1424, 0, x_1503);
lean_ctor_set_tag(x_1507, 0);
lean_ctor_set(x_1507, 0, x_1424);
return x_1507;
}
else
{
lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; 
x_1517 = lean_ctor_get(x_1507, 0);
x_1518 = lean_ctor_get(x_1507, 1);
lean_inc(x_1518);
lean_inc(x_1517);
lean_dec(x_1507);
x_1519 = lean_io_error_to_string(x_1517);
x_1520 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1520, 0, x_1519);
lean_ctor_set_uint8(x_1520, sizeof(void*)*1, x_1501);
x_1521 = lean_array_push(x_1504, x_1520);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1521);
lean_ctor_set(x_1424, 0, x_1503);
x_1522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1522, 0, x_1424);
lean_ctor_set(x_1522, 1, x_1518);
return x_1522;
}
}
}
else
{
uint8_t x_1523; 
lean_dec(x_21);
x_1523 = !lean_is_exclusive(x_1505);
if (x_1523 == 0)
{
lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; 
x_1524 = lean_ctor_get(x_1505, 0);
x_1525 = lean_io_error_to_string(x_1524);
x_1526 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1526, 0, x_1525);
lean_ctor_set_uint8(x_1526, sizeof(void*)*1, x_1501);
x_1527 = lean_array_push(x_1504, x_1526);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1527);
lean_ctor_set(x_1424, 0, x_1503);
lean_ctor_set_tag(x_1505, 0);
lean_ctor_set(x_1505, 0, x_1424);
return x_1505;
}
else
{
lean_object* x_1528; lean_object* x_1529; lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; 
x_1528 = lean_ctor_get(x_1505, 0);
x_1529 = lean_ctor_get(x_1505, 1);
lean_inc(x_1529);
lean_inc(x_1528);
lean_dec(x_1505);
x_1530 = lean_io_error_to_string(x_1528);
x_1531 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1531, 0, x_1530);
lean_ctor_set_uint8(x_1531, sizeof(void*)*1, x_1501);
x_1532 = lean_array_push(x_1504, x_1531);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1532);
lean_ctor_set(x_1424, 0, x_1503);
x_1533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1533, 0, x_1424);
lean_ctor_set(x_1533, 1, x_1529);
return x_1533;
}
}
}
else
{
lean_object* x_1534; lean_object* x_1535; uint8_t x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; 
x_1534 = lean_ctor_get(x_1424, 1);
lean_inc(x_1534);
lean_dec(x_1424);
x_1535 = lean_io_error_to_string(x_1427);
x_1536 = 3;
x_1537 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1537, 0, x_1535);
lean_ctor_set_uint8(x_1537, sizeof(void*)*1, x_1536);
x_1538 = lean_array_get_size(x_1534);
x_1539 = lean_array_push(x_1534, x_1537);
x_1540 = lean_io_prim_handle_unlock(x_1318, x_1425);
lean_dec(x_1318);
if (lean_obj_tag(x_1540) == 0)
{
lean_object* x_1541; lean_object* x_1542; 
x_1541 = lean_ctor_get(x_1540, 1);
lean_inc(x_1541);
lean_dec(x_1540);
x_1542 = lean_io_remove_file(x_21, x_1541);
lean_dec(x_21);
if (lean_obj_tag(x_1542) == 0)
{
lean_object* x_1543; lean_object* x_1544; lean_object* x_1545; lean_object* x_1546; 
x_1543 = lean_ctor_get(x_1542, 1);
lean_inc(x_1543);
if (lean_is_exclusive(x_1542)) {
 lean_ctor_release(x_1542, 0);
 lean_ctor_release(x_1542, 1);
 x_1544 = x_1542;
} else {
 lean_dec_ref(x_1542);
 x_1544 = lean_box(0);
}
x_1545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1545, 0, x_1538);
lean_ctor_set(x_1545, 1, x_1539);
if (lean_is_scalar(x_1544)) {
 x_1546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1546 = x_1544;
}
lean_ctor_set(x_1546, 0, x_1545);
lean_ctor_set(x_1546, 1, x_1543);
return x_1546;
}
else
{
lean_object* x_1547; lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
x_1547 = lean_ctor_get(x_1542, 0);
lean_inc(x_1547);
x_1548 = lean_ctor_get(x_1542, 1);
lean_inc(x_1548);
if (lean_is_exclusive(x_1542)) {
 lean_ctor_release(x_1542, 0);
 lean_ctor_release(x_1542, 1);
 x_1549 = x_1542;
} else {
 lean_dec_ref(x_1542);
 x_1549 = lean_box(0);
}
x_1550 = lean_io_error_to_string(x_1547);
x_1551 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1551, 0, x_1550);
lean_ctor_set_uint8(x_1551, sizeof(void*)*1, x_1536);
x_1552 = lean_array_push(x_1539, x_1551);
x_1553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1553, 0, x_1538);
lean_ctor_set(x_1553, 1, x_1552);
if (lean_is_scalar(x_1549)) {
 x_1554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1554 = x_1549;
 lean_ctor_set_tag(x_1554, 0);
}
lean_ctor_set(x_1554, 0, x_1553);
lean_ctor_set(x_1554, 1, x_1548);
return x_1554;
}
}
else
{
lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; lean_object* x_1562; 
lean_dec(x_21);
x_1555 = lean_ctor_get(x_1540, 0);
lean_inc(x_1555);
x_1556 = lean_ctor_get(x_1540, 1);
lean_inc(x_1556);
if (lean_is_exclusive(x_1540)) {
 lean_ctor_release(x_1540, 0);
 lean_ctor_release(x_1540, 1);
 x_1557 = x_1540;
} else {
 lean_dec_ref(x_1540);
 x_1557 = lean_box(0);
}
x_1558 = lean_io_error_to_string(x_1555);
x_1559 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1559, 0, x_1558);
lean_ctor_set_uint8(x_1559, sizeof(void*)*1, x_1536);
x_1560 = lean_array_push(x_1539, x_1559);
x_1561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1561, 0, x_1538);
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
}
}
else
{
uint8_t x_1563; 
lean_dec(x_1426);
lean_dec(x_21);
x_1563 = !lean_is_exclusive(x_1424);
if (x_1563 == 0)
{
lean_object* x_1564; lean_object* x_1565; lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; lean_object* x_1570; lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; 
x_1564 = lean_ctor_get(x_1424, 1);
x_1565 = lean_ctor_get(x_1424, 0);
lean_dec(x_1565);
x_1566 = lean_ctor_get(x_1, 0);
lean_inc(x_1566);
x_1567 = l_Lake_Env_leanGithash(x_1566);
lean_dec(x_1566);
x_1568 = l_System_Platform_target;
lean_inc(x_1324);
x_1569 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1569, 0, x_1568);
lean_ctor_set(x_1569, 1, x_1567);
lean_ctor_set(x_1569, 2, x_27);
lean_ctor_set(x_1569, 3, x_1324);
x_1570 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1569);
x_1571 = lean_unsigned_to_nat(80u);
x_1572 = l_Lean_Json_pretty(x_1570, x_1571);
x_1573 = l_IO_FS_Handle_putStrLn(x_1318, x_1572, x_1425);
if (lean_obj_tag(x_1573) == 0)
{
lean_object* x_1574; lean_object* x_1575; 
x_1574 = lean_ctor_get(x_1573, 1);
lean_inc(x_1574);
lean_dec(x_1573);
x_1575 = lean_io_prim_handle_truncate(x_1318, x_1574);
if (lean_obj_tag(x_1575) == 0)
{
lean_object* x_1576; lean_object* x_1577; 
x_1576 = lean_ctor_get(x_1575, 0);
lean_inc(x_1576);
x_1577 = lean_ctor_get(x_1575, 1);
lean_inc(x_1577);
lean_dec(x_1575);
lean_ctor_set(x_1424, 0, x_1576);
x_1325 = x_1424;
x_1326 = x_1577;
goto block_1423;
}
else
{
lean_object* x_1578; lean_object* x_1579; lean_object* x_1580; uint8_t x_1581; lean_object* x_1582; lean_object* x_1583; lean_object* x_1584; 
x_1578 = lean_ctor_get(x_1575, 0);
lean_inc(x_1578);
x_1579 = lean_ctor_get(x_1575, 1);
lean_inc(x_1579);
lean_dec(x_1575);
x_1580 = lean_io_error_to_string(x_1578);
x_1581 = 3;
x_1582 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1582, 0, x_1580);
lean_ctor_set_uint8(x_1582, sizeof(void*)*1, x_1581);
x_1583 = lean_array_get_size(x_1564);
x_1584 = lean_array_push(x_1564, x_1582);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1584);
lean_ctor_set(x_1424, 0, x_1583);
x_1325 = x_1424;
x_1326 = x_1579;
goto block_1423;
}
}
else
{
uint8_t x_1585; 
lean_dec(x_1324);
lean_dec(x_1318);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1585 = !lean_is_exclusive(x_1573);
if (x_1585 == 0)
{
lean_object* x_1586; lean_object* x_1587; uint8_t x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; 
x_1586 = lean_ctor_get(x_1573, 0);
x_1587 = lean_io_error_to_string(x_1586);
x_1588 = 3;
x_1589 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1589, 0, x_1587);
lean_ctor_set_uint8(x_1589, sizeof(void*)*1, x_1588);
x_1590 = lean_array_get_size(x_1564);
x_1591 = lean_array_push(x_1564, x_1589);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1591);
lean_ctor_set(x_1424, 0, x_1590);
lean_ctor_set_tag(x_1573, 0);
lean_ctor_set(x_1573, 0, x_1424);
return x_1573;
}
else
{
lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; uint8_t x_1595; lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
x_1592 = lean_ctor_get(x_1573, 0);
x_1593 = lean_ctor_get(x_1573, 1);
lean_inc(x_1593);
lean_inc(x_1592);
lean_dec(x_1573);
x_1594 = lean_io_error_to_string(x_1592);
x_1595 = 3;
x_1596 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1596, 0, x_1594);
lean_ctor_set_uint8(x_1596, sizeof(void*)*1, x_1595);
x_1597 = lean_array_get_size(x_1564);
x_1598 = lean_array_push(x_1564, x_1596);
lean_ctor_set_tag(x_1424, 1);
lean_ctor_set(x_1424, 1, x_1598);
lean_ctor_set(x_1424, 0, x_1597);
x_1599 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1599, 0, x_1424);
lean_ctor_set(x_1599, 1, x_1593);
return x_1599;
}
}
}
else
{
lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; 
x_1600 = lean_ctor_get(x_1424, 1);
lean_inc(x_1600);
lean_dec(x_1424);
x_1601 = lean_ctor_get(x_1, 0);
lean_inc(x_1601);
x_1602 = l_Lake_Env_leanGithash(x_1601);
lean_dec(x_1601);
x_1603 = l_System_Platform_target;
lean_inc(x_1324);
x_1604 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1604, 0, x_1603);
lean_ctor_set(x_1604, 1, x_1602);
lean_ctor_set(x_1604, 2, x_27);
lean_ctor_set(x_1604, 3, x_1324);
x_1605 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1604);
x_1606 = lean_unsigned_to_nat(80u);
x_1607 = l_Lean_Json_pretty(x_1605, x_1606);
x_1608 = l_IO_FS_Handle_putStrLn(x_1318, x_1607, x_1425);
if (lean_obj_tag(x_1608) == 0)
{
lean_object* x_1609; lean_object* x_1610; 
x_1609 = lean_ctor_get(x_1608, 1);
lean_inc(x_1609);
lean_dec(x_1608);
x_1610 = lean_io_prim_handle_truncate(x_1318, x_1609);
if (lean_obj_tag(x_1610) == 0)
{
lean_object* x_1611; lean_object* x_1612; lean_object* x_1613; 
x_1611 = lean_ctor_get(x_1610, 0);
lean_inc(x_1611);
x_1612 = lean_ctor_get(x_1610, 1);
lean_inc(x_1612);
lean_dec(x_1610);
x_1613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1613, 0, x_1611);
lean_ctor_set(x_1613, 1, x_1600);
x_1325 = x_1613;
x_1326 = x_1612;
goto block_1423;
}
else
{
lean_object* x_1614; lean_object* x_1615; lean_object* x_1616; uint8_t x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; 
x_1614 = lean_ctor_get(x_1610, 0);
lean_inc(x_1614);
x_1615 = lean_ctor_get(x_1610, 1);
lean_inc(x_1615);
lean_dec(x_1610);
x_1616 = lean_io_error_to_string(x_1614);
x_1617 = 3;
x_1618 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1618, 0, x_1616);
lean_ctor_set_uint8(x_1618, sizeof(void*)*1, x_1617);
x_1619 = lean_array_get_size(x_1600);
x_1620 = lean_array_push(x_1600, x_1618);
x_1621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1621, 0, x_1619);
lean_ctor_set(x_1621, 1, x_1620);
x_1325 = x_1621;
x_1326 = x_1615;
goto block_1423;
}
}
else
{
lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; uint8_t x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; lean_object* x_1630; lean_object* x_1631; 
lean_dec(x_1324);
lean_dec(x_1318);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1622 = lean_ctor_get(x_1608, 0);
lean_inc(x_1622);
x_1623 = lean_ctor_get(x_1608, 1);
lean_inc(x_1623);
if (lean_is_exclusive(x_1608)) {
 lean_ctor_release(x_1608, 0);
 lean_ctor_release(x_1608, 1);
 x_1624 = x_1608;
} else {
 lean_dec_ref(x_1608);
 x_1624 = lean_box(0);
}
x_1625 = lean_io_error_to_string(x_1622);
x_1626 = 3;
x_1627 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1627, 0, x_1625);
lean_ctor_set_uint8(x_1627, sizeof(void*)*1, x_1626);
x_1628 = lean_array_get_size(x_1600);
x_1629 = lean_array_push(x_1600, x_1627);
x_1630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1630, 0, x_1628);
lean_ctor_set(x_1630, 1, x_1629);
if (lean_is_scalar(x_1624)) {
 x_1631 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1631 = x_1624;
 lean_ctor_set_tag(x_1631, 0);
}
lean_ctor_set(x_1631, 0, x_1630);
lean_ctor_set(x_1631, 1, x_1623);
return x_1631;
}
}
}
}
}
else
{
lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1696; lean_object* x_1697; lean_object* x_1797; 
x_1640 = lean_ctor_get(x_1320, 1);
lean_inc(x_1640);
lean_dec(x_1320);
x_1641 = lean_ctor_get(x_1, 8);
lean_inc(x_1641);
x_1797 = lean_io_remove_file(x_18, x_1321);
if (lean_obj_tag(x_1797) == 0)
{
lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; 
x_1798 = lean_ctor_get(x_1797, 0);
lean_inc(x_1798);
x_1799 = lean_ctor_get(x_1797, 1);
lean_inc(x_1799);
lean_dec(x_1797);
if (lean_is_scalar(x_1319)) {
 x_1800 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1800 = x_1319;
}
lean_ctor_set(x_1800, 0, x_1798);
x_1801 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1801, 0, x_1800);
lean_ctor_set(x_1801, 1, x_1640);
x_1696 = x_1801;
x_1697 = x_1799;
goto block_1796;
}
else
{
lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; 
x_1802 = lean_ctor_get(x_1797, 0);
lean_inc(x_1802);
x_1803 = lean_ctor_get(x_1797, 1);
lean_inc(x_1803);
lean_dec(x_1797);
if (lean_is_scalar(x_1319)) {
 x_1804 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1804 = x_1319;
 lean_ctor_set_tag(x_1804, 0);
}
lean_ctor_set(x_1804, 0, x_1802);
x_1805 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1805, 0, x_1804);
lean_ctor_set(x_1805, 1, x_1640);
x_1696 = x_1805;
x_1697 = x_1803;
goto block_1796;
}
block_1695:
{
if (lean_obj_tag(x_1642) == 0)
{
lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; 
x_1644 = lean_ctor_get(x_1642, 1);
lean_inc(x_1644);
lean_dec(x_1642);
x_1645 = lean_ctor_get(x_1, 9);
lean_inc(x_1645);
lean_dec(x_1);
x_1646 = l_Lake_elabConfigFile(x_13, x_1641, x_1645, x_4, x_1644, x_1643);
if (lean_obj_tag(x_1646) == 0)
{
lean_object* x_1647; 
x_1647 = lean_ctor_get(x_1646, 0);
lean_inc(x_1647);
if (lean_obj_tag(x_1647) == 0)
{
lean_object* x_1648; lean_object* x_1649; lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; 
x_1648 = lean_ctor_get(x_1646, 1);
lean_inc(x_1648);
lean_dec(x_1646);
x_1649 = lean_ctor_get(x_1647, 0);
lean_inc(x_1649);
x_1650 = lean_ctor_get(x_1647, 1);
lean_inc(x_1650);
if (lean_is_exclusive(x_1647)) {
 lean_ctor_release(x_1647, 0);
 lean_ctor_release(x_1647, 1);
 x_1651 = x_1647;
} else {
 lean_dec_ref(x_1647);
 x_1651 = lean_box(0);
}
lean_inc(x_1649);
x_1652 = lean_write_module(x_1649, x_18, x_1648);
if (lean_obj_tag(x_1652) == 0)
{
lean_object* x_1653; lean_object* x_1654; 
x_1653 = lean_ctor_get(x_1652, 1);
lean_inc(x_1653);
lean_dec(x_1652);
x_1654 = lean_io_prim_handle_unlock(x_1318, x_1653);
lean_dec(x_1318);
if (lean_obj_tag(x_1654) == 0)
{
lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; 
x_1655 = lean_ctor_get(x_1654, 1);
lean_inc(x_1655);
if (lean_is_exclusive(x_1654)) {
 lean_ctor_release(x_1654, 0);
 lean_ctor_release(x_1654, 1);
 x_1656 = x_1654;
} else {
 lean_dec_ref(x_1654);
 x_1656 = lean_box(0);
}
if (lean_is_scalar(x_1651)) {
 x_1657 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1657 = x_1651;
}
lean_ctor_set(x_1657, 0, x_1649);
lean_ctor_set(x_1657, 1, x_1650);
if (lean_is_scalar(x_1656)) {
 x_1658 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1658 = x_1656;
}
lean_ctor_set(x_1658, 0, x_1657);
lean_ctor_set(x_1658, 1, x_1655);
return x_1658;
}
else
{
lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; uint8_t x_1663; lean_object* x_1664; lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; 
lean_dec(x_1649);
x_1659 = lean_ctor_get(x_1654, 0);
lean_inc(x_1659);
x_1660 = lean_ctor_get(x_1654, 1);
lean_inc(x_1660);
if (lean_is_exclusive(x_1654)) {
 lean_ctor_release(x_1654, 0);
 lean_ctor_release(x_1654, 1);
 x_1661 = x_1654;
} else {
 lean_dec_ref(x_1654);
 x_1661 = lean_box(0);
}
x_1662 = lean_io_error_to_string(x_1659);
x_1663 = 3;
x_1664 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1664, 0, x_1662);
lean_ctor_set_uint8(x_1664, sizeof(void*)*1, x_1663);
x_1665 = lean_array_get_size(x_1650);
x_1666 = lean_array_push(x_1650, x_1664);
if (lean_is_scalar(x_1651)) {
 x_1667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1667 = x_1651;
 lean_ctor_set_tag(x_1667, 1);
}
lean_ctor_set(x_1667, 0, x_1665);
lean_ctor_set(x_1667, 1, x_1666);
if (lean_is_scalar(x_1661)) {
 x_1668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1668 = x_1661;
 lean_ctor_set_tag(x_1668, 0);
}
lean_ctor_set(x_1668, 0, x_1667);
lean_ctor_set(x_1668, 1, x_1660);
return x_1668;
}
}
else
{
lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; uint8_t x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; 
lean_dec(x_1649);
lean_dec(x_1318);
x_1669 = lean_ctor_get(x_1652, 0);
lean_inc(x_1669);
x_1670 = lean_ctor_get(x_1652, 1);
lean_inc(x_1670);
if (lean_is_exclusive(x_1652)) {
 lean_ctor_release(x_1652, 0);
 lean_ctor_release(x_1652, 1);
 x_1671 = x_1652;
} else {
 lean_dec_ref(x_1652);
 x_1671 = lean_box(0);
}
x_1672 = lean_io_error_to_string(x_1669);
x_1673 = 3;
x_1674 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1674, 0, x_1672);
lean_ctor_set_uint8(x_1674, sizeof(void*)*1, x_1673);
x_1675 = lean_array_get_size(x_1650);
x_1676 = lean_array_push(x_1650, x_1674);
if (lean_is_scalar(x_1651)) {
 x_1677 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1677 = x_1651;
 lean_ctor_set_tag(x_1677, 1);
}
lean_ctor_set(x_1677, 0, x_1675);
lean_ctor_set(x_1677, 1, x_1676);
if (lean_is_scalar(x_1671)) {
 x_1678 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1678 = x_1671;
 lean_ctor_set_tag(x_1678, 0);
}
lean_ctor_set(x_1678, 0, x_1677);
lean_ctor_set(x_1678, 1, x_1670);
return x_1678;
}
}
else
{
lean_object* x_1679; lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; 
lean_dec(x_1318);
lean_dec(x_18);
x_1679 = lean_ctor_get(x_1646, 1);
lean_inc(x_1679);
if (lean_is_exclusive(x_1646)) {
 lean_ctor_release(x_1646, 0);
 lean_ctor_release(x_1646, 1);
 x_1680 = x_1646;
} else {
 lean_dec_ref(x_1646);
 x_1680 = lean_box(0);
}
x_1681 = lean_ctor_get(x_1647, 0);
lean_inc(x_1681);
x_1682 = lean_ctor_get(x_1647, 1);
lean_inc(x_1682);
if (lean_is_exclusive(x_1647)) {
 lean_ctor_release(x_1647, 0);
 lean_ctor_release(x_1647, 1);
 x_1683 = x_1647;
} else {
 lean_dec_ref(x_1647);
 x_1683 = lean_box(0);
}
if (lean_is_scalar(x_1683)) {
 x_1684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1684 = x_1683;
}
lean_ctor_set(x_1684, 0, x_1681);
lean_ctor_set(x_1684, 1, x_1682);
if (lean_is_scalar(x_1680)) {
 x_1685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1685 = x_1680;
}
lean_ctor_set(x_1685, 0, x_1684);
lean_ctor_set(x_1685, 1, x_1679);
return x_1685;
}
}
else
{
lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; 
lean_dec(x_1318);
lean_dec(x_18);
x_1686 = lean_ctor_get(x_1646, 0);
lean_inc(x_1686);
x_1687 = lean_ctor_get(x_1646, 1);
lean_inc(x_1687);
if (lean_is_exclusive(x_1646)) {
 lean_ctor_release(x_1646, 0);
 lean_ctor_release(x_1646, 1);
 x_1688 = x_1646;
} else {
 lean_dec_ref(x_1646);
 x_1688 = lean_box(0);
}
if (lean_is_scalar(x_1688)) {
 x_1689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1689 = x_1688;
}
lean_ctor_set(x_1689, 0, x_1686);
lean_ctor_set(x_1689, 1, x_1687);
return x_1689;
}
}
else
{
lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; 
lean_dec(x_1641);
lean_dec(x_1318);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1690 = lean_ctor_get(x_1642, 0);
lean_inc(x_1690);
x_1691 = lean_ctor_get(x_1642, 1);
lean_inc(x_1691);
if (lean_is_exclusive(x_1642)) {
 lean_ctor_release(x_1642, 0);
 lean_ctor_release(x_1642, 1);
 x_1692 = x_1642;
} else {
 lean_dec_ref(x_1642);
 x_1692 = lean_box(0);
}
if (lean_is_scalar(x_1692)) {
 x_1693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1693 = x_1692;
}
lean_ctor_set(x_1693, 0, x_1690);
lean_ctor_set(x_1693, 1, x_1691);
x_1694 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1694, 0, x_1693);
lean_ctor_set(x_1694, 1, x_1643);
return x_1694;
}
}
block_1796:
{
lean_object* x_1698; 
x_1698 = lean_ctor_get(x_1696, 0);
lean_inc(x_1698);
if (lean_obj_tag(x_1698) == 0)
{
lean_object* x_1699; 
x_1699 = lean_ctor_get(x_1698, 0);
lean_inc(x_1699);
lean_dec(x_1698);
if (lean_obj_tag(x_1699) == 11)
{
lean_object* x_1700; lean_object* x_1701; lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; lean_object* x_1705; lean_object* x_1706; lean_object* x_1707; lean_object* x_1708; lean_object* x_1709; 
lean_dec(x_1699);
lean_dec(x_21);
x_1700 = lean_ctor_get(x_1696, 1);
lean_inc(x_1700);
if (lean_is_exclusive(x_1696)) {
 lean_ctor_release(x_1696, 0);
 lean_ctor_release(x_1696, 1);
 x_1701 = x_1696;
} else {
 lean_dec_ref(x_1696);
 x_1701 = lean_box(0);
}
x_1702 = lean_ctor_get(x_1, 0);
lean_inc(x_1702);
x_1703 = l_Lake_Env_leanGithash(x_1702);
lean_dec(x_1702);
x_1704 = l_System_Platform_target;
lean_inc(x_1641);
x_1705 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1705, 0, x_1704);
lean_ctor_set(x_1705, 1, x_1703);
lean_ctor_set(x_1705, 2, x_27);
lean_ctor_set(x_1705, 3, x_1641);
x_1706 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1705);
x_1707 = lean_unsigned_to_nat(80u);
x_1708 = l_Lean_Json_pretty(x_1706, x_1707);
x_1709 = l_IO_FS_Handle_putStrLn(x_1318, x_1708, x_1697);
if (lean_obj_tag(x_1709) == 0)
{
lean_object* x_1710; lean_object* x_1711; 
x_1710 = lean_ctor_get(x_1709, 1);
lean_inc(x_1710);
lean_dec(x_1709);
x_1711 = lean_io_prim_handle_truncate(x_1318, x_1710);
if (lean_obj_tag(x_1711) == 0)
{
lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; 
x_1712 = lean_ctor_get(x_1711, 0);
lean_inc(x_1712);
x_1713 = lean_ctor_get(x_1711, 1);
lean_inc(x_1713);
lean_dec(x_1711);
if (lean_is_scalar(x_1701)) {
 x_1714 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1714 = x_1701;
}
lean_ctor_set(x_1714, 0, x_1712);
lean_ctor_set(x_1714, 1, x_1700);
x_1642 = x_1714;
x_1643 = x_1713;
goto block_1695;
}
else
{
lean_object* x_1715; lean_object* x_1716; lean_object* x_1717; uint8_t x_1718; lean_object* x_1719; lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; 
x_1715 = lean_ctor_get(x_1711, 0);
lean_inc(x_1715);
x_1716 = lean_ctor_get(x_1711, 1);
lean_inc(x_1716);
lean_dec(x_1711);
x_1717 = lean_io_error_to_string(x_1715);
x_1718 = 3;
x_1719 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1719, 0, x_1717);
lean_ctor_set_uint8(x_1719, sizeof(void*)*1, x_1718);
x_1720 = lean_array_get_size(x_1700);
x_1721 = lean_array_push(x_1700, x_1719);
if (lean_is_scalar(x_1701)) {
 x_1722 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1722 = x_1701;
 lean_ctor_set_tag(x_1722, 1);
}
lean_ctor_set(x_1722, 0, x_1720);
lean_ctor_set(x_1722, 1, x_1721);
x_1642 = x_1722;
x_1643 = x_1716;
goto block_1695;
}
}
else
{
lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; uint8_t x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; 
lean_dec(x_1641);
lean_dec(x_1318);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1723 = lean_ctor_get(x_1709, 0);
lean_inc(x_1723);
x_1724 = lean_ctor_get(x_1709, 1);
lean_inc(x_1724);
if (lean_is_exclusive(x_1709)) {
 lean_ctor_release(x_1709, 0);
 lean_ctor_release(x_1709, 1);
 x_1725 = x_1709;
} else {
 lean_dec_ref(x_1709);
 x_1725 = lean_box(0);
}
x_1726 = lean_io_error_to_string(x_1723);
x_1727 = 3;
x_1728 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1728, 0, x_1726);
lean_ctor_set_uint8(x_1728, sizeof(void*)*1, x_1727);
x_1729 = lean_array_get_size(x_1700);
x_1730 = lean_array_push(x_1700, x_1728);
if (lean_is_scalar(x_1701)) {
 x_1731 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1731 = x_1701;
 lean_ctor_set_tag(x_1731, 1);
}
lean_ctor_set(x_1731, 0, x_1729);
lean_ctor_set(x_1731, 1, x_1730);
if (lean_is_scalar(x_1725)) {
 x_1732 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1732 = x_1725;
 lean_ctor_set_tag(x_1732, 0);
}
lean_ctor_set(x_1732, 0, x_1731);
lean_ctor_set(x_1732, 1, x_1724);
return x_1732;
}
}
else
{
lean_object* x_1733; lean_object* x_1734; lean_object* x_1735; uint8_t x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; 
lean_dec(x_1641);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1733 = lean_ctor_get(x_1696, 1);
lean_inc(x_1733);
if (lean_is_exclusive(x_1696)) {
 lean_ctor_release(x_1696, 0);
 lean_ctor_release(x_1696, 1);
 x_1734 = x_1696;
} else {
 lean_dec_ref(x_1696);
 x_1734 = lean_box(0);
}
x_1735 = lean_io_error_to_string(x_1699);
x_1736 = 3;
x_1737 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1737, 0, x_1735);
lean_ctor_set_uint8(x_1737, sizeof(void*)*1, x_1736);
x_1738 = lean_array_get_size(x_1733);
x_1739 = lean_array_push(x_1733, x_1737);
x_1740 = lean_io_prim_handle_unlock(x_1318, x_1697);
lean_dec(x_1318);
if (lean_obj_tag(x_1740) == 0)
{
lean_object* x_1741; lean_object* x_1742; 
x_1741 = lean_ctor_get(x_1740, 1);
lean_inc(x_1741);
lean_dec(x_1740);
x_1742 = lean_io_remove_file(x_21, x_1741);
lean_dec(x_21);
if (lean_obj_tag(x_1742) == 0)
{
lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; 
x_1743 = lean_ctor_get(x_1742, 1);
lean_inc(x_1743);
if (lean_is_exclusive(x_1742)) {
 lean_ctor_release(x_1742, 0);
 lean_ctor_release(x_1742, 1);
 x_1744 = x_1742;
} else {
 lean_dec_ref(x_1742);
 x_1744 = lean_box(0);
}
if (lean_is_scalar(x_1734)) {
 x_1745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1745 = x_1734;
 lean_ctor_set_tag(x_1745, 1);
}
lean_ctor_set(x_1745, 0, x_1738);
lean_ctor_set(x_1745, 1, x_1739);
if (lean_is_scalar(x_1744)) {
 x_1746 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1746 = x_1744;
}
lean_ctor_set(x_1746, 0, x_1745);
lean_ctor_set(x_1746, 1, x_1743);
return x_1746;
}
else
{
lean_object* x_1747; lean_object* x_1748; lean_object* x_1749; lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; lean_object* x_1753; lean_object* x_1754; 
x_1747 = lean_ctor_get(x_1742, 0);
lean_inc(x_1747);
x_1748 = lean_ctor_get(x_1742, 1);
lean_inc(x_1748);
if (lean_is_exclusive(x_1742)) {
 lean_ctor_release(x_1742, 0);
 lean_ctor_release(x_1742, 1);
 x_1749 = x_1742;
} else {
 lean_dec_ref(x_1742);
 x_1749 = lean_box(0);
}
x_1750 = lean_io_error_to_string(x_1747);
x_1751 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1751, 0, x_1750);
lean_ctor_set_uint8(x_1751, sizeof(void*)*1, x_1736);
x_1752 = lean_array_push(x_1739, x_1751);
if (lean_is_scalar(x_1734)) {
 x_1753 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1753 = x_1734;
 lean_ctor_set_tag(x_1753, 1);
}
lean_ctor_set(x_1753, 0, x_1738);
lean_ctor_set(x_1753, 1, x_1752);
if (lean_is_scalar(x_1749)) {
 x_1754 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1754 = x_1749;
 lean_ctor_set_tag(x_1754, 0);
}
lean_ctor_set(x_1754, 0, x_1753);
lean_ctor_set(x_1754, 1, x_1748);
return x_1754;
}
}
else
{
lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; 
lean_dec(x_21);
x_1755 = lean_ctor_get(x_1740, 0);
lean_inc(x_1755);
x_1756 = lean_ctor_get(x_1740, 1);
lean_inc(x_1756);
if (lean_is_exclusive(x_1740)) {
 lean_ctor_release(x_1740, 0);
 lean_ctor_release(x_1740, 1);
 x_1757 = x_1740;
} else {
 lean_dec_ref(x_1740);
 x_1757 = lean_box(0);
}
x_1758 = lean_io_error_to_string(x_1755);
x_1759 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1759, 0, x_1758);
lean_ctor_set_uint8(x_1759, sizeof(void*)*1, x_1736);
x_1760 = lean_array_push(x_1739, x_1759);
if (lean_is_scalar(x_1734)) {
 x_1761 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1761 = x_1734;
 lean_ctor_set_tag(x_1761, 1);
}
lean_ctor_set(x_1761, 0, x_1738);
lean_ctor_set(x_1761, 1, x_1760);
if (lean_is_scalar(x_1757)) {
 x_1762 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1762 = x_1757;
 lean_ctor_set_tag(x_1762, 0);
}
lean_ctor_set(x_1762, 0, x_1761);
lean_ctor_set(x_1762, 1, x_1756);
return x_1762;
}
}
}
else
{
lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; lean_object* x_1767; lean_object* x_1768; lean_object* x_1769; lean_object* x_1770; lean_object* x_1771; lean_object* x_1772; 
lean_dec(x_1698);
lean_dec(x_21);
x_1763 = lean_ctor_get(x_1696, 1);
lean_inc(x_1763);
if (lean_is_exclusive(x_1696)) {
 lean_ctor_release(x_1696, 0);
 lean_ctor_release(x_1696, 1);
 x_1764 = x_1696;
} else {
 lean_dec_ref(x_1696);
 x_1764 = lean_box(0);
}
x_1765 = lean_ctor_get(x_1, 0);
lean_inc(x_1765);
x_1766 = l_Lake_Env_leanGithash(x_1765);
lean_dec(x_1765);
x_1767 = l_System_Platform_target;
lean_inc(x_1641);
x_1768 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1768, 0, x_1767);
lean_ctor_set(x_1768, 1, x_1766);
lean_ctor_set(x_1768, 2, x_27);
lean_ctor_set(x_1768, 3, x_1641);
x_1769 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1768);
x_1770 = lean_unsigned_to_nat(80u);
x_1771 = l_Lean_Json_pretty(x_1769, x_1770);
x_1772 = l_IO_FS_Handle_putStrLn(x_1318, x_1771, x_1697);
if (lean_obj_tag(x_1772) == 0)
{
lean_object* x_1773; lean_object* x_1774; 
x_1773 = lean_ctor_get(x_1772, 1);
lean_inc(x_1773);
lean_dec(x_1772);
x_1774 = lean_io_prim_handle_truncate(x_1318, x_1773);
if (lean_obj_tag(x_1774) == 0)
{
lean_object* x_1775; lean_object* x_1776; lean_object* x_1777; 
x_1775 = lean_ctor_get(x_1774, 0);
lean_inc(x_1775);
x_1776 = lean_ctor_get(x_1774, 1);
lean_inc(x_1776);
lean_dec(x_1774);
if (lean_is_scalar(x_1764)) {
 x_1777 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1777 = x_1764;
}
lean_ctor_set(x_1777, 0, x_1775);
lean_ctor_set(x_1777, 1, x_1763);
x_1642 = x_1777;
x_1643 = x_1776;
goto block_1695;
}
else
{
lean_object* x_1778; lean_object* x_1779; lean_object* x_1780; uint8_t x_1781; lean_object* x_1782; lean_object* x_1783; lean_object* x_1784; lean_object* x_1785; 
x_1778 = lean_ctor_get(x_1774, 0);
lean_inc(x_1778);
x_1779 = lean_ctor_get(x_1774, 1);
lean_inc(x_1779);
lean_dec(x_1774);
x_1780 = lean_io_error_to_string(x_1778);
x_1781 = 3;
x_1782 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1782, 0, x_1780);
lean_ctor_set_uint8(x_1782, sizeof(void*)*1, x_1781);
x_1783 = lean_array_get_size(x_1763);
x_1784 = lean_array_push(x_1763, x_1782);
if (lean_is_scalar(x_1764)) {
 x_1785 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1785 = x_1764;
 lean_ctor_set_tag(x_1785, 1);
}
lean_ctor_set(x_1785, 0, x_1783);
lean_ctor_set(x_1785, 1, x_1784);
x_1642 = x_1785;
x_1643 = x_1779;
goto block_1695;
}
}
else
{
lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; uint8_t x_1790; lean_object* x_1791; lean_object* x_1792; lean_object* x_1793; lean_object* x_1794; lean_object* x_1795; 
lean_dec(x_1641);
lean_dec(x_1318);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1786 = lean_ctor_get(x_1772, 0);
lean_inc(x_1786);
x_1787 = lean_ctor_get(x_1772, 1);
lean_inc(x_1787);
if (lean_is_exclusive(x_1772)) {
 lean_ctor_release(x_1772, 0);
 lean_ctor_release(x_1772, 1);
 x_1788 = x_1772;
} else {
 lean_dec_ref(x_1772);
 x_1788 = lean_box(0);
}
x_1789 = lean_io_error_to_string(x_1786);
x_1790 = 3;
x_1791 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1791, 0, x_1789);
lean_ctor_set_uint8(x_1791, sizeof(void*)*1, x_1790);
x_1792 = lean_array_get_size(x_1763);
x_1793 = lean_array_push(x_1763, x_1791);
if (lean_is_scalar(x_1764)) {
 x_1794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1794 = x_1764;
 lean_ctor_set_tag(x_1794, 1);
}
lean_ctor_set(x_1794, 0, x_1792);
lean_ctor_set(x_1794, 1, x_1793);
if (lean_is_scalar(x_1788)) {
 x_1795 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1795 = x_1788;
 lean_ctor_set_tag(x_1795, 0);
}
lean_ctor_set(x_1795, 0, x_1794);
lean_ctor_set(x_1795, 1, x_1787);
return x_1795;
}
}
}
}
}
else
{
uint8_t x_1806; 
lean_dec(x_1319);
lean_dec(x_1318);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1806 = !lean_is_exclusive(x_1320);
if (x_1806 == 0)
{
lean_object* x_1807; 
x_1807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1807, 0, x_1320);
lean_ctor_set(x_1807, 1, x_1321);
return x_1807;
}
else
{
lean_object* x_1808; lean_object* x_1809; lean_object* x_1810; lean_object* x_1811; 
x_1808 = lean_ctor_get(x_1320, 0);
x_1809 = lean_ctor_get(x_1320, 1);
lean_inc(x_1809);
lean_inc(x_1808);
lean_dec(x_1320);
x_1810 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1810, 0, x_1808);
lean_ctor_set(x_1810, 1, x_1809);
x_1811 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1811, 0, x_1810);
lean_ctor_set(x_1811, 1, x_1321);
return x_1811;
}
}
}
}
else
{
lean_object* x_1824; lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; lean_object* x_1828; uint8_t x_2002; lean_object* x_2003; 
x_1824 = lean_ctor_get(x_1266, 1);
lean_inc(x_1824);
lean_dec(x_1266);
x_1825 = lean_ctor_get(x_1268, 0);
lean_inc(x_1825);
if (lean_is_exclusive(x_1268)) {
 lean_ctor_release(x_1268, 0);
 x_1826 = x_1268;
} else {
 lean_dec_ref(x_1268);
 x_1826 = lean_box(0);
}
x_2002 = 1;
x_2003 = lean_io_prim_handle_lock(x_1825, x_2002, x_1267);
if (lean_obj_tag(x_2003) == 0)
{
lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; 
x_2004 = lean_ctor_get(x_2003, 0);
lean_inc(x_2004);
x_2005 = lean_ctor_get(x_2003, 1);
lean_inc(x_2005);
lean_dec(x_2003);
x_2006 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2006, 0, x_2004);
lean_ctor_set(x_2006, 1, x_1824);
x_1827 = x_2006;
x_1828 = x_2005;
goto block_2001;
}
else
{
lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; uint8_t x_2010; lean_object* x_2011; lean_object* x_2012; lean_object* x_2013; lean_object* x_2014; 
x_2007 = lean_ctor_get(x_2003, 0);
lean_inc(x_2007);
x_2008 = lean_ctor_get(x_2003, 1);
lean_inc(x_2008);
lean_dec(x_2003);
x_2009 = lean_io_error_to_string(x_2007);
x_2010 = 3;
x_2011 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_2011, 0, x_2009);
lean_ctor_set_uint8(x_2011, sizeof(void*)*1, x_2010);
x_2012 = lean_array_get_size(x_1824);
x_2013 = lean_array_push(x_1824, x_2011);
x_2014 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2014, 0, x_2012);
lean_ctor_set(x_2014, 1, x_2013);
x_1827 = x_2014;
x_1828 = x_2008;
goto block_2001;
}
block_2001:
{
if (lean_obj_tag(x_1827) == 0)
{
lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1886; lean_object* x_1887; lean_object* x_1987; 
x_1829 = lean_ctor_get(x_1827, 1);
lean_inc(x_1829);
if (lean_is_exclusive(x_1827)) {
 lean_ctor_release(x_1827, 0);
 lean_ctor_release(x_1827, 1);
 x_1830 = x_1827;
} else {
 lean_dec_ref(x_1827);
 x_1830 = lean_box(0);
}
x_1831 = lean_ctor_get(x_1, 8);
lean_inc(x_1831);
x_1987 = lean_io_remove_file(x_18, x_1828);
if (lean_obj_tag(x_1987) == 0)
{
lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; 
x_1988 = lean_ctor_get(x_1987, 0);
lean_inc(x_1988);
x_1989 = lean_ctor_get(x_1987, 1);
lean_inc(x_1989);
lean_dec(x_1987);
if (lean_is_scalar(x_1826)) {
 x_1990 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1990 = x_1826;
}
lean_ctor_set(x_1990, 0, x_1988);
if (lean_is_scalar(x_1830)) {
 x_1991 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1991 = x_1830;
}
lean_ctor_set(x_1991, 0, x_1990);
lean_ctor_set(x_1991, 1, x_1829);
x_1886 = x_1991;
x_1887 = x_1989;
goto block_1986;
}
else
{
lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; lean_object* x_1995; 
x_1992 = lean_ctor_get(x_1987, 0);
lean_inc(x_1992);
x_1993 = lean_ctor_get(x_1987, 1);
lean_inc(x_1993);
lean_dec(x_1987);
if (lean_is_scalar(x_1826)) {
 x_1994 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1994 = x_1826;
 lean_ctor_set_tag(x_1994, 0);
}
lean_ctor_set(x_1994, 0, x_1992);
if (lean_is_scalar(x_1830)) {
 x_1995 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1995 = x_1830;
}
lean_ctor_set(x_1995, 0, x_1994);
lean_ctor_set(x_1995, 1, x_1829);
x_1886 = x_1995;
x_1887 = x_1993;
goto block_1986;
}
block_1885:
{
if (lean_obj_tag(x_1832) == 0)
{
lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; 
x_1834 = lean_ctor_get(x_1832, 1);
lean_inc(x_1834);
lean_dec(x_1832);
x_1835 = lean_ctor_get(x_1, 9);
lean_inc(x_1835);
lean_dec(x_1);
x_1836 = l_Lake_elabConfigFile(x_13, x_1831, x_1835, x_4, x_1834, x_1833);
if (lean_obj_tag(x_1836) == 0)
{
lean_object* x_1837; 
x_1837 = lean_ctor_get(x_1836, 0);
lean_inc(x_1837);
if (lean_obj_tag(x_1837) == 0)
{
lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; lean_object* x_1842; 
x_1838 = lean_ctor_get(x_1836, 1);
lean_inc(x_1838);
lean_dec(x_1836);
x_1839 = lean_ctor_get(x_1837, 0);
lean_inc(x_1839);
x_1840 = lean_ctor_get(x_1837, 1);
lean_inc(x_1840);
if (lean_is_exclusive(x_1837)) {
 lean_ctor_release(x_1837, 0);
 lean_ctor_release(x_1837, 1);
 x_1841 = x_1837;
} else {
 lean_dec_ref(x_1837);
 x_1841 = lean_box(0);
}
lean_inc(x_1839);
x_1842 = lean_write_module(x_1839, x_18, x_1838);
if (lean_obj_tag(x_1842) == 0)
{
lean_object* x_1843; lean_object* x_1844; 
x_1843 = lean_ctor_get(x_1842, 1);
lean_inc(x_1843);
lean_dec(x_1842);
x_1844 = lean_io_prim_handle_unlock(x_1825, x_1843);
lean_dec(x_1825);
if (lean_obj_tag(x_1844) == 0)
{
lean_object* x_1845; lean_object* x_1846; lean_object* x_1847; lean_object* x_1848; 
x_1845 = lean_ctor_get(x_1844, 1);
lean_inc(x_1845);
if (lean_is_exclusive(x_1844)) {
 lean_ctor_release(x_1844, 0);
 lean_ctor_release(x_1844, 1);
 x_1846 = x_1844;
} else {
 lean_dec_ref(x_1844);
 x_1846 = lean_box(0);
}
if (lean_is_scalar(x_1841)) {
 x_1847 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1847 = x_1841;
}
lean_ctor_set(x_1847, 0, x_1839);
lean_ctor_set(x_1847, 1, x_1840);
if (lean_is_scalar(x_1846)) {
 x_1848 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1848 = x_1846;
}
lean_ctor_set(x_1848, 0, x_1847);
lean_ctor_set(x_1848, 1, x_1845);
return x_1848;
}
else
{
lean_object* x_1849; lean_object* x_1850; lean_object* x_1851; lean_object* x_1852; uint8_t x_1853; lean_object* x_1854; lean_object* x_1855; lean_object* x_1856; lean_object* x_1857; lean_object* x_1858; 
lean_dec(x_1839);
x_1849 = lean_ctor_get(x_1844, 0);
lean_inc(x_1849);
x_1850 = lean_ctor_get(x_1844, 1);
lean_inc(x_1850);
if (lean_is_exclusive(x_1844)) {
 lean_ctor_release(x_1844, 0);
 lean_ctor_release(x_1844, 1);
 x_1851 = x_1844;
} else {
 lean_dec_ref(x_1844);
 x_1851 = lean_box(0);
}
x_1852 = lean_io_error_to_string(x_1849);
x_1853 = 3;
x_1854 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1854, 0, x_1852);
lean_ctor_set_uint8(x_1854, sizeof(void*)*1, x_1853);
x_1855 = lean_array_get_size(x_1840);
x_1856 = lean_array_push(x_1840, x_1854);
if (lean_is_scalar(x_1841)) {
 x_1857 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1857 = x_1841;
 lean_ctor_set_tag(x_1857, 1);
}
lean_ctor_set(x_1857, 0, x_1855);
lean_ctor_set(x_1857, 1, x_1856);
if (lean_is_scalar(x_1851)) {
 x_1858 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1858 = x_1851;
 lean_ctor_set_tag(x_1858, 0);
}
lean_ctor_set(x_1858, 0, x_1857);
lean_ctor_set(x_1858, 1, x_1850);
return x_1858;
}
}
else
{
lean_object* x_1859; lean_object* x_1860; lean_object* x_1861; lean_object* x_1862; uint8_t x_1863; lean_object* x_1864; lean_object* x_1865; lean_object* x_1866; lean_object* x_1867; lean_object* x_1868; 
lean_dec(x_1839);
lean_dec(x_1825);
x_1859 = lean_ctor_get(x_1842, 0);
lean_inc(x_1859);
x_1860 = lean_ctor_get(x_1842, 1);
lean_inc(x_1860);
if (lean_is_exclusive(x_1842)) {
 lean_ctor_release(x_1842, 0);
 lean_ctor_release(x_1842, 1);
 x_1861 = x_1842;
} else {
 lean_dec_ref(x_1842);
 x_1861 = lean_box(0);
}
x_1862 = lean_io_error_to_string(x_1859);
x_1863 = 3;
x_1864 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1864, 0, x_1862);
lean_ctor_set_uint8(x_1864, sizeof(void*)*1, x_1863);
x_1865 = lean_array_get_size(x_1840);
x_1866 = lean_array_push(x_1840, x_1864);
if (lean_is_scalar(x_1841)) {
 x_1867 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1867 = x_1841;
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
lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; lean_object* x_1875; 
lean_dec(x_1825);
lean_dec(x_18);
x_1869 = lean_ctor_get(x_1836, 1);
lean_inc(x_1869);
if (lean_is_exclusive(x_1836)) {
 lean_ctor_release(x_1836, 0);
 lean_ctor_release(x_1836, 1);
 x_1870 = x_1836;
} else {
 lean_dec_ref(x_1836);
 x_1870 = lean_box(0);
}
x_1871 = lean_ctor_get(x_1837, 0);
lean_inc(x_1871);
x_1872 = lean_ctor_get(x_1837, 1);
lean_inc(x_1872);
if (lean_is_exclusive(x_1837)) {
 lean_ctor_release(x_1837, 0);
 lean_ctor_release(x_1837, 1);
 x_1873 = x_1837;
} else {
 lean_dec_ref(x_1837);
 x_1873 = lean_box(0);
}
if (lean_is_scalar(x_1873)) {
 x_1874 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1874 = x_1873;
}
lean_ctor_set(x_1874, 0, x_1871);
lean_ctor_set(x_1874, 1, x_1872);
if (lean_is_scalar(x_1870)) {
 x_1875 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1875 = x_1870;
}
lean_ctor_set(x_1875, 0, x_1874);
lean_ctor_set(x_1875, 1, x_1869);
return x_1875;
}
}
else
{
lean_object* x_1876; lean_object* x_1877; lean_object* x_1878; lean_object* x_1879; 
lean_dec(x_1825);
lean_dec(x_18);
x_1876 = lean_ctor_get(x_1836, 0);
lean_inc(x_1876);
x_1877 = lean_ctor_get(x_1836, 1);
lean_inc(x_1877);
if (lean_is_exclusive(x_1836)) {
 lean_ctor_release(x_1836, 0);
 lean_ctor_release(x_1836, 1);
 x_1878 = x_1836;
} else {
 lean_dec_ref(x_1836);
 x_1878 = lean_box(0);
}
if (lean_is_scalar(x_1878)) {
 x_1879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1879 = x_1878;
}
lean_ctor_set(x_1879, 0, x_1876);
lean_ctor_set(x_1879, 1, x_1877);
return x_1879;
}
}
else
{
lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; 
lean_dec(x_1831);
lean_dec(x_1825);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1880 = lean_ctor_get(x_1832, 0);
lean_inc(x_1880);
x_1881 = lean_ctor_get(x_1832, 1);
lean_inc(x_1881);
if (lean_is_exclusive(x_1832)) {
 lean_ctor_release(x_1832, 0);
 lean_ctor_release(x_1832, 1);
 x_1882 = x_1832;
} else {
 lean_dec_ref(x_1832);
 x_1882 = lean_box(0);
}
if (lean_is_scalar(x_1882)) {
 x_1883 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1883 = x_1882;
}
lean_ctor_set(x_1883, 0, x_1880);
lean_ctor_set(x_1883, 1, x_1881);
x_1884 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1884, 0, x_1883);
lean_ctor_set(x_1884, 1, x_1833);
return x_1884;
}
}
block_1986:
{
lean_object* x_1888; 
x_1888 = lean_ctor_get(x_1886, 0);
lean_inc(x_1888);
if (lean_obj_tag(x_1888) == 0)
{
lean_object* x_1889; 
x_1889 = lean_ctor_get(x_1888, 0);
lean_inc(x_1889);
lean_dec(x_1888);
if (lean_obj_tag(x_1889) == 11)
{
lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; lean_object* x_1893; lean_object* x_1894; lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; 
lean_dec(x_1889);
lean_dec(x_21);
x_1890 = lean_ctor_get(x_1886, 1);
lean_inc(x_1890);
if (lean_is_exclusive(x_1886)) {
 lean_ctor_release(x_1886, 0);
 lean_ctor_release(x_1886, 1);
 x_1891 = x_1886;
} else {
 lean_dec_ref(x_1886);
 x_1891 = lean_box(0);
}
x_1892 = lean_ctor_get(x_1, 0);
lean_inc(x_1892);
x_1893 = l_Lake_Env_leanGithash(x_1892);
lean_dec(x_1892);
x_1894 = l_System_Platform_target;
lean_inc(x_1831);
x_1895 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1895, 0, x_1894);
lean_ctor_set(x_1895, 1, x_1893);
lean_ctor_set(x_1895, 2, x_27);
lean_ctor_set(x_1895, 3, x_1831);
x_1896 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1895);
x_1897 = lean_unsigned_to_nat(80u);
x_1898 = l_Lean_Json_pretty(x_1896, x_1897);
x_1899 = l_IO_FS_Handle_putStrLn(x_1825, x_1898, x_1887);
if (lean_obj_tag(x_1899) == 0)
{
lean_object* x_1900; lean_object* x_1901; 
x_1900 = lean_ctor_get(x_1899, 1);
lean_inc(x_1900);
lean_dec(x_1899);
x_1901 = lean_io_prim_handle_truncate(x_1825, x_1900);
if (lean_obj_tag(x_1901) == 0)
{
lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; 
x_1902 = lean_ctor_get(x_1901, 0);
lean_inc(x_1902);
x_1903 = lean_ctor_get(x_1901, 1);
lean_inc(x_1903);
lean_dec(x_1901);
if (lean_is_scalar(x_1891)) {
 x_1904 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1904 = x_1891;
}
lean_ctor_set(x_1904, 0, x_1902);
lean_ctor_set(x_1904, 1, x_1890);
x_1832 = x_1904;
x_1833 = x_1903;
goto block_1885;
}
else
{
lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; uint8_t x_1908; lean_object* x_1909; lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; 
x_1905 = lean_ctor_get(x_1901, 0);
lean_inc(x_1905);
x_1906 = lean_ctor_get(x_1901, 1);
lean_inc(x_1906);
lean_dec(x_1901);
x_1907 = lean_io_error_to_string(x_1905);
x_1908 = 3;
x_1909 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1909, 0, x_1907);
lean_ctor_set_uint8(x_1909, sizeof(void*)*1, x_1908);
x_1910 = lean_array_get_size(x_1890);
x_1911 = lean_array_push(x_1890, x_1909);
if (lean_is_scalar(x_1891)) {
 x_1912 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1912 = x_1891;
 lean_ctor_set_tag(x_1912, 1);
}
lean_ctor_set(x_1912, 0, x_1910);
lean_ctor_set(x_1912, 1, x_1911);
x_1832 = x_1912;
x_1833 = x_1906;
goto block_1885;
}
}
else
{
lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; uint8_t x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; 
lean_dec(x_1831);
lean_dec(x_1825);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1913 = lean_ctor_get(x_1899, 0);
lean_inc(x_1913);
x_1914 = lean_ctor_get(x_1899, 1);
lean_inc(x_1914);
if (lean_is_exclusive(x_1899)) {
 lean_ctor_release(x_1899, 0);
 lean_ctor_release(x_1899, 1);
 x_1915 = x_1899;
} else {
 lean_dec_ref(x_1899);
 x_1915 = lean_box(0);
}
x_1916 = lean_io_error_to_string(x_1913);
x_1917 = 3;
x_1918 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1918, 0, x_1916);
lean_ctor_set_uint8(x_1918, sizeof(void*)*1, x_1917);
x_1919 = lean_array_get_size(x_1890);
x_1920 = lean_array_push(x_1890, x_1918);
if (lean_is_scalar(x_1891)) {
 x_1921 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1921 = x_1891;
 lean_ctor_set_tag(x_1921, 1);
}
lean_ctor_set(x_1921, 0, x_1919);
lean_ctor_set(x_1921, 1, x_1920);
if (lean_is_scalar(x_1915)) {
 x_1922 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1922 = x_1915;
 lean_ctor_set_tag(x_1922, 0);
}
lean_ctor_set(x_1922, 0, x_1921);
lean_ctor_set(x_1922, 1, x_1914);
return x_1922;
}
}
else
{
lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; uint8_t x_1926; lean_object* x_1927; lean_object* x_1928; lean_object* x_1929; lean_object* x_1930; 
lean_dec(x_1831);
lean_dec(x_27);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1923 = lean_ctor_get(x_1886, 1);
lean_inc(x_1923);
if (lean_is_exclusive(x_1886)) {
 lean_ctor_release(x_1886, 0);
 lean_ctor_release(x_1886, 1);
 x_1924 = x_1886;
} else {
 lean_dec_ref(x_1886);
 x_1924 = lean_box(0);
}
x_1925 = lean_io_error_to_string(x_1889);
x_1926 = 3;
x_1927 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1927, 0, x_1925);
lean_ctor_set_uint8(x_1927, sizeof(void*)*1, x_1926);
x_1928 = lean_array_get_size(x_1923);
x_1929 = lean_array_push(x_1923, x_1927);
x_1930 = lean_io_prim_handle_unlock(x_1825, x_1887);
lean_dec(x_1825);
if (lean_obj_tag(x_1930) == 0)
{
lean_object* x_1931; lean_object* x_1932; 
x_1931 = lean_ctor_get(x_1930, 1);
lean_inc(x_1931);
lean_dec(x_1930);
x_1932 = lean_io_remove_file(x_21, x_1931);
lean_dec(x_21);
if (lean_obj_tag(x_1932) == 0)
{
lean_object* x_1933; lean_object* x_1934; lean_object* x_1935; lean_object* x_1936; 
x_1933 = lean_ctor_get(x_1932, 1);
lean_inc(x_1933);
if (lean_is_exclusive(x_1932)) {
 lean_ctor_release(x_1932, 0);
 lean_ctor_release(x_1932, 1);
 x_1934 = x_1932;
} else {
 lean_dec_ref(x_1932);
 x_1934 = lean_box(0);
}
if (lean_is_scalar(x_1924)) {
 x_1935 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1935 = x_1924;
 lean_ctor_set_tag(x_1935, 1);
}
lean_ctor_set(x_1935, 0, x_1928);
lean_ctor_set(x_1935, 1, x_1929);
if (lean_is_scalar(x_1934)) {
 x_1936 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1936 = x_1934;
}
lean_ctor_set(x_1936, 0, x_1935);
lean_ctor_set(x_1936, 1, x_1933);
return x_1936;
}
else
{
lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; lean_object* x_1943; lean_object* x_1944; 
x_1937 = lean_ctor_get(x_1932, 0);
lean_inc(x_1937);
x_1938 = lean_ctor_get(x_1932, 1);
lean_inc(x_1938);
if (lean_is_exclusive(x_1932)) {
 lean_ctor_release(x_1932, 0);
 lean_ctor_release(x_1932, 1);
 x_1939 = x_1932;
} else {
 lean_dec_ref(x_1932);
 x_1939 = lean_box(0);
}
x_1940 = lean_io_error_to_string(x_1937);
x_1941 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1941, 0, x_1940);
lean_ctor_set_uint8(x_1941, sizeof(void*)*1, x_1926);
x_1942 = lean_array_push(x_1929, x_1941);
if (lean_is_scalar(x_1924)) {
 x_1943 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1943 = x_1924;
 lean_ctor_set_tag(x_1943, 1);
}
lean_ctor_set(x_1943, 0, x_1928);
lean_ctor_set(x_1943, 1, x_1942);
if (lean_is_scalar(x_1939)) {
 x_1944 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1944 = x_1939;
 lean_ctor_set_tag(x_1944, 0);
}
lean_ctor_set(x_1944, 0, x_1943);
lean_ctor_set(x_1944, 1, x_1938);
return x_1944;
}
}
else
{
lean_object* x_1945; lean_object* x_1946; lean_object* x_1947; lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; 
lean_dec(x_21);
x_1945 = lean_ctor_get(x_1930, 0);
lean_inc(x_1945);
x_1946 = lean_ctor_get(x_1930, 1);
lean_inc(x_1946);
if (lean_is_exclusive(x_1930)) {
 lean_ctor_release(x_1930, 0);
 lean_ctor_release(x_1930, 1);
 x_1947 = x_1930;
} else {
 lean_dec_ref(x_1930);
 x_1947 = lean_box(0);
}
x_1948 = lean_io_error_to_string(x_1945);
x_1949 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1949, 0, x_1948);
lean_ctor_set_uint8(x_1949, sizeof(void*)*1, x_1926);
x_1950 = lean_array_push(x_1929, x_1949);
if (lean_is_scalar(x_1924)) {
 x_1951 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1951 = x_1924;
 lean_ctor_set_tag(x_1951, 1);
}
lean_ctor_set(x_1951, 0, x_1928);
lean_ctor_set(x_1951, 1, x_1950);
if (lean_is_scalar(x_1947)) {
 x_1952 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1952 = x_1947;
 lean_ctor_set_tag(x_1952, 0);
}
lean_ctor_set(x_1952, 0, x_1951);
lean_ctor_set(x_1952, 1, x_1946);
return x_1952;
}
}
}
else
{
lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; lean_object* x_1961; lean_object* x_1962; 
lean_dec(x_1888);
lean_dec(x_21);
x_1953 = lean_ctor_get(x_1886, 1);
lean_inc(x_1953);
if (lean_is_exclusive(x_1886)) {
 lean_ctor_release(x_1886, 0);
 lean_ctor_release(x_1886, 1);
 x_1954 = x_1886;
} else {
 lean_dec_ref(x_1886);
 x_1954 = lean_box(0);
}
x_1955 = lean_ctor_get(x_1, 0);
lean_inc(x_1955);
x_1956 = l_Lake_Env_leanGithash(x_1955);
lean_dec(x_1955);
x_1957 = l_System_Platform_target;
lean_inc(x_1831);
x_1958 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1958, 0, x_1957);
lean_ctor_set(x_1958, 1, x_1956);
lean_ctor_set(x_1958, 2, x_27);
lean_ctor_set(x_1958, 3, x_1831);
x_1959 = l___private_Lake_Load_Lean_Elab_0__Lake_toJsonConfigTrace____x40_Lake_Load_Lean_Elab___hyg_870_(x_1958);
x_1960 = lean_unsigned_to_nat(80u);
x_1961 = l_Lean_Json_pretty(x_1959, x_1960);
x_1962 = l_IO_FS_Handle_putStrLn(x_1825, x_1961, x_1887);
if (lean_obj_tag(x_1962) == 0)
{
lean_object* x_1963; lean_object* x_1964; 
x_1963 = lean_ctor_get(x_1962, 1);
lean_inc(x_1963);
lean_dec(x_1962);
x_1964 = lean_io_prim_handle_truncate(x_1825, x_1963);
if (lean_obj_tag(x_1964) == 0)
{
lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; 
x_1965 = lean_ctor_get(x_1964, 0);
lean_inc(x_1965);
x_1966 = lean_ctor_get(x_1964, 1);
lean_inc(x_1966);
lean_dec(x_1964);
if (lean_is_scalar(x_1954)) {
 x_1967 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1967 = x_1954;
}
lean_ctor_set(x_1967, 0, x_1965);
lean_ctor_set(x_1967, 1, x_1953);
x_1832 = x_1967;
x_1833 = x_1966;
goto block_1885;
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
x_1973 = lean_array_get_size(x_1953);
x_1974 = lean_array_push(x_1953, x_1972);
if (lean_is_scalar(x_1954)) {
 x_1975 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1975 = x_1954;
 lean_ctor_set_tag(x_1975, 1);
}
lean_ctor_set(x_1975, 0, x_1973);
lean_ctor_set(x_1975, 1, x_1974);
x_1832 = x_1975;
x_1833 = x_1969;
goto block_1885;
}
}
else
{
lean_object* x_1976; lean_object* x_1977; lean_object* x_1978; lean_object* x_1979; uint8_t x_1980; lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; 
lean_dec(x_1831);
lean_dec(x_1825);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1976 = lean_ctor_get(x_1962, 0);
lean_inc(x_1976);
x_1977 = lean_ctor_get(x_1962, 1);
lean_inc(x_1977);
if (lean_is_exclusive(x_1962)) {
 lean_ctor_release(x_1962, 0);
 lean_ctor_release(x_1962, 1);
 x_1978 = x_1962;
} else {
 lean_dec_ref(x_1962);
 x_1978 = lean_box(0);
}
x_1979 = lean_io_error_to_string(x_1976);
x_1980 = 3;
x_1981 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_1981, 0, x_1979);
lean_ctor_set_uint8(x_1981, sizeof(void*)*1, x_1980);
x_1982 = lean_array_get_size(x_1953);
x_1983 = lean_array_push(x_1953, x_1981);
if (lean_is_scalar(x_1954)) {
 x_1984 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1984 = x_1954;
 lean_ctor_set_tag(x_1984, 1);
}
lean_ctor_set(x_1984, 0, x_1982);
lean_ctor_set(x_1984, 1, x_1983);
if (lean_is_scalar(x_1978)) {
 x_1985 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1985 = x_1978;
 lean_ctor_set_tag(x_1985, 0);
}
lean_ctor_set(x_1985, 0, x_1984);
lean_ctor_set(x_1985, 1, x_1977);
return x_1985;
}
}
}
}
else
{
lean_object* x_1996; lean_object* x_1997; lean_object* x_1998; lean_object* x_1999; lean_object* x_2000; 
lean_dec(x_1826);
lean_dec(x_1825);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_1);
x_1996 = lean_ctor_get(x_1827, 0);
lean_inc(x_1996);
x_1997 = lean_ctor_get(x_1827, 1);
lean_inc(x_1997);
if (lean_is_exclusive(x_1827)) {
 lean_ctor_release(x_1827, 0);
 lean_ctor_release(x_1827, 1);
 x_1998 = x_1827;
} else {
 lean_dec_ref(x_1827);
 x_1998 = lean_box(0);
}
if (lean_is_scalar(x_1998)) {
 x_1999 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1999 = x_1998;
}
lean_ctor_set(x_1999, 0, x_1996);
lean_ctor_set(x_1999, 1, x_1997);
x_2000 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2000, 0, x_1999);
lean_ctor_set(x_2000, 1, x_1828);
return x_2000;
}
}
}
}
}
}
else
{
uint8_t x_2106; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_4);
lean_dec(x_1);
x_2106 = !lean_is_exclusive(x_25);
if (x_2106 == 0)
{
lean_object* x_2107; 
x_2107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2107, 0, x_25);
lean_ctor_set(x_2107, 1, x_26);
return x_2107;
}
else
{
lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; 
x_2108 = lean_ctor_get(x_25, 0);
x_2109 = lean_ctor_get(x_25, 1);
lean_inc(x_2109);
lean_inc(x_2108);
lean_dec(x_25);
x_2110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_2110, 0, x_2108);
lean_ctor_set(x_2110, 1, x_2109);
x_2111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2111, 0, x_2110);
lean_ctor_set(x_2111, 1, x_26);
return x_2111;
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
