// Lean compiler output
// Module: Lake.Load.Toml
// Imports: Init Lake.Toml.Load Lake.Toml.Decode Lake.Config.Package Lake.Util.Log
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
static lean_object* l_Lake_PackageConfig_decodeToml___closed__27;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___boxed(lean_object*);
static lean_object* l_Lake_Backend_decodeToml___closed__2;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__10;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__11;
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__11(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_loadTomlConfig___closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__2;
static lean_object* l_Lake_LeanOption_decodeToml___closed__4;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_RBArray_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__24;
static lean_object* l_Lake_Backend_decodeToml___closed__4;
static lean_object* l_Lake_Dependency_decodeToml___closed__2;
extern lean_object* l_Lake_defaultBuildDir;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__33;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__37;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__17;
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__30;
static lean_object* l_Lake_Dependency_decodeToml___closed__10;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__9;
static lean_object* l_Lake_BuildType_decodeToml___closed__7;
static lean_object* l_Lake_LeanOption_decodeToml___closed__2;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__6;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanOptionValue(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__1;
lean_object* l_Lake_Toml_ppKey(lean_object*);
static lean_object* l_Lake_Dependency_decodeToml___closed__12;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependency(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_loadTomlConfig___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__15;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__11;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultPackagesDir;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__20;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__3;
static lean_object* l_Lake_loadTomlConfig___closed__5;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(lean_object*);
static lean_object* l_Lake_Glob_decodeToml___closed__2;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__22;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__18;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__13;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__9;
static lean_object* l_Lake_Backend_decodeToml___closed__6;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlBuildType(lean_object*);
static lean_object* l_Lake_loadTomlConfig___closed__4;
static lean_object* l_Lake_loadTomlConfig___closed__3;
static lean_object* l_Lake_loadTomlConfig___closed__9;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__8;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_loadTomlConfig___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_WorkspaceConfig_decodeToml___closed__1;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__9;
LEAN_EXPORT lean_object* l_Lake_LeanOptionValue_decodeToml(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__3;
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__13;
LEAN_EXPORT lean_object* l_Lake_DependencySrc_decodeToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(lean_object*);
extern uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__4(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__35;
static lean_object* l_Lake_loadTomlConfig___closed__10;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptionsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__9;
static lean_object* l_Lake_BuildType_decodeToml___closed__6;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__21;
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f(lean_object*);
static lean_object* l_Lake_LeanOptionValue_decodeToml___closed__1;
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__6;
static lean_object* l_Lake_takeNamePart___closed__1;
lean_object* l_Lake_RBArray_mkEmpty___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__3;
static lean_object* l_Lake_LeanOptionValue_decodeToml___closed__2;
static uint8_t l_Lake_PackageConfig_decodeToml___closed__12;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__21;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__15;
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlPackageConfig(lean_object*);
static lean_object* l_Lake_LeanOption_decodeToml___closed__1;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__23;
static uint8_t l_Lake_LeanOption_decodeToml___closed__8;
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_loadTomlConfig___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_String_isEmpty(lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__29;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_globs___default___spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__14(lean_object*);
lean_object* l_panic___at_String_toNat_x21___spec__1(lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__3;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__5;
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__15(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__11___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(lean_object*);
static lean_object* l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__18;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1___boxed(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__8;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanExeConfig(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__9(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Dependency_decodeToml___closed__9;
static lean_object* l_Lake_takeNamePart___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__26;
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4;
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__1;
static lean_object* l_Lake_LeanOption_decodeToml___closed__12;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__8;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__5;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2;
static lean_object* l_Lake_Dependency_decodeToml___closed__11;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__1;
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__7;
static lean_object* l_Lake_loadTomlConfig___closed__8;
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptions(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanConfig(lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__19;
LEAN_EXPORT lean_object* l_Lake_Dependency_decodeToml(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__6;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Dependency_decodeToml___closed__4;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__17;
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__16;
lean_object* l_Lake_Toml_RBDict_findEntry_x3f___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__3;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__12;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanConfig_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__22;
static lean_object* l_Lake_LeanOption_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__31;
static lean_object* l_Lake_loadTomlConfig___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__4;
static lean_object* l_Lake_Dependency_decodeToml___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__23;
static lean_object* l_Lake_decodeLeanOptions___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_loadTomlConfig___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlWorkspaceConfig(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__18;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__15;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__17;
static lean_object* l_Lake_loadTomlConfig___closed__6;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__14;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__19;
static lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2;
static lean_object* l_Lake_Dependency_decodeToml___closed__3;
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanOption_decodeToml___closed__9;
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_decodeToml(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Backend_decodeToml(lean_object*);
static lean_object* l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__16;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlBackend(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
uint8_t l_Char_isDigit(uint32_t);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__20;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanLibConfig(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__2;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__19;
LEAN_EXPORT lean_object* l_Lake_BuildType_decodeToml(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_PackageConfig_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_Backend_decodeToml___closed__7;
static uint8_t l_Lake_PackageConfig_decodeToml___closed__13;
static lean_object* l_Lake_LeanOption_decodeToml___closed__11;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__6;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__32;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
lean_object* l_Lake_mergeErrors___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__24;
static lean_object* l_Lake_BuildType_decodeToml___closed__1;
static lean_object* l_Lake_BuildType_decodeToml___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__28;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__5;
LEAN_EXPORT lean_object* l_Lake_LeanConfig_decodeToml(lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__9;
LEAN_EXPORT lean_object* l_Lake_takeName(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__38;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptionsAux___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__14;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlGlob(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__11;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_PackageConfig_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanOption;
lean_object* l_String_toName(lean_object*);
static lean_object* l_Lake_LeanOption_decodeToml___closed__13;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__16;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__10;
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_WorkspaceConfig_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Lake_takeName_takeRest(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultNativeLibDir;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__4;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependencySrc(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanConfig_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_decodeToml(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__4;
static lean_object* l_Lake_BuildType_decodeToml___closed__4;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__11;
static lean_object* l_Lake_Dependency_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1(uint8_t);
static lean_object* l_Lake_takeNamePart___closed__3;
static lean_object* l_Lake_LeanOption_decodeToml___closed__5;
static lean_object* l_Lake_Backend_decodeToml___closed__3;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Lake_Glob_decodeToml(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__3(lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__6;
static lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__12;
static lean_object* l_Lake_instDecodeTomlLeanOption___closed__1;
static lean_object* l_Lake_LeanOption_decodeToml___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_LeanOption_decodeToml___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__5;
static lean_object* l_Lake_LeanOption_decodeToml___closed__10;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__14;
static lean_object* l_Lake_Dependency_decodeToml___closed__5;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__7;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__25;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeNamePart(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__12(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultBinDir;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__34;
static lean_object* l_Lake_takeNamePart___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__36;
extern lean_object* l_Lake_defaultIrDir;
static lean_object* l_Lake_Backend_decodeToml___closed__1;
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__5;
static lean_object* l_Lake_Backend_decodeToml___closed__5;
uint8_t l_Lean_isIdFirst(uint32_t);
static lean_object* l_Lake_Dependency_decodeToml___closed__6;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_decodeToml(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanOption_decodeToml(lean_object*);
extern lean_object* l_Lake_defaultLeanLibDir;
static lean_object* l_Lake_Glob_decodeToml___closed__1;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__12;
extern lean_object* l_Lake_defaultManifestFile;
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__14___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_loadTomlConfig___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Message_toString(lean_object*, uint8_t, lean_object*);
static lean_object* _init_l_Lake_takeNamePart___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_takeNamePart___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Option.get!", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_takeNamePart___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value is none", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_takeNamePart___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_takeNamePart___closed__1;
x_2 = l_Lake_takeNamePart___closed__2;
x_3 = lean_unsigned_to_nat(16u);
x_4 = lean_unsigned_to_nat(14u);
x_5 = l_Lake_takeNamePart___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_takeNamePart(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_nat_add(x_4, x_7);
x_10 = lean_string_utf8_get(x_3, x_9);
lean_dec(x_9);
x_11 = l_Lean_idBeginEscape;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_isIdFirst(x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_Char_isDigit(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Substring_nextn(x_1, x_17, x_7);
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_20 = lean_ctor_get(x_1, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_nat_add(x_4, x_18);
lean_dec(x_18);
x_24 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__1(x_3, x_5, x_23);
lean_inc(x_24);
lean_inc(x_3);
lean_ctor_set(x_1, 1, x_24);
x_25 = lean_string_utf8_extract(x_3, x_4, x_24);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_26 = l_Lean_Syntax_decodeNatLitVal_x3f(x_25);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lake_takeNamePart___closed__4;
x_28 = l_panic___at_String_toNat_x21___spec__1(x_27);
x_29 = l_Lean_Name_num___override(x_2, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = l_Lean_Name_num___override(x_2, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_34 = lean_nat_add(x_4, x_18);
lean_dec(x_18);
x_35 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__1(x_3, x_5, x_34);
lean_inc(x_35);
lean_inc(x_3);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set(x_36, 2, x_5);
x_37 = lean_string_utf8_extract(x_3, x_4, x_35);
lean_dec(x_35);
lean_dec(x_4);
lean_dec(x_3);
x_38 = l_Lean_Syntax_decodeNatLitVal_x3f(x_37);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Lake_takeNamePart___closed__4;
x_40 = l_panic___at_String_toNat_x21___spec__1(x_39);
x_41 = l_Lean_Name_num___override(x_2, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
lean_dec(x_38);
x_44 = l_Lean_Name_num___override(x_2, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = l_Substring_nextn(x_1, x_46, x_7);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_49 = lean_ctor_get(x_1, 2);
lean_dec(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_52 = lean_nat_add(x_4, x_47);
lean_dec(x_47);
x_53 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__2(x_3, x_5, x_52);
lean_inc(x_53);
lean_inc(x_3);
lean_ctor_set(x_1, 1, x_53);
x_54 = lean_string_utf8_extract(x_3, x_4, x_53);
lean_dec(x_53);
lean_dec(x_4);
lean_dec(x_3);
x_55 = l_Lean_Name_str___override(x_2, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_1);
x_57 = lean_nat_add(x_4, x_47);
lean_dec(x_47);
x_58 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__2(x_3, x_5, x_57);
lean_inc(x_58);
lean_inc(x_3);
x_59 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_59, 2, x_5);
x_60 = lean_string_utf8_extract(x_3, x_4, x_58);
lean_dec(x_58);
lean_dec(x_4);
lean_dec(x_3);
x_61 = l_Lean_Name_str___override(x_2, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = l_Substring_nextn(x_1, x_63, x_7);
x_65 = !lean_is_exclusive(x_1);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint32_t x_72; uint32_t x_73; uint8_t x_74; 
x_66 = lean_ctor_get(x_1, 2);
lean_dec(x_66);
x_67 = lean_ctor_get(x_1, 1);
lean_dec(x_67);
x_68 = lean_ctor_get(x_1, 0);
lean_dec(x_68);
x_69 = lean_nat_add(x_4, x_64);
lean_dec(x_64);
lean_dec(x_4);
lean_inc(x_69);
x_70 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__3(x_3, x_5, x_69);
lean_inc(x_70);
lean_inc(x_3);
lean_ctor_set(x_1, 1, x_70);
x_71 = lean_nat_add(x_70, x_7);
x_72 = lean_string_utf8_get(x_3, x_71);
lean_dec(x_71);
x_73 = l_Lean_idEndEscape;
x_74 = lean_uint32_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_3);
lean_dec(x_2);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_string_utf8_extract(x_3, x_69, x_70);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_3);
x_78 = l_Lean_Name_str___override(x_2, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint32_t x_84; uint32_t x_85; uint8_t x_86; 
lean_dec(x_1);
x_80 = lean_nat_add(x_4, x_64);
lean_dec(x_64);
lean_dec(x_4);
lean_inc(x_80);
x_81 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__3(x_3, x_5, x_80);
lean_inc(x_81);
lean_inc(x_3);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_3);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set(x_82, 2, x_5);
x_83 = lean_nat_add(x_81, x_7);
x_84 = lean_string_utf8_get(x_3, x_83);
lean_dec(x_83);
x_85 = l_Lean_idEndEscape;
x_86 = lean_uint32_dec_eq(x_84, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_82);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_string_utf8_extract(x_3, x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_3);
x_90 = l_Lean_Name_str___override(x_2, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_82);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeName_takeRest(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint32_t x_9; uint8_t x_10; 
x_3 = 46;
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_add(x_5, x_7);
x_9 = lean_string_utf8_get(x_4, x_8);
lean_dec(x_8);
x_10 = lean_uint32_dec_eq(x_9, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = l_Substring_nextn(x_1, x_12, x_7);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_1, 2);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_1, 0);
lean_dec(x_17);
x_18 = lean_nat_add(x_5, x_13);
lean_dec(x_13);
lean_ctor_set(x_1, 1, x_18);
lean_inc(x_2);
x_19 = l_Lake_takeNamePart(x_1, x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Lean_Name_isAnonymous(x_22);
if (x_23 == 0)
{
lean_free_object(x_19);
lean_dec(x_5);
lean_dec(x_2);
x_1 = x_21;
x_2 = x_22;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_21, 1);
lean_dec(x_26);
lean_ctor_set(x_21, 1, x_5);
lean_ctor_set(x_19, 1, x_2);
return x_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 2);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_29);
return x_19;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = l_Lean_Name_isAnonymous(x_31);
if (x_32 == 0)
{
lean_dec(x_5);
lean_dec(x_2);
x_1 = x_30;
x_2 = x_31;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_30, 2);
lean_inc(x_35);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 lean_ctor_release(x_30, 2);
 x_36 = x_30;
} else {
 lean_dec_ref(x_30);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 3, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_5);
lean_ctor_set(x_37, 2, x_35);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_2);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_1);
x_39 = lean_nat_add(x_5, x_13);
lean_dec(x_13);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
lean_ctor_set(x_40, 2, x_6);
lean_inc(x_2);
x_41 = l_Lake_takeNamePart(x_40, x_2);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = l_Lean_Name_isAnonymous(x_43);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_5);
lean_dec(x_2);
x_1 = x_42;
x_2 = x_43;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 2);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 3, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_5);
lean_ctor_set(x_50, 2, x_48);
if (lean_is_scalar(x_44)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_44;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_2);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = l_Lake_takeNamePart(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_Name_isAnonymous(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_free_object(x_3);
x_8 = l_Lake_takeName_takeRest(x_5, x_6);
return x_8;
}
else
{
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = l_Lean_Name_isAnonymous(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = l_Lake_takeName_takeRest(x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_2);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_at_end(x_4, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_7 = lean_string_utf8_get_fast(x_4, x_5);
x_8 = 46;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
uint32_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_11 = 43;
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Substring_nextn(x_1, x_14, x_15);
x_17 = lean_nat_add(x_13, x_16);
lean_dec(x_16);
x_18 = lean_nat_add(x_17, x_15);
lean_dec(x_17);
x_19 = lean_string_utf8_get(x_12, x_18);
lean_dec(x_18);
x_20 = lean_uint32_dec_eq(x_19, x_11);
if (x_20 == 0)
{
uint32_t x_21; uint8_t x_22; 
x_21 = 42;
x_22 = lean_uint32_dec_eq(x_19, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_2);
x_23 = lean_box(0);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_2);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_2);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
x_5 = l_Lake_takeName(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Name_isAnonymous(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = l_Lake_Glob_ofString_x3f___lambda__1(x_6, x_7, x_9);
lean_dec(x_6);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Glob_ofString_x3f___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Glob_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected glob", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Glob_decodeToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected string", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Glob_decodeToml(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_string_utf8_byte_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_4);
x_7 = l_Lake_takeName(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Name_isAnonymous(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lake_Glob_ofString_x3f___lambda__1(x_9, x_10, x_12);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lake_Glob_decodeToml___closed__1;
lean_ctor_set(x_7, 1, x_14);
lean_ctor_set(x_7, 0, x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
else
{
uint8_t x_16; 
lean_free_object(x_7);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
x_19 = l_Lake_Glob_decodeToml___closed__1;
lean_ctor_set(x_7, 1, x_19);
lean_ctor_set(x_7, 0, x_2);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_7);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = l_Lean_Name_isAnonymous(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lake_Glob_ofString_x3f___lambda__1(x_21, x_22, x_24);
lean_dec(x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Lake_Glob_decodeToml___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 x_30 = x_25;
} else {
 lean_dec_ref(x_25);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 1, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_22);
lean_dec(x_21);
x_32 = l_Lake_Glob_decodeToml___closed__1;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
}
case 2:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lake_Glob_decodeToml___closed__2;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
case 3:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = l_Lake_Glob_decodeToml___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
default: 
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_1, 1);
lean_dec(x_44);
x_45 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_45);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_1);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Lake_Glob_decodeToml___closed__2;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlGlob(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Glob_decodeToml(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_mk_array(x_8, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lake_LeanOptionValue_decodeToml___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOptionValue_decodeToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected string, boolean, or nonnegative integer", 48, 48);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanOptionValue_decodeToml(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 1:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lake_LeanOptionValue_decodeToml___closed__1;
x_9 = lean_int_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_free_object(x_1);
lean_dec(x_6);
x_10 = lean_nat_abs(x_7);
lean_dec(x_7);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_7);
x_13 = l_Lake_LeanOptionValue_decodeToml___closed__2;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_13);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_1);
x_17 = l_Lake_LeanOptionValue_decodeToml___closed__1;
x_18 = lean_int_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_15);
x_19 = lean_nat_abs(x_16);
lean_dec(x_16);
x_20 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_16);
x_22 = l_Lake_LeanOptionValue_decodeToml___closed__2;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lake_LeanOptionValue_decodeToml___closed__2;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
case 3:
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_30 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_30, 0, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
default: 
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = l_Lake_LeanOptionValue_decodeToml___closed__2;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_34);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_1);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lake_LeanOptionValue_decodeToml___closed__2;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanOptionValue(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_LeanOptionValue_decodeToml(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_mk_array(x_8, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lake_Toml_ppKey(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_10);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_16);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = l_Lake_Toml_ppKey(x_1);
x_24 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_22);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_8, x_3, x_29);
x_3 = x_31;
x_4 = x_32;
goto _start;
}
}
}
}
static lean_object* _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("missing required key: ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected name", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_11; lean_object* x_12; 
x_11 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
lean_inc(x_2);
x_12 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_11, x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = l_Lake_Toml_ppKey(x_2);
lean_dec(x_2);
x_14 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_mk_array(x_19, x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
switch (lean_obj_tag(x_24)) {
case 0:
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_String_toName(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_12);
x_29 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
lean_ctor_set(x_24, 1, x_29);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_mk_array(x_30, x_24);
x_4 = x_31;
goto block_10;
}
else
{
lean_free_object(x_24);
lean_dec(x_26);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_28);
return x_12;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
x_34 = l_String_toName(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_12);
x_35 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_mk_array(x_37, x_36);
x_4 = x_38;
goto block_10;
}
else
{
lean_dec(x_32);
lean_dec(x_2);
lean_ctor_set(x_12, 0, x_34);
return x_12;
}
}
}
case 2:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_free_object(x_12);
x_39 = lean_ctor_get(x_24, 0);
lean_inc(x_39);
lean_dec(x_24);
x_40 = l_Lake_Glob_decodeToml___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_mk_array(x_42, x_41);
x_4 = x_43;
goto block_10;
}
case 3:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_12);
x_44 = lean_ctor_get(x_24, 0);
lean_inc(x_44);
lean_dec(x_24);
x_45 = l_Lake_Glob_decodeToml___closed__2;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_mk_array(x_47, x_46);
x_4 = x_48;
goto block_10;
}
default: 
{
uint8_t x_49; 
lean_free_object(x_12);
x_49 = !lean_is_exclusive(x_24);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_24, 1);
lean_dec(x_50);
x_51 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 1, x_51);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_mk_array(x_52, x_24);
x_4 = x_53;
goto block_10;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_24, 0);
lean_inc(x_54);
lean_dec(x_24);
x_55 = l_Lake_Glob_decodeToml___closed__2;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_mk_array(x_57, x_56);
x_4 = x_58;
goto block_10;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_12, 0);
lean_inc(x_59);
lean_dec(x_12);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
switch (lean_obj_tag(x_60)) {
case 0:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = l_String_toName(x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_mk_array(x_67, x_66);
x_4 = x_68;
goto block_10;
}
else
{
lean_object* x_69; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_2);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
return x_69;
}
}
case 2:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_60, 0);
lean_inc(x_70);
lean_dec(x_60);
x_71 = l_Lake_Glob_decodeToml___closed__2;
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_mk_array(x_73, x_72);
x_4 = x_74;
goto block_10;
}
case 3:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_60, 0);
lean_inc(x_75);
lean_dec(x_60);
x_76 = l_Lake_Glob_decodeToml___closed__2;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_mk_array(x_78, x_77);
x_4 = x_79;
goto block_10;
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_60, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_81 = x_60;
} else {
 lean_dec_ref(x_60);
 x_81 = lean_box(0);
}
x_82 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
 lean_ctor_set_tag(x_83, 0);
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_mk_array(x_84, x_83);
x_4 = x_85;
goto block_10;
}
}
}
}
block_10:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2(x_2, x_6, x_7, x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lake_Toml_ppKey(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_10);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_16);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = l_Lake_Toml_ppKey(x_1);
x_24 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_22);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_8, x_3, x_29);
x_3 = x_31;
x_4 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
lean_inc(x_2);
x_5 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_4, x_2, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = l_Lake_Toml_ppKey(x_2);
lean_dec(x_2);
x_7 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_10 = lean_string_append(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lake_LeanOptionValue_decodeToml(x_16);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_mk_array(x_20, x_19);
x_22 = lean_array_get_size(x_21);
x_23 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_24 = 0;
x_25 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__4(x_2, x_23, x_24, x_21);
lean_dec(x_2);
lean_ctor_set(x_17, 0, x_25);
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_mk_array(x_27, x_26);
x_29 = lean_array_get_size(x_28);
x_30 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_31 = 0;
x_32 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__4(x_2, x_30, x_31, x_28);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_17, 0);
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected array or table", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected array of size 2", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanOption_decodeToml___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_LeanOption_decodeToml___closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__4;
x_2 = l_Array_isEmpty___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanOption_decodeToml___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanOption_decodeToml___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanOption_decodeToml(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = l_Lake_LeanOption_decodeToml___closed__2;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_LeanOption_decodeToml___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lake_LeanOption_decodeToml___closed__2;
x_12 = lean_array_push(x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_LeanOption_decodeToml___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lake_LeanOption_decodeToml___closed__2;
x_18 = lean_array_push(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_LeanOption_decodeToml___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_LeanOption_decodeToml___closed__2;
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 5:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_28 = x_1;
} else {
 lean_dec_ref(x_1);
 x_28 = lean_box(0);
}
x_29 = lean_array_get_size(x_27);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
x_32 = l_Lake_LeanOption_decodeToml___closed__3;
if (lean_is_scalar(x_28)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_28;
 lean_ctor_set_tag(x_33, 0);
}
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lake_LeanOption_decodeToml___closed__2;
x_35 = lean_array_push(x_34, x_33);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_69; 
lean_dec(x_26);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_array_fget(x_27, x_37);
switch (lean_obj_tag(x_38)) {
case 0:
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_38);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_38, 0);
x_103 = lean_ctor_get(x_38, 1);
x_104 = l_String_toName(x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
lean_ctor_set(x_38, 1, x_105);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_mk_array(x_106, x_38);
x_39 = x_107;
goto block_68;
}
else
{
lean_free_object(x_38);
lean_dec(x_102);
lean_dec(x_28);
x_69 = x_104;
goto block_100;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_38, 0);
x_109 = lean_ctor_get(x_38, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_38);
x_110 = l_String_toName(x_109);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_108);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_mk_array(x_113, x_112);
x_39 = x_114;
goto block_68;
}
else
{
lean_dec(x_108);
lean_dec(x_28);
x_69 = x_110;
goto block_100;
}
}
}
case 2:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_38, 0);
lean_inc(x_115);
lean_dec(x_38);
x_116 = l_Lake_Glob_decodeToml___closed__2;
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_mk_array(x_118, x_117);
x_39 = x_119;
goto block_68;
}
case 3:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_38, 0);
lean_inc(x_120);
lean_dec(x_38);
x_121 = l_Lake_Glob_decodeToml___closed__2;
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_mk_array(x_123, x_122);
x_39 = x_124;
goto block_68;
}
default: 
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_38);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_38, 1);
lean_dec(x_126);
x_127 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_38, 0);
lean_ctor_set(x_38, 1, x_127);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_mk_array(x_128, x_38);
x_39 = x_129;
goto block_68;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_38, 0);
lean_inc(x_130);
lean_dec(x_38);
x_131 = l_Lake_Glob_decodeToml___closed__2;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_mk_array(x_133, x_132);
x_39 = x_134;
goto block_68;
}
}
}
block_68:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = l_Lake_LeanOption_decodeToml___closed__4;
x_41 = l_Array_append___rarg(x_40, x_39);
lean_dec(x_39);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_array_fget(x_27, x_42);
lean_dec(x_27);
x_44 = l_Lake_LeanOptionValue_decodeToml(x_43);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec(x_28);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_mk_array(x_42, x_46);
x_48 = l_Array_append___rarg(x_41, x_47);
lean_dec(x_47);
x_49 = l_Array_isEmpty___rarg(x_48);
if (x_49 == 0)
{
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_50; 
lean_dec(x_48);
lean_free_object(x_44);
x_50 = l_Lake_LeanOption_decodeToml___closed__7;
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_mk_array(x_42, x_51);
x_53 = l_Array_append___rarg(x_41, x_52);
lean_dec(x_52);
x_54 = l_Array_isEmpty___rarg(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_53);
return x_55;
}
else
{
lean_object* x_56; 
lean_dec(x_53);
x_56 = l_Lake_LeanOption_decodeToml___closed__7;
return x_56;
}
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_44);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_44, 0);
x_59 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_28;
 lean_ctor_set_tag(x_60, 0);
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
x_61 = l_Array_isEmpty___rarg(x_41);
if (x_61 == 0)
{
lean_dec(x_60);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 0, x_41);
return x_44;
}
else
{
lean_dec(x_41);
lean_ctor_set(x_44, 0, x_60);
return x_44;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_44, 0);
lean_inc(x_62);
lean_dec(x_44);
x_63 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_28;
 lean_ctor_set_tag(x_64, 0);
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_65 = l_Array_isEmpty___rarg(x_41);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_41);
return x_66;
}
else
{
lean_object* x_67; 
lean_dec(x_41);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_64);
return x_67;
}
}
}
}
block_100:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_array_fget(x_27, x_70);
lean_dec(x_27);
x_72 = l_Lake_LeanOptionValue_decodeToml(x_71);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_mk_array(x_70, x_74);
x_76 = l_Lake_LeanOption_decodeToml___closed__4;
x_77 = l_Array_append___rarg(x_76, x_75);
lean_dec(x_75);
x_78 = l_Lake_LeanOption_decodeToml___closed__5;
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_69);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Array_isEmpty___rarg(x_77);
if (x_80 == 0)
{
lean_dec(x_79);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
else
{
lean_dec(x_77);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 0, x_79);
return x_72;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
lean_dec(x_72);
x_82 = lean_mk_array(x_70, x_81);
x_83 = l_Lake_LeanOption_decodeToml___closed__4;
x_84 = l_Array_append___rarg(x_83, x_82);
lean_dec(x_82);
x_85 = l_Lake_LeanOption_decodeToml___closed__5;
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_69);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Array_isEmpty___rarg(x_84);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_86);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_84);
return x_88;
}
else
{
lean_object* x_89; 
lean_dec(x_84);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_86);
return x_89;
}
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_72);
if (x_90 == 0)
{
lean_object* x_91; uint8_t x_92; 
x_91 = lean_ctor_get(x_72, 0);
x_92 = l_Lake_LeanOption_decodeToml___closed__8;
if (x_92 == 0)
{
lean_object* x_93; 
lean_free_object(x_72);
lean_dec(x_91);
lean_dec(x_69);
x_93 = l_Lake_LeanOption_decodeToml___closed__9;
return x_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_69);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_72, 0, x_94);
return x_72;
}
}
else
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_72, 0);
lean_inc(x_95);
lean_dec(x_72);
x_96 = l_Lake_LeanOption_decodeToml___closed__8;
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_95);
lean_dec(x_69);
x_97 = l_Lake_LeanOption_decodeToml___closed__9;
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_69);
lean_ctor_set(x_98, 1, x_95);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
return x_99;
}
}
}
}
}
}
case 6:
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_1);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_1, 0);
x_137 = lean_ctor_get(x_1, 1);
x_138 = l_Lake_LeanOption_decodeToml___closed__11;
lean_inc(x_136);
lean_inc(x_137);
x_139 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(x_137, x_138, x_136);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lake_LeanOption_decodeToml___closed__4;
x_142 = l_Array_append___rarg(x_141, x_140);
lean_dec(x_140);
x_143 = l_Lake_LeanOption_decodeToml___closed__13;
x_144 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__3(x_137, x_143, x_136);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
lean_free_object(x_1);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = l_Array_append___rarg(x_142, x_146);
lean_dec(x_146);
x_148 = l_Array_isEmpty___rarg(x_147);
if (x_148 == 0)
{
lean_ctor_set(x_144, 0, x_147);
return x_144;
}
else
{
lean_object* x_149; 
lean_dec(x_147);
lean_free_object(x_144);
x_149 = l_Lake_LeanOption_decodeToml___closed__7;
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
lean_dec(x_144);
x_151 = l_Array_append___rarg(x_142, x_150);
lean_dec(x_150);
x_152 = l_Array_isEmpty___rarg(x_151);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
else
{
lean_object* x_154; 
lean_dec(x_151);
x_154 = l_Lake_LeanOption_decodeToml___closed__7;
return x_154;
}
}
}
else
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_144);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_144, 0);
x_157 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_156);
lean_ctor_set(x_1, 0, x_157);
x_158 = l_Array_isEmpty___rarg(x_142);
if (x_158 == 0)
{
lean_dec(x_1);
lean_ctor_set_tag(x_144, 0);
lean_ctor_set(x_144, 0, x_142);
return x_144;
}
else
{
lean_dec(x_142);
lean_ctor_set(x_144, 0, x_1);
return x_144;
}
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = lean_ctor_get(x_144, 0);
lean_inc(x_159);
lean_dec(x_144);
x_160 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_159);
lean_ctor_set(x_1, 0, x_160);
x_161 = l_Array_isEmpty___rarg(x_142);
if (x_161 == 0)
{
lean_object* x_162; 
lean_dec(x_1);
x_162 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_162, 0, x_142);
return x_162;
}
else
{
lean_object* x_163; 
lean_dec(x_142);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_1);
return x_163;
}
}
}
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_139, 0);
lean_inc(x_164);
lean_dec(x_139);
x_165 = l_Lake_LeanOption_decodeToml___closed__13;
x_166 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__3(x_137, x_165, x_136);
if (lean_obj_tag(x_166) == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = l_Lake_LeanOption_decodeToml___closed__4;
x_170 = l_Array_append___rarg(x_169, x_168);
lean_dec(x_168);
x_171 = l_Lake_LeanOption_decodeToml___closed__5;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_171);
lean_ctor_set(x_1, 0, x_164);
x_172 = l_Array_isEmpty___rarg(x_170);
if (x_172 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_166, 0, x_170);
return x_166;
}
else
{
lean_dec(x_170);
lean_ctor_set_tag(x_166, 1);
lean_ctor_set(x_166, 0, x_1);
return x_166;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_173 = lean_ctor_get(x_166, 0);
lean_inc(x_173);
lean_dec(x_166);
x_174 = l_Lake_LeanOption_decodeToml___closed__4;
x_175 = l_Array_append___rarg(x_174, x_173);
lean_dec(x_173);
x_176 = l_Lake_LeanOption_decodeToml___closed__5;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_176);
lean_ctor_set(x_1, 0, x_164);
x_177 = l_Array_isEmpty___rarg(x_175);
if (x_177 == 0)
{
lean_object* x_178; 
lean_dec(x_1);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_175);
return x_178;
}
else
{
lean_object* x_179; 
lean_dec(x_175);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_1);
return x_179;
}
}
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_166);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_166, 0);
x_182 = l_Lake_LeanOption_decodeToml___closed__8;
if (x_182 == 0)
{
lean_object* x_183; 
lean_free_object(x_166);
lean_dec(x_181);
lean_dec(x_164);
lean_free_object(x_1);
x_183 = l_Lake_LeanOption_decodeToml___closed__9;
return x_183;
}
else
{
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_181);
lean_ctor_set(x_1, 0, x_164);
lean_ctor_set(x_166, 0, x_1);
return x_166;
}
}
else
{
lean_object* x_184; uint8_t x_185; 
x_184 = lean_ctor_get(x_166, 0);
lean_inc(x_184);
lean_dec(x_166);
x_185 = l_Lake_LeanOption_decodeToml___closed__8;
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_184);
lean_dec(x_164);
lean_free_object(x_1);
x_186 = l_Lake_LeanOption_decodeToml___closed__9;
return x_186;
}
else
{
lean_object* x_187; 
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_184);
lean_ctor_set(x_1, 0, x_164);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_1);
return x_187;
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_1, 0);
x_189 = lean_ctor_get(x_1, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_1);
x_190 = l_Lake_LeanOption_decodeToml___closed__11;
lean_inc(x_188);
lean_inc(x_189);
x_191 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(x_189, x_190, x_188);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec(x_191);
x_193 = l_Lake_LeanOption_decodeToml___closed__4;
x_194 = l_Array_append___rarg(x_193, x_192);
lean_dec(x_192);
x_195 = l_Lake_LeanOption_decodeToml___closed__13;
x_196 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__3(x_189, x_195, x_188);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = l_Array_append___rarg(x_194, x_197);
lean_dec(x_197);
x_200 = l_Array_isEmpty___rarg(x_199);
if (x_200 == 0)
{
lean_object* x_201; 
if (lean_is_scalar(x_198)) {
 x_201 = lean_alloc_ctor(0, 1, 0);
} else {
 x_201 = x_198;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
else
{
lean_object* x_202; 
lean_dec(x_199);
lean_dec(x_198);
x_202 = l_Lake_LeanOption_decodeToml___closed__7;
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_203 = lean_ctor_get(x_196, 0);
lean_inc(x_203);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_204 = x_196;
} else {
 lean_dec_ref(x_196);
 x_204 = lean_box(0);
}
x_205 = lean_box(0);
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_203);
x_207 = l_Array_isEmpty___rarg(x_194);
if (x_207 == 0)
{
lean_object* x_208; 
lean_dec(x_206);
if (lean_is_scalar(x_204)) {
 x_208 = lean_alloc_ctor(0, 1, 0);
} else {
 x_208 = x_204;
 lean_ctor_set_tag(x_208, 0);
}
lean_ctor_set(x_208, 0, x_194);
return x_208;
}
else
{
lean_object* x_209; 
lean_dec(x_194);
if (lean_is_scalar(x_204)) {
 x_209 = lean_alloc_ctor(1, 1, 0);
} else {
 x_209 = x_204;
}
lean_ctor_set(x_209, 0, x_206);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_191, 0);
lean_inc(x_210);
lean_dec(x_191);
x_211 = l_Lake_LeanOption_decodeToml___closed__13;
x_212 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__3(x_189, x_211, x_188);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
x_215 = l_Lake_LeanOption_decodeToml___closed__4;
x_216 = l_Array_append___rarg(x_215, x_213);
lean_dec(x_213);
x_217 = l_Lake_LeanOption_decodeToml___closed__5;
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_210);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Array_isEmpty___rarg(x_216);
if (x_219 == 0)
{
lean_object* x_220; 
lean_dec(x_218);
if (lean_is_scalar(x_214)) {
 x_220 = lean_alloc_ctor(0, 1, 0);
} else {
 x_220 = x_214;
}
lean_ctor_set(x_220, 0, x_216);
return x_220;
}
else
{
lean_object* x_221; 
lean_dec(x_216);
if (lean_is_scalar(x_214)) {
 x_221 = lean_alloc_ctor(1, 1, 0);
} else {
 x_221 = x_214;
 lean_ctor_set_tag(x_221, 1);
}
lean_ctor_set(x_221, 0, x_218);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_ctor_get(x_212, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_223 = x_212;
} else {
 lean_dec_ref(x_212);
 x_223 = lean_box(0);
}
x_224 = l_Lake_LeanOption_decodeToml___closed__8;
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_210);
x_225 = l_Lake_LeanOption_decodeToml___closed__9;
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; 
x_226 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_226, 0, x_210);
lean_ctor_set(x_226, 1, x_222);
if (lean_is_scalar(x_223)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_223;
}
lean_ctor_set(x_227, 0, x_226);
return x_227;
}
}
}
}
}
default: 
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_1);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_1, 1);
lean_dec(x_229);
x_230 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_230);
x_231 = l_Lake_LeanOption_decodeToml___closed__2;
x_232 = lean_array_push(x_231, x_1);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_1, 0);
lean_inc(x_234);
lean_dec(x_1);
x_235 = l_Lake_LeanOption_decodeToml___closed__1;
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = l_Lake_LeanOption_decodeToml___closed__2;
x_238 = lean_array_push(x_237, x_236);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_instDecodeTomlLeanOption___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanOption_decodeToml), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instDecodeTomlLeanOption() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instDecodeTomlLeanOption___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_BuildType_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildType_decodeToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("relWithDebInfo", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildType_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("minSizeRel", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildType_decodeToml___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("release", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildType_decodeToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected one of 'debug', 'relWithDebInfo', 'minSizeRel', 'release'", 66, 66);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildType_decodeToml___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildType_decodeToml___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildType_decodeToml___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildType_decodeToml___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildType_decodeToml(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_BuildType_decodeToml___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lake_BuildType_decodeToml___closed__2;
x_8 = lean_string_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lake_BuildType_decodeToml___closed__3;
x_10 = lean_string_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lake_BuildType_decodeToml___closed__4;
x_12 = lean_string_dec_eq(x_4, x_11);
lean_dec(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lake_BuildType_decodeToml___closed__5;
lean_ctor_set(x_1, 1, x_13);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_1);
return x_14;
}
else
{
lean_object* x_15; 
lean_free_object(x_1);
lean_dec(x_3);
x_15 = l_Lake_BuildType_decodeToml___closed__6;
return x_15;
}
}
else
{
lean_object* x_16; 
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
x_16 = l_Lake_BuildType_decodeToml___closed__7;
return x_16;
}
}
else
{
lean_object* x_17; 
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
x_17 = l_Lake_BuildType_decodeToml___closed__8;
return x_17;
}
}
else
{
lean_object* x_18; 
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
x_18 = l_Lake_BuildType_decodeToml___closed__9;
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l_Lake_BuildType_decodeToml___closed__1;
x_22 = lean_string_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l_Lake_BuildType_decodeToml___closed__2;
x_24 = lean_string_dec_eq(x_20, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lake_BuildType_decodeToml___closed__3;
x_26 = lean_string_dec_eq(x_20, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lake_BuildType_decodeToml___closed__4;
x_28 = lean_string_dec_eq(x_20, x_27);
lean_dec(x_20);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lake_BuildType_decodeToml___closed__5;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_19);
x_32 = l_Lake_BuildType_decodeToml___closed__6;
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_19);
x_33 = l_Lake_BuildType_decodeToml___closed__7;
return x_33;
}
}
else
{
lean_object* x_34; 
lean_dec(x_20);
lean_dec(x_19);
x_34 = l_Lake_BuildType_decodeToml___closed__8;
return x_34;
}
}
else
{
lean_object* x_35; 
lean_dec(x_20);
lean_dec(x_19);
x_35 = l_Lake_BuildType_decodeToml___closed__9;
return x_35;
}
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lake_Glob_decodeToml___closed__2;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
case 3:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l_Lake_Glob_decodeToml___closed__2;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
default: 
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_46);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_1);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = l_Lake_Glob_decodeToml___closed__2;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlBuildType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildType_decodeToml(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_mk_array(x_8, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
static lean_object* _init_l_Lake_Backend_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("c", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Backend_decodeToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("llvm", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Backend_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("default", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Backend_decodeToml___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected one of 'c', 'llvm', or 'default'", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_Backend_decodeToml___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Backend_decodeToml___closed__6() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Backend_decodeToml___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Backend_decodeToml(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_Backend_decodeToml___closed__1;
x_6 = lean_string_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lake_Backend_decodeToml___closed__2;
x_8 = lean_string_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lake_Backend_decodeToml___closed__3;
x_10 = lean_string_dec_eq(x_4, x_9);
lean_dec(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lake_Backend_decodeToml___closed__4;
lean_ctor_set(x_1, 1, x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; 
lean_free_object(x_1);
lean_dec(x_3);
x_13 = l_Lake_Backend_decodeToml___closed__5;
return x_13;
}
}
else
{
lean_object* x_14; 
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
x_14 = l_Lake_Backend_decodeToml___closed__6;
return x_14;
}
}
else
{
lean_object* x_15; 
lean_free_object(x_1);
lean_dec(x_4);
lean_dec(x_3);
x_15 = l_Lake_Backend_decodeToml___closed__7;
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = l_Lake_Backend_decodeToml___closed__1;
x_19 = lean_string_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lake_Backend_decodeToml___closed__2;
x_21 = lean_string_dec_eq(x_17, x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lake_Backend_decodeToml___closed__3;
x_23 = lean_string_dec_eq(x_17, x_22);
lean_dec(x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lake_Backend_decodeToml___closed__4;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; 
lean_dec(x_16);
x_27 = l_Lake_Backend_decodeToml___closed__5;
return x_27;
}
}
else
{
lean_object* x_28; 
lean_dec(x_17);
lean_dec(x_16);
x_28 = l_Lake_Backend_decodeToml___closed__6;
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_17);
lean_dec(x_16);
x_29 = l_Lake_Backend_decodeToml___closed__7;
return x_29;
}
}
}
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lake_Glob_decodeToml___closed__2;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
case 3:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lake_Glob_decodeToml___closed__2;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
default: 
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_1, 1);
lean_dec(x_39);
x_40 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_40);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_1);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lake_Glob_decodeToml___closed__2;
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlBackend(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Backend_decodeToml(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_4);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_mk_array(x_8, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_1);
x_12 = l_Lean_Name_append(x_1, x_10);
x_13 = l_Lake_decodeLeanOptionsAux(x_11, x_12, x_5);
x_3 = x_9;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptionsAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptionsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_array_get_size(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_lt(x_7, x_6);
if (x_8 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_9; 
x_9 = lean_nat_dec_le(x_6, x_6);
if (x_9 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = 0;
x_11 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1(x_2, x_5, x_10, x_11, x_3);
lean_dec(x_5);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lake_LeanOptionValue_decodeToml(x_1);
x_14 = lean_alloc_closure((void*)(l_Lake_decodeLeanOptionsAux___lambda__1), 3, 1);
lean_closure_set(x_14, 0, x_2);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_array(x_17, x_16);
lean_ctor_set(x_13, 0, x_18);
x_19 = l_Lake_mergeErrors___rarg(x_3, x_13, x_14);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_array(x_21, x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lake_mergeErrors___rarg(x_3, x_23, x_14);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lake_mergeErrors___rarg(x_3, x_13, x_14);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lake_mergeErrors___rarg(x_3, x_28, x_14);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Array_push___boxed), 3, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_LeanOption_decodeToml(x_6);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_9 = l_Lake_mergeErrors___rarg(x_4, x_7, x_8);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_2, x_2);
if (x_7 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lake_decodeLeanOptionsAux(x_10, x_9, x_4);
x_2 = x_8;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lake_decodeLeanOptions___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__4;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptions(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = l_Lake_LeanOption_decodeToml___closed__2;
x_6 = lean_array_push(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_LeanOption_decodeToml___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lake_LeanOption_decodeToml___closed__2;
x_12 = lean_array_push(x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_LeanOption_decodeToml___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lake_LeanOption_decodeToml___closed__2;
x_18 = lean_array_push(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_LeanOption_decodeToml___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_LeanOption_decodeToml___closed__2;
x_24 = lean_array_push(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 5:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1(x_26);
lean_dec(x_26);
return x_27;
}
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_array_get_size(x_29);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_lt(x_31, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_29);
x_33 = l_Lake_decodeLeanOptions___closed__1;
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_30, x_30);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_29);
x_35 = l_Lake_decodeLeanOptions___closed__1;
return x_35;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = 0;
x_37 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_38 = l_Lake_decodeLeanOptions___closed__1;
x_39 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__3(x_29, x_36, x_37, x_38);
lean_dec(x_29);
return x_39;
}
}
}
default: 
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_1, 1);
lean_dec(x_41);
x_42 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_42);
x_43 = l_Lake_LeanOption_decodeToml___closed__2;
x_44 = lean_array_push(x_43, x_1);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
lean_dec(x_1);
x_47 = l_Lake_LeanOption_decodeToml___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lake_LeanOption_decodeToml___closed__2;
x_50 = lean_array_push(x_49, x_48);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("packagesDir", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_decodeToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_WorkspaceConfig_decodeToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_decodeToml(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_9 = l_Lake_WorkspaceConfig_decodeToml___closed__2;
x_10 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_8, x_9, x_1);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lake_defaultPackagesDir;
x_12 = l_Lake_LeanOption_decodeToml___closed__4;
x_2 = x_11;
x_3 = x_12;
goto block_7;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lake_LeanOption_decodeToml___closed__4;
x_2 = x_15;
x_3 = x_16;
goto block_7;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Lake_Glob_decodeToml___closed__2;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_mk_array(x_20, x_19);
x_22 = l_Lake_LeanOption_decodeToml___closed__4;
x_23 = l_Array_append___rarg(x_22, x_21);
lean_dec(x_21);
x_24 = l_Lake_defaultPackagesDir;
x_2 = x_24;
x_3 = x_23;
goto block_7;
}
case 3:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = l_Lake_Glob_decodeToml___closed__2;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_mk_array(x_28, x_27);
x_30 = l_Lake_LeanOption_decodeToml___closed__4;
x_31 = l_Array_append___rarg(x_30, x_29);
lean_dec(x_29);
x_32 = l_Lake_defaultPackagesDir;
x_2 = x_32;
x_3 = x_31;
goto block_7;
}
default: 
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_14);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_14, 1);
lean_dec(x_34);
x_35 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_14, 0);
lean_ctor_set(x_14, 1, x_35);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_mk_array(x_36, x_14);
x_38 = l_Lake_LeanOption_decodeToml___closed__4;
x_39 = l_Array_append___rarg(x_38, x_37);
lean_dec(x_37);
x_40 = l_Lake_defaultPackagesDir;
x_2 = x_40;
x_3 = x_39;
goto block_7;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_14, 0);
lean_inc(x_41);
lean_dec(x_14);
x_42 = l_Lake_Glob_decodeToml___closed__2;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_mk_array(x_44, x_43);
x_46 = l_Lake_LeanOption_decodeToml___closed__4;
x_47 = l_Array_append___rarg(x_46, x_45);
lean_dec(x_45);
x_48 = l_Lake_defaultPackagesDir;
x_2 = x_48;
x_3 = x_47;
goto block_7;
}
}
}
}
block_7:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
}
}
static lean_object* _init_l_Lake_instDecodeTomlWorkspaceConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected table", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlWorkspaceConfig(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 6:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lake_WorkspaceConfig_decodeToml(x_26);
return x_27;
}
default: 
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_1, 1);
lean_dec(x_29);
x_30 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_mk_array(x_31, x_1);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_mk_array(x_37, x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanConfig_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_12 = l_Lake_mergeErrors___rarg(x_4, x_10, x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
lean_inc(x_14);
lean_dec(x_6);
x_15 = l_Lake_Glob_decodeToml___closed__2;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_21 = l_Lake_mergeErrors___rarg(x_4, x_19, x_20);
x_2 = x_8;
x_4 = x_21;
goto _start;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
x_24 = l_Lake_Glob_decodeToml___closed__2;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_mk_array(x_26, x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_30 = l_Lake_mergeErrors___rarg(x_4, x_28, x_29);
x_2 = x_8;
x_4 = x_30;
goto _start;
}
default: 
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_6);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_6, 1);
lean_dec(x_33);
x_34 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_34);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_mk_array(x_35, x_6);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_39 = l_Lake_mergeErrors___rarg(x_4, x_37, x_38);
x_2 = x_8;
x_4 = x_39;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_6, 0);
lean_inc(x_41);
lean_dec(x_6);
x_42 = l_Lake_Glob_decodeToml___closed__2;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_mk_array(x_44, x_43);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_48 = l_Lake_mergeErrors___rarg(x_4, x_46, x_47);
x_2 = x_8;
x_4 = x_48;
goto _start;
}
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_2, x_2);
if (x_7 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_LeanConfig_decodeToml___spec__2(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreLeanArgs", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("weakLinkArgs", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected array", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreLinkArgs", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("weakLeancArgs", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreLeancArgs", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("weakLeanArgs", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreServerOptions", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanOptions", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("platformIndependent", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected boolean", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backend", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__21;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("buildType", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanConfig_decodeToml___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanConfig_decodeToml___closed__23;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanConfig_decodeToml(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_8; lean_object* x_9; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_472 = l_Lake_LeanConfig_decodeToml___closed__24;
lean_inc(x_1);
x_473 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_471, x_472, x_1);
if (lean_obj_tag(x_473) == 0)
{
uint8_t x_474; lean_object* x_475; 
x_474 = 3;
x_475 = l_Lake_LeanOption_decodeToml___closed__4;
x_8 = x_474;
x_9 = x_475;
goto block_470;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_473, 0);
lean_inc(x_476);
lean_dec(x_473);
x_477 = lean_ctor_get(x_476, 1);
lean_inc(x_477);
lean_dec(x_476);
x_478 = l_Lake_BuildType_decodeToml(x_477);
if (lean_obj_tag(x_478) == 0)
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; 
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
lean_dec(x_478);
x_480 = lean_unsigned_to_nat(1u);
x_481 = lean_mk_array(x_480, x_479);
x_482 = l_Lake_LeanOption_decodeToml___closed__4;
x_483 = l_Array_append___rarg(x_482, x_481);
lean_dec(x_481);
x_484 = 3;
x_8 = x_484;
x_9 = x_483;
goto block_470;
}
else
{
lean_object* x_485; lean_object* x_486; uint8_t x_487; 
x_485 = lean_ctor_get(x_478, 0);
lean_inc(x_485);
lean_dec(x_478);
x_486 = l_Lake_LeanOption_decodeToml___closed__4;
x_487 = lean_unbox(x_485);
lean_dec(x_485);
x_8 = x_487;
x_9 = x_486;
goto block_470;
}
}
block_7:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___rarg(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
}
block_470:
{
uint8_t x_10; lean_object* x_11; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_457 = l_Lake_LeanConfig_decodeToml___closed__22;
lean_inc(x_1);
x_458 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_456, x_457, x_1);
if (lean_obj_tag(x_458) == 0)
{
uint8_t x_459; 
x_459 = 2;
x_10 = x_459;
x_11 = x_9;
goto block_455;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_458, 0);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
lean_dec(x_460);
x_462 = l_Lake_Backend_decodeToml(x_461);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
lean_dec(x_462);
x_464 = lean_unsigned_to_nat(1u);
x_465 = lean_mk_array(x_464, x_463);
x_466 = l_Array_append___rarg(x_9, x_465);
lean_dec(x_465);
x_467 = 2;
x_10 = x_467;
x_11 = x_466;
goto block_455;
}
else
{
lean_object* x_468; uint8_t x_469; 
x_468 = lean_ctor_get(x_462, 0);
lean_inc(x_468);
lean_dec(x_462);
x_469 = lean_unbox(x_468);
lean_dec(x_468);
x_10 = x_469;
x_11 = x_9;
goto block_455;
}
}
block_455:
{
lean_object* x_12; lean_object* x_13; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_391 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_392 = l_Lake_LeanConfig_decodeToml___closed__19;
lean_inc(x_1);
x_393 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_391, x_392, x_1);
x_394 = lean_box(0);
if (lean_obj_tag(x_393) == 0)
{
x_12 = x_394;
x_13 = x_11;
goto block_390;
}
else
{
uint8_t x_395; 
x_395 = !lean_is_exclusive(x_393);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; 
x_396 = lean_ctor_get(x_393, 0);
x_397 = lean_ctor_get(x_396, 1);
lean_inc(x_397);
lean_dec(x_396);
switch (lean_obj_tag(x_397)) {
case 0:
{
uint8_t x_398; 
lean_free_object(x_393);
x_398 = !lean_is_exclusive(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_399 = lean_ctor_get(x_397, 1);
lean_dec(x_399);
x_400 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_397, 1, x_400);
x_401 = lean_unsigned_to_nat(1u);
x_402 = lean_mk_array(x_401, x_397);
x_403 = l_Array_append___rarg(x_11, x_402);
lean_dec(x_402);
x_12 = x_394;
x_13 = x_403;
goto block_390;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_404 = lean_ctor_get(x_397, 0);
lean_inc(x_404);
lean_dec(x_397);
x_405 = l_Lake_LeanConfig_decodeToml___closed__20;
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
x_407 = lean_unsigned_to_nat(1u);
x_408 = lean_mk_array(x_407, x_406);
x_409 = l_Array_append___rarg(x_11, x_408);
lean_dec(x_408);
x_12 = x_394;
x_13 = x_409;
goto block_390;
}
}
case 2:
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_free_object(x_393);
x_410 = lean_ctor_get(x_397, 0);
lean_inc(x_410);
lean_dec(x_397);
x_411 = l_Lake_LeanConfig_decodeToml___closed__20;
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
x_413 = lean_unsigned_to_nat(1u);
x_414 = lean_mk_array(x_413, x_412);
x_415 = l_Array_append___rarg(x_11, x_414);
lean_dec(x_414);
x_12 = x_394;
x_13 = x_415;
goto block_390;
}
case 3:
{
uint8_t x_416; lean_object* x_417; 
x_416 = lean_ctor_get_uint8(x_397, sizeof(void*)*1);
lean_dec(x_397);
x_417 = lean_box(x_416);
lean_ctor_set(x_393, 0, x_417);
x_12 = x_393;
x_13 = x_11;
goto block_390;
}
default: 
{
uint8_t x_418; 
lean_free_object(x_393);
x_418 = !lean_is_exclusive(x_397);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_419 = lean_ctor_get(x_397, 1);
lean_dec(x_419);
x_420 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_397, 0);
lean_ctor_set(x_397, 1, x_420);
x_421 = lean_unsigned_to_nat(1u);
x_422 = lean_mk_array(x_421, x_397);
x_423 = l_Array_append___rarg(x_11, x_422);
lean_dec(x_422);
x_12 = x_394;
x_13 = x_423;
goto block_390;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_ctor_get(x_397, 0);
lean_inc(x_424);
lean_dec(x_397);
x_425 = l_Lake_LeanConfig_decodeToml___closed__20;
x_426 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
x_427 = lean_unsigned_to_nat(1u);
x_428 = lean_mk_array(x_427, x_426);
x_429 = l_Array_append___rarg(x_11, x_428);
lean_dec(x_428);
x_12 = x_394;
x_13 = x_429;
goto block_390;
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; 
x_430 = lean_ctor_get(x_393, 0);
lean_inc(x_430);
lean_dec(x_393);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
lean_dec(x_430);
switch (lean_obj_tag(x_431)) {
case 0:
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_433 = x_431;
} else {
 lean_dec_ref(x_431);
 x_433 = lean_box(0);
}
x_434 = l_Lake_LeanConfig_decodeToml___closed__20;
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_434);
x_436 = lean_unsigned_to_nat(1u);
x_437 = lean_mk_array(x_436, x_435);
x_438 = l_Array_append___rarg(x_11, x_437);
lean_dec(x_437);
x_12 = x_394;
x_13 = x_438;
goto block_390;
}
case 2:
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_439 = lean_ctor_get(x_431, 0);
lean_inc(x_439);
lean_dec(x_431);
x_440 = l_Lake_LeanConfig_decodeToml___closed__20;
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_440);
x_442 = lean_unsigned_to_nat(1u);
x_443 = lean_mk_array(x_442, x_441);
x_444 = l_Array_append___rarg(x_11, x_443);
lean_dec(x_443);
x_12 = x_394;
x_13 = x_444;
goto block_390;
}
case 3:
{
uint8_t x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get_uint8(x_431, sizeof(void*)*1);
lean_dec(x_431);
x_446 = lean_box(x_445);
x_447 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_447, 0, x_446);
x_12 = x_447;
x_13 = x_11;
goto block_390;
}
default: 
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_448 = lean_ctor_get(x_431, 0);
lean_inc(x_448);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_449 = x_431;
} else {
 lean_dec_ref(x_431);
 x_449 = lean_box(0);
}
x_450 = l_Lake_LeanConfig_decodeToml___closed__20;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(0, 2, 0);
} else {
 x_451 = x_449;
 lean_ctor_set_tag(x_451, 0);
}
lean_ctor_set(x_451, 0, x_448);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_unsigned_to_nat(1u);
x_453 = lean_mk_array(x_452, x_451);
x_454 = l_Array_append___rarg(x_11, x_453);
lean_dec(x_453);
x_12 = x_394;
x_13 = x_454;
goto block_390;
}
}
}
}
block_390:
{
lean_object* x_14; lean_object* x_15; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_380 = l_Lake_LeanConfig_decodeToml___closed__17;
lean_inc(x_1);
x_381 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_379, x_380, x_1);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; 
x_382 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_382;
x_15 = x_13;
goto block_378;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
lean_dec(x_381);
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec(x_383);
x_385 = l_Lake_decodeLeanOptions(x_384);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
lean_dec(x_385);
x_387 = l_Array_append___rarg(x_13, x_386);
lean_dec(x_386);
x_388 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_388;
x_15 = x_387;
goto block_378;
}
else
{
lean_object* x_389; 
x_389 = lean_ctor_get(x_385, 0);
lean_inc(x_389);
lean_dec(x_385);
x_14 = x_389;
x_15 = x_13;
goto block_378;
}
}
block_378:
{
lean_object* x_16; lean_object* x_17; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_368 = l_Lake_LeanConfig_decodeToml___closed__15;
lean_inc(x_1);
x_369 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_367, x_368, x_1);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; 
x_370 = l_Lake_LeanOption_decodeToml___closed__4;
x_16 = x_370;
x_17 = x_15;
goto block_366;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_369, 0);
lean_inc(x_371);
lean_dec(x_369);
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
lean_dec(x_371);
x_373 = l_Lake_decodeLeanOptions(x_372);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
lean_dec(x_373);
x_375 = l_Array_append___rarg(x_15, x_374);
lean_dec(x_374);
x_376 = l_Lake_LeanOption_decodeToml___closed__4;
x_16 = x_376;
x_17 = x_375;
goto block_366;
}
else
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_373, 0);
lean_inc(x_377);
lean_dec(x_373);
x_16 = x_377;
x_17 = x_15;
goto block_366;
}
}
block_366:
{
lean_object* x_18; lean_object* x_19; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_313 = l_Lake_LeanConfig_decodeToml___closed__2;
lean_inc(x_1);
x_314 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_312, x_313, x_1);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; 
x_315 = l_Lake_LeanOption_decodeToml___closed__4;
x_18 = x_315;
x_19 = x_17;
goto block_311;
}
else
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_314, 0);
lean_inc(x_316);
lean_dec(x_314);
x_317 = lean_ctor_get(x_316, 1);
lean_inc(x_317);
lean_dec(x_316);
switch (lean_obj_tag(x_317)) {
case 0:
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_319 = lean_ctor_get(x_317, 1);
lean_dec(x_319);
x_320 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_317, 1, x_320);
x_321 = lean_unsigned_to_nat(1u);
x_322 = lean_mk_array(x_321, x_317);
x_323 = l_Array_append___rarg(x_17, x_322);
lean_dec(x_322);
x_324 = l_Lake_LeanOption_decodeToml___closed__4;
x_18 = x_324;
x_19 = x_323;
goto block_311;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_325 = lean_ctor_get(x_317, 0);
lean_inc(x_325);
lean_dec(x_317);
x_326 = l_Lake_LeanConfig_decodeToml___closed__5;
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_unsigned_to_nat(1u);
x_329 = lean_mk_array(x_328, x_327);
x_330 = l_Array_append___rarg(x_17, x_329);
lean_dec(x_329);
x_331 = l_Lake_LeanOption_decodeToml___closed__4;
x_18 = x_331;
x_19 = x_330;
goto block_311;
}
}
case 2:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_332 = lean_ctor_get(x_317, 0);
lean_inc(x_332);
lean_dec(x_317);
x_333 = l_Lake_LeanConfig_decodeToml___closed__5;
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_335 = lean_unsigned_to_nat(1u);
x_336 = lean_mk_array(x_335, x_334);
x_337 = l_Array_append___rarg(x_17, x_336);
lean_dec(x_336);
x_338 = l_Lake_LeanOption_decodeToml___closed__4;
x_18 = x_338;
x_19 = x_337;
goto block_311;
}
case 3:
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_339 = lean_ctor_get(x_317, 0);
lean_inc(x_339);
lean_dec(x_317);
x_340 = l_Lake_LeanConfig_decodeToml___closed__5;
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_unsigned_to_nat(1u);
x_343 = lean_mk_array(x_342, x_341);
x_344 = l_Array_append___rarg(x_17, x_343);
lean_dec(x_343);
x_345 = l_Lake_LeanOption_decodeToml___closed__4;
x_18 = x_345;
x_19 = x_344;
goto block_311;
}
case 5:
{
lean_object* x_346; lean_object* x_347; 
x_346 = lean_ctor_get(x_317, 1);
lean_inc(x_346);
lean_dec(x_317);
x_347 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_346);
lean_dec(x_346);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
lean_dec(x_347);
x_349 = l_Array_append___rarg(x_17, x_348);
lean_dec(x_348);
x_350 = l_Lake_LeanOption_decodeToml___closed__4;
x_18 = x_350;
x_19 = x_349;
goto block_311;
}
else
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_347, 0);
lean_inc(x_351);
lean_dec(x_347);
x_18 = x_351;
x_19 = x_17;
goto block_311;
}
}
default: 
{
uint8_t x_352; 
x_352 = !lean_is_exclusive(x_317);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_353 = lean_ctor_get(x_317, 1);
lean_dec(x_353);
x_354 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_317, 0);
lean_ctor_set(x_317, 1, x_354);
x_355 = lean_unsigned_to_nat(1u);
x_356 = lean_mk_array(x_355, x_317);
x_357 = l_Array_append___rarg(x_17, x_356);
lean_dec(x_356);
x_358 = l_Lake_LeanOption_decodeToml___closed__4;
x_18 = x_358;
x_19 = x_357;
goto block_311;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_359 = lean_ctor_get(x_317, 0);
lean_inc(x_359);
lean_dec(x_317);
x_360 = l_Lake_LeanConfig_decodeToml___closed__5;
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_unsigned_to_nat(1u);
x_363 = lean_mk_array(x_362, x_361);
x_364 = l_Array_append___rarg(x_17, x_363);
lean_dec(x_363);
x_365 = l_Lake_LeanOption_decodeToml___closed__4;
x_18 = x_365;
x_19 = x_364;
goto block_311;
}
}
}
}
block_311:
{
lean_object* x_20; lean_object* x_21; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_258 = l_Lake_LeanConfig_decodeToml___closed__13;
lean_inc(x_1);
x_259 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_257, x_258, x_1);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; 
x_260 = l_Lake_LeanOption_decodeToml___closed__4;
x_20 = x_260;
x_21 = x_19;
goto block_256;
}
else
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec(x_261);
switch (lean_obj_tag(x_262)) {
case 0:
{
uint8_t x_263; 
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_264 = lean_ctor_get(x_262, 1);
lean_dec(x_264);
x_265 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_262, 1, x_265);
x_266 = lean_unsigned_to_nat(1u);
x_267 = lean_mk_array(x_266, x_262);
x_268 = l_Array_append___rarg(x_19, x_267);
lean_dec(x_267);
x_269 = l_Lake_LeanOption_decodeToml___closed__4;
x_20 = x_269;
x_21 = x_268;
goto block_256;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_270 = lean_ctor_get(x_262, 0);
lean_inc(x_270);
lean_dec(x_262);
x_271 = l_Lake_LeanConfig_decodeToml___closed__5;
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_mk_array(x_273, x_272);
x_275 = l_Array_append___rarg(x_19, x_274);
lean_dec(x_274);
x_276 = l_Lake_LeanOption_decodeToml___closed__4;
x_20 = x_276;
x_21 = x_275;
goto block_256;
}
}
case 2:
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_277 = lean_ctor_get(x_262, 0);
lean_inc(x_277);
lean_dec(x_262);
x_278 = l_Lake_LeanConfig_decodeToml___closed__5;
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_unsigned_to_nat(1u);
x_281 = lean_mk_array(x_280, x_279);
x_282 = l_Array_append___rarg(x_19, x_281);
lean_dec(x_281);
x_283 = l_Lake_LeanOption_decodeToml___closed__4;
x_20 = x_283;
x_21 = x_282;
goto block_256;
}
case 3:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_262, 0);
lean_inc(x_284);
lean_dec(x_262);
x_285 = l_Lake_LeanConfig_decodeToml___closed__5;
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_unsigned_to_nat(1u);
x_288 = lean_mk_array(x_287, x_286);
x_289 = l_Array_append___rarg(x_19, x_288);
lean_dec(x_288);
x_290 = l_Lake_LeanOption_decodeToml___closed__4;
x_20 = x_290;
x_21 = x_289;
goto block_256;
}
case 5:
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_262, 1);
lean_inc(x_291);
lean_dec(x_262);
x_292 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_291);
lean_dec(x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec(x_292);
x_294 = l_Array_append___rarg(x_19, x_293);
lean_dec(x_293);
x_295 = l_Lake_LeanOption_decodeToml___closed__4;
x_20 = x_295;
x_21 = x_294;
goto block_256;
}
else
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_292, 0);
lean_inc(x_296);
lean_dec(x_292);
x_20 = x_296;
x_21 = x_19;
goto block_256;
}
}
default: 
{
uint8_t x_297; 
x_297 = !lean_is_exclusive(x_262);
if (x_297 == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_298 = lean_ctor_get(x_262, 1);
lean_dec(x_298);
x_299 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_262, 0);
lean_ctor_set(x_262, 1, x_299);
x_300 = lean_unsigned_to_nat(1u);
x_301 = lean_mk_array(x_300, x_262);
x_302 = l_Array_append___rarg(x_19, x_301);
lean_dec(x_301);
x_303 = l_Lake_LeanOption_decodeToml___closed__4;
x_20 = x_303;
x_21 = x_302;
goto block_256;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_304 = lean_ctor_get(x_262, 0);
lean_inc(x_304);
lean_dec(x_262);
x_305 = l_Lake_LeanConfig_decodeToml___closed__5;
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_unsigned_to_nat(1u);
x_308 = lean_mk_array(x_307, x_306);
x_309 = l_Array_append___rarg(x_19, x_308);
lean_dec(x_308);
x_310 = l_Lake_LeanOption_decodeToml___closed__4;
x_20 = x_310;
x_21 = x_309;
goto block_256;
}
}
}
}
block_256:
{
lean_object* x_22; lean_object* x_23; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_203 = l_Lake_LeanConfig_decodeToml___closed__11;
lean_inc(x_1);
x_204 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_202, x_203, x_1);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = l_Lake_LeanOption_decodeToml___closed__4;
x_22 = x_205;
x_23 = x_21;
goto block_201;
}
else
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
switch (lean_obj_tag(x_207)) {
case 0:
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_207, 1);
lean_dec(x_209);
x_210 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_207, 1, x_210);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_mk_array(x_211, x_207);
x_213 = l_Array_append___rarg(x_21, x_212);
lean_dec(x_212);
x_214 = l_Lake_LeanOption_decodeToml___closed__4;
x_22 = x_214;
x_23 = x_213;
goto block_201;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_215 = lean_ctor_get(x_207, 0);
lean_inc(x_215);
lean_dec(x_207);
x_216 = l_Lake_LeanConfig_decodeToml___closed__5;
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_mk_array(x_218, x_217);
x_220 = l_Array_append___rarg(x_21, x_219);
lean_dec(x_219);
x_221 = l_Lake_LeanOption_decodeToml___closed__4;
x_22 = x_221;
x_23 = x_220;
goto block_201;
}
}
case 2:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_222 = lean_ctor_get(x_207, 0);
lean_inc(x_222);
lean_dec(x_207);
x_223 = l_Lake_LeanConfig_decodeToml___closed__5;
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_unsigned_to_nat(1u);
x_226 = lean_mk_array(x_225, x_224);
x_227 = l_Array_append___rarg(x_21, x_226);
lean_dec(x_226);
x_228 = l_Lake_LeanOption_decodeToml___closed__4;
x_22 = x_228;
x_23 = x_227;
goto block_201;
}
case 3:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_229 = lean_ctor_get(x_207, 0);
lean_inc(x_229);
lean_dec(x_207);
x_230 = l_Lake_LeanConfig_decodeToml___closed__5;
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_unsigned_to_nat(1u);
x_233 = lean_mk_array(x_232, x_231);
x_234 = l_Array_append___rarg(x_21, x_233);
lean_dec(x_233);
x_235 = l_Lake_LeanOption_decodeToml___closed__4;
x_22 = x_235;
x_23 = x_234;
goto block_201;
}
case 5:
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_207, 1);
lean_inc(x_236);
lean_dec(x_207);
x_237 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_236);
lean_dec(x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec(x_237);
x_239 = l_Array_append___rarg(x_21, x_238);
lean_dec(x_238);
x_240 = l_Lake_LeanOption_decodeToml___closed__4;
x_22 = x_240;
x_23 = x_239;
goto block_201;
}
else
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_237, 0);
lean_inc(x_241);
lean_dec(x_237);
x_22 = x_241;
x_23 = x_21;
goto block_201;
}
}
default: 
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_207);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_243 = lean_ctor_get(x_207, 1);
lean_dec(x_243);
x_244 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_207, 0);
lean_ctor_set(x_207, 1, x_244);
x_245 = lean_unsigned_to_nat(1u);
x_246 = lean_mk_array(x_245, x_207);
x_247 = l_Array_append___rarg(x_21, x_246);
lean_dec(x_246);
x_248 = l_Lake_LeanOption_decodeToml___closed__4;
x_22 = x_248;
x_23 = x_247;
goto block_201;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_249 = lean_ctor_get(x_207, 0);
lean_inc(x_249);
lean_dec(x_207);
x_250 = l_Lake_LeanConfig_decodeToml___closed__5;
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_mk_array(x_252, x_251);
x_254 = l_Array_append___rarg(x_21, x_253);
lean_dec(x_253);
x_255 = l_Lake_LeanOption_decodeToml___closed__4;
x_22 = x_255;
x_23 = x_254;
goto block_201;
}
}
}
}
block_201:
{
lean_object* x_24; lean_object* x_25; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_148 = l_Lake_LeanConfig_decodeToml___closed__9;
lean_inc(x_1);
x_149 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_147, x_148, x_1);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; 
x_150 = l_Lake_LeanOption_decodeToml___closed__4;
x_24 = x_150;
x_25 = x_23;
goto block_146;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_149, 0);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
switch (lean_obj_tag(x_152)) {
case 0:
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_152, 1);
lean_dec(x_154);
x_155 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_152, 1, x_155);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_mk_array(x_156, x_152);
x_158 = l_Array_append___rarg(x_23, x_157);
lean_dec(x_157);
x_159 = l_Lake_LeanOption_decodeToml___closed__4;
x_24 = x_159;
x_25 = x_158;
goto block_146;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_152, 0);
lean_inc(x_160);
lean_dec(x_152);
x_161 = l_Lake_LeanConfig_decodeToml___closed__5;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_mk_array(x_163, x_162);
x_165 = l_Array_append___rarg(x_23, x_164);
lean_dec(x_164);
x_166 = l_Lake_LeanOption_decodeToml___closed__4;
x_24 = x_166;
x_25 = x_165;
goto block_146;
}
}
case 2:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_152, 0);
lean_inc(x_167);
lean_dec(x_152);
x_168 = l_Lake_LeanConfig_decodeToml___closed__5;
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_mk_array(x_170, x_169);
x_172 = l_Array_append___rarg(x_23, x_171);
lean_dec(x_171);
x_173 = l_Lake_LeanOption_decodeToml___closed__4;
x_24 = x_173;
x_25 = x_172;
goto block_146;
}
case 3:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_152, 0);
lean_inc(x_174);
lean_dec(x_152);
x_175 = l_Lake_LeanConfig_decodeToml___closed__5;
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_mk_array(x_177, x_176);
x_179 = l_Array_append___rarg(x_23, x_178);
lean_dec(x_178);
x_180 = l_Lake_LeanOption_decodeToml___closed__4;
x_24 = x_180;
x_25 = x_179;
goto block_146;
}
case 5:
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_152, 1);
lean_inc(x_181);
lean_dec(x_152);
x_182 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_181);
lean_dec(x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Array_append___rarg(x_23, x_183);
lean_dec(x_183);
x_185 = l_Lake_LeanOption_decodeToml___closed__4;
x_24 = x_185;
x_25 = x_184;
goto block_146;
}
else
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_182, 0);
lean_inc(x_186);
lean_dec(x_182);
x_24 = x_186;
x_25 = x_23;
goto block_146;
}
}
default: 
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_152);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_152, 1);
lean_dec(x_188);
x_189 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_152, 0);
lean_ctor_set(x_152, 1, x_189);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_mk_array(x_190, x_152);
x_192 = l_Array_append___rarg(x_23, x_191);
lean_dec(x_191);
x_193 = l_Lake_LeanOption_decodeToml___closed__4;
x_24 = x_193;
x_25 = x_192;
goto block_146;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_152, 0);
lean_inc(x_194);
lean_dec(x_152);
x_195 = l_Lake_LeanConfig_decodeToml___closed__5;
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_mk_array(x_197, x_196);
x_199 = l_Array_append___rarg(x_23, x_198);
lean_dec(x_198);
x_200 = l_Lake_LeanOption_decodeToml___closed__4;
x_24 = x_200;
x_25 = x_199;
goto block_146;
}
}
}
}
block_146:
{
lean_object* x_26; lean_object* x_27; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_93 = l_Lake_LeanConfig_decodeToml___closed__7;
lean_inc(x_1);
x_94 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_92, x_93, x_1);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = l_Lake_LeanOption_decodeToml___closed__4;
x_26 = x_95;
x_27 = x_25;
goto block_91;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
switch (lean_obj_tag(x_97)) {
case 0:
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_97, 1);
lean_dec(x_99);
x_100 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_97, 1, x_100);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_mk_array(x_101, x_97);
x_103 = l_Array_append___rarg(x_25, x_102);
lean_dec(x_102);
x_104 = l_Lake_LeanOption_decodeToml___closed__4;
x_26 = x_104;
x_27 = x_103;
goto block_91;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_97, 0);
lean_inc(x_105);
lean_dec(x_97);
x_106 = l_Lake_LeanConfig_decodeToml___closed__5;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_mk_array(x_108, x_107);
x_110 = l_Array_append___rarg(x_25, x_109);
lean_dec(x_109);
x_111 = l_Lake_LeanOption_decodeToml___closed__4;
x_26 = x_111;
x_27 = x_110;
goto block_91;
}
}
case 2:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_112 = lean_ctor_get(x_97, 0);
lean_inc(x_112);
lean_dec(x_97);
x_113 = l_Lake_LeanConfig_decodeToml___closed__5;
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_mk_array(x_115, x_114);
x_117 = l_Array_append___rarg(x_25, x_116);
lean_dec(x_116);
x_118 = l_Lake_LeanOption_decodeToml___closed__4;
x_26 = x_118;
x_27 = x_117;
goto block_91;
}
case 3:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_119 = lean_ctor_get(x_97, 0);
lean_inc(x_119);
lean_dec(x_97);
x_120 = l_Lake_LeanConfig_decodeToml___closed__5;
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_mk_array(x_122, x_121);
x_124 = l_Array_append___rarg(x_25, x_123);
lean_dec(x_123);
x_125 = l_Lake_LeanOption_decodeToml___closed__4;
x_26 = x_125;
x_27 = x_124;
goto block_91;
}
case 5:
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_97, 1);
lean_inc(x_126);
lean_dec(x_97);
x_127 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_126);
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l_Array_append___rarg(x_25, x_128);
lean_dec(x_128);
x_130 = l_Lake_LeanOption_decodeToml___closed__4;
x_26 = x_130;
x_27 = x_129;
goto block_91;
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
lean_dec(x_127);
x_26 = x_131;
x_27 = x_25;
goto block_91;
}
}
default: 
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_97);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_97, 1);
lean_dec(x_133);
x_134 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_97, 0);
lean_ctor_set(x_97, 1, x_134);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_mk_array(x_135, x_97);
x_137 = l_Array_append___rarg(x_25, x_136);
lean_dec(x_136);
x_138 = l_Lake_LeanOption_decodeToml___closed__4;
x_26 = x_138;
x_27 = x_137;
goto block_91;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_139 = lean_ctor_get(x_97, 0);
lean_inc(x_139);
lean_dec(x_97);
x_140 = l_Lake_LeanConfig_decodeToml___closed__5;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_mk_array(x_142, x_141);
x_144 = l_Array_append___rarg(x_25, x_143);
lean_dec(x_143);
x_145 = l_Lake_LeanOption_decodeToml___closed__4;
x_26 = x_145;
x_27 = x_144;
goto block_91;
}
}
}
}
block_91:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_29 = l_Lake_LeanConfig_decodeToml___closed__4;
x_30 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_28, x_29, x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Lake_LeanOption_decodeToml___closed__4;
x_32 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_18);
lean_ctor_set(x_32, 2, x_20);
lean_ctor_set(x_32, 3, x_22);
lean_ctor_set(x_32, 4, x_16);
lean_ctor_set(x_32, 5, x_24);
lean_ctor_set(x_32, 6, x_26);
lean_ctor_set(x_32, 7, x_31);
lean_ctor_set(x_32, 8, x_12);
lean_ctor_set_uint8(x_32, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_32, sizeof(void*)*9 + 1, x_10);
x_2 = x_32;
x_3 = x_27;
goto block_7;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
switch (lean_obj_tag(x_34)) {
case 0:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_34, 1);
lean_dec(x_36);
x_37 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_34, 1, x_37);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_array(x_38, x_34);
x_40 = l_Array_append___rarg(x_27, x_39);
lean_dec(x_39);
x_41 = l_Lake_LeanOption_decodeToml___closed__4;
x_42 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_42, 0, x_14);
lean_ctor_set(x_42, 1, x_18);
lean_ctor_set(x_42, 2, x_20);
lean_ctor_set(x_42, 3, x_22);
lean_ctor_set(x_42, 4, x_16);
lean_ctor_set(x_42, 5, x_24);
lean_ctor_set(x_42, 6, x_26);
lean_ctor_set(x_42, 7, x_41);
lean_ctor_set(x_42, 8, x_12);
lean_ctor_set_uint8(x_42, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_42, sizeof(void*)*9 + 1, x_10);
x_2 = x_42;
x_3 = x_40;
goto block_7;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_34, 0);
lean_inc(x_43);
lean_dec(x_34);
x_44 = l_Lake_LeanConfig_decodeToml___closed__5;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_mk_array(x_46, x_45);
x_48 = l_Array_append___rarg(x_27, x_47);
lean_dec(x_47);
x_49 = l_Lake_LeanOption_decodeToml___closed__4;
x_50 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_50, 0, x_14);
lean_ctor_set(x_50, 1, x_18);
lean_ctor_set(x_50, 2, x_20);
lean_ctor_set(x_50, 3, x_22);
lean_ctor_set(x_50, 4, x_16);
lean_ctor_set(x_50, 5, x_24);
lean_ctor_set(x_50, 6, x_26);
lean_ctor_set(x_50, 7, x_49);
lean_ctor_set(x_50, 8, x_12);
lean_ctor_set_uint8(x_50, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_50, sizeof(void*)*9 + 1, x_10);
x_2 = x_50;
x_3 = x_48;
goto block_7;
}
}
case 2:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_34, 0);
lean_inc(x_51);
lean_dec(x_34);
x_52 = l_Lake_LeanConfig_decodeToml___closed__5;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_mk_array(x_54, x_53);
x_56 = l_Array_append___rarg(x_27, x_55);
lean_dec(x_55);
x_57 = l_Lake_LeanOption_decodeToml___closed__4;
x_58 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_58, 0, x_14);
lean_ctor_set(x_58, 1, x_18);
lean_ctor_set(x_58, 2, x_20);
lean_ctor_set(x_58, 3, x_22);
lean_ctor_set(x_58, 4, x_16);
lean_ctor_set(x_58, 5, x_24);
lean_ctor_set(x_58, 6, x_26);
lean_ctor_set(x_58, 7, x_57);
lean_ctor_set(x_58, 8, x_12);
lean_ctor_set_uint8(x_58, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_58, sizeof(void*)*9 + 1, x_10);
x_2 = x_58;
x_3 = x_56;
goto block_7;
}
case 3:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_34, 0);
lean_inc(x_59);
lean_dec(x_34);
x_60 = l_Lake_LeanConfig_decodeToml___closed__5;
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_mk_array(x_62, x_61);
x_64 = l_Array_append___rarg(x_27, x_63);
lean_dec(x_63);
x_65 = l_Lake_LeanOption_decodeToml___closed__4;
x_66 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_66, 0, x_14);
lean_ctor_set(x_66, 1, x_18);
lean_ctor_set(x_66, 2, x_20);
lean_ctor_set(x_66, 3, x_22);
lean_ctor_set(x_66, 4, x_16);
lean_ctor_set(x_66, 5, x_24);
lean_ctor_set(x_66, 6, x_26);
lean_ctor_set(x_66, 7, x_65);
lean_ctor_set(x_66, 8, x_12);
lean_ctor_set_uint8(x_66, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_66, sizeof(void*)*9 + 1, x_10);
x_2 = x_66;
x_3 = x_64;
goto block_7;
}
case 5:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_34, 1);
lean_inc(x_67);
lean_dec(x_34);
x_68 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_67);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Array_append___rarg(x_27, x_69);
lean_dec(x_69);
x_71 = l_Lake_LeanOption_decodeToml___closed__4;
x_72 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_72, 0, x_14);
lean_ctor_set(x_72, 1, x_18);
lean_ctor_set(x_72, 2, x_20);
lean_ctor_set(x_72, 3, x_22);
lean_ctor_set(x_72, 4, x_16);
lean_ctor_set(x_72, 5, x_24);
lean_ctor_set(x_72, 6, x_26);
lean_ctor_set(x_72, 7, x_71);
lean_ctor_set(x_72, 8, x_12);
lean_ctor_set_uint8(x_72, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_72, sizeof(void*)*9 + 1, x_10);
x_2 = x_72;
x_3 = x_70;
goto block_7;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_74, 0, x_14);
lean_ctor_set(x_74, 1, x_18);
lean_ctor_set(x_74, 2, x_20);
lean_ctor_set(x_74, 3, x_22);
lean_ctor_set(x_74, 4, x_16);
lean_ctor_set(x_74, 5, x_24);
lean_ctor_set(x_74, 6, x_26);
lean_ctor_set(x_74, 7, x_73);
lean_ctor_set(x_74, 8, x_12);
lean_ctor_set_uint8(x_74, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_74, sizeof(void*)*9 + 1, x_10);
x_2 = x_74;
x_3 = x_27;
goto block_7;
}
}
default: 
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_34);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_76 = lean_ctor_get(x_34, 1);
lean_dec(x_76);
x_77 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_34, 0);
lean_ctor_set(x_34, 1, x_77);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_mk_array(x_78, x_34);
x_80 = l_Array_append___rarg(x_27, x_79);
lean_dec(x_79);
x_81 = l_Lake_LeanOption_decodeToml___closed__4;
x_82 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_82, 0, x_14);
lean_ctor_set(x_82, 1, x_18);
lean_ctor_set(x_82, 2, x_20);
lean_ctor_set(x_82, 3, x_22);
lean_ctor_set(x_82, 4, x_16);
lean_ctor_set(x_82, 5, x_24);
lean_ctor_set(x_82, 6, x_26);
lean_ctor_set(x_82, 7, x_81);
lean_ctor_set(x_82, 8, x_12);
lean_ctor_set_uint8(x_82, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_82, sizeof(void*)*9 + 1, x_10);
x_2 = x_82;
x_3 = x_80;
goto block_7;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_ctor_get(x_34, 0);
lean_inc(x_83);
lean_dec(x_34);
x_84 = l_Lake_LeanConfig_decodeToml___closed__5;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_mk_array(x_86, x_85);
x_88 = l_Array_append___rarg(x_27, x_87);
lean_dec(x_87);
x_89 = l_Lake_LeanOption_decodeToml___closed__4;
x_90 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_90, 0, x_14);
lean_ctor_set(x_90, 1, x_18);
lean_ctor_set(x_90, 2, x_20);
lean_ctor_set(x_90, 3, x_22);
lean_ctor_set(x_90, 4, x_16);
lean_ctor_set(x_90, 5, x_24);
lean_ctor_set(x_90, 6, x_26);
lean_ctor_set(x_90, 7, x_89);
lean_ctor_set(x_90, 8, x_12);
lean_ctor_set_uint8(x_90, sizeof(void*)*9, x_8);
lean_ctor_set_uint8(x_90, sizeof(void*)*9 + 1, x_10);
x_2 = x_90;
x_3 = x_88;
goto block_7;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanConfig_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_LeanConfig_decodeToml___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanConfig(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 6:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lake_LeanConfig_decodeToml(x_26);
return x_27;
}
default: 
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_1, 1);
lean_dec(x_29);
x_30 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_mk_array(x_31, x_1);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_mk_array(x_37, x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_PackageConfig_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lake_Toml_ppKey(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_10);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_16);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = l_Lake_Toml_ppKey(x_1);
x_24 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_22);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_8, x_3, x_29);
x_3 = x_31;
x_4 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_11; lean_object* x_12; 
x_11 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
lean_inc(x_2);
x_12 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_11, x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = l_Lake_Toml_ppKey(x_2);
lean_dec(x_2);
x_14 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_mk_array(x_19, x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_12);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lake_Glob_decodeToml___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_mk_array(x_29, x_28);
x_4 = x_30;
goto block_10;
}
case 3:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_12);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec(x_24);
x_32 = l_Lake_Glob_decodeToml___closed__2;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_mk_array(x_34, x_33);
x_4 = x_35;
goto block_10;
}
default: 
{
uint8_t x_36; 
lean_free_object(x_12);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_24, 1);
lean_dec(x_37);
x_38 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 1, x_38);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_mk_array(x_39, x_24);
x_4 = x_40;
goto block_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_24, 0);
lean_inc(x_41);
lean_dec(x_24);
x_42 = l_Lake_Glob_decodeToml___closed__2;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_mk_array(x_44, x_43);
x_4 = x_45;
goto block_10;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
lean_dec(x_12);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
switch (lean_obj_tag(x_47)) {
case 0:
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
case 2:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lake_Glob_decodeToml___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_mk_array(x_53, x_52);
x_4 = x_54;
goto block_10;
}
case 3:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = l_Lake_Glob_decodeToml___closed__2;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_mk_array(x_58, x_57);
x_4 = x_59;
goto block_10;
}
default: 
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_47, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_61 = x_47;
} else {
 lean_dec_ref(x_47);
 x_61 = lean_box(0);
}
x_62 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
 lean_ctor_set_tag(x_63, 0);
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_mk_array(x_64, x_63);
x_4 = x_65;
goto block_10;
}
}
}
}
block_10:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_Lake_PackageConfig_decodeToml___spec__2(x_2, x_6, x_7, x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("moreGlobalServerArgs", 20, 20);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("testDriverArgs", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".tar.gz", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = l_Lake_LeanOption_decodeToml___closed__4;
x_4 = 2;
x_5 = lean_alloc_ctor(0, 9, 2);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_3);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*9, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*9 + 1, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lintDriverArgs", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lintDriver", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static uint8_t _init_l_Lake_PackageConfig_decodeToml___closed__12() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_PackageConfig_decodeToml___closed__13() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("testDriver", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("testRunner", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("preferReleaseBuild", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("buildArchive", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__20;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("releaseRepo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__22;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("irDir", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__24;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__26;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nativeLibDir", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__28;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanLibDir", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__30;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("buildDir", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__32;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("srcDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__34;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precompileModules", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__37;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_782; lean_object* x_783; 
x_782 = l_Lake_LeanOption_decodeToml___closed__11;
lean_inc(x_1);
x_783 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__1(x_1, x_782, x_2);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
x_784 = lean_ctor_get(x_783, 0);
lean_inc(x_784);
lean_dec(x_783);
x_785 = l_Lake_LeanOption_decodeToml___closed__4;
x_786 = l_Array_append___rarg(x_785, x_784);
lean_dec(x_784);
x_787 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_787;
x_10 = x_786;
goto block_781;
}
else
{
lean_object* x_788; lean_object* x_789; 
x_788 = lean_ctor_get(x_783, 0);
lean_inc(x_788);
lean_dec(x_783);
x_789 = l_Lake_LeanOption_decodeToml___closed__4;
x_9 = x_788;
x_10 = x_789;
goto block_781;
}
block_8:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
}
block_781:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
x_11 = l_Lake_stringToLegalOrSimpleName(x_9);
x_739 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_740 = l_Lake_PackageConfig_decodeToml___closed__38;
lean_inc(x_1);
x_741 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_739, x_740, x_1);
if (lean_obj_tag(x_741) == 0)
{
uint8_t x_742; 
x_742 = 0;
x_12 = x_742;
x_13 = x_10;
goto block_738;
}
else
{
lean_object* x_743; lean_object* x_744; 
x_743 = lean_ctor_get(x_741, 0);
lean_inc(x_743);
lean_dec(x_741);
x_744 = lean_ctor_get(x_743, 1);
lean_inc(x_744);
lean_dec(x_743);
switch (lean_obj_tag(x_744)) {
case 0:
{
uint8_t x_745; 
x_745 = !lean_is_exclusive(x_744);
if (x_745 == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; 
x_746 = lean_ctor_get(x_744, 1);
lean_dec(x_746);
x_747 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_744, 1, x_747);
x_748 = lean_unsigned_to_nat(1u);
x_749 = lean_mk_array(x_748, x_744);
x_750 = l_Array_append___rarg(x_10, x_749);
lean_dec(x_749);
x_751 = 0;
x_12 = x_751;
x_13 = x_750;
goto block_738;
}
else
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; uint8_t x_758; 
x_752 = lean_ctor_get(x_744, 0);
lean_inc(x_752);
lean_dec(x_744);
x_753 = l_Lake_LeanConfig_decodeToml___closed__20;
x_754 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_754, 0, x_752);
lean_ctor_set(x_754, 1, x_753);
x_755 = lean_unsigned_to_nat(1u);
x_756 = lean_mk_array(x_755, x_754);
x_757 = l_Array_append___rarg(x_10, x_756);
lean_dec(x_756);
x_758 = 0;
x_12 = x_758;
x_13 = x_757;
goto block_738;
}
}
case 2:
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; uint8_t x_765; 
x_759 = lean_ctor_get(x_744, 0);
lean_inc(x_759);
lean_dec(x_744);
x_760 = l_Lake_LeanConfig_decodeToml___closed__20;
x_761 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_761, 0, x_759);
lean_ctor_set(x_761, 1, x_760);
x_762 = lean_unsigned_to_nat(1u);
x_763 = lean_mk_array(x_762, x_761);
x_764 = l_Array_append___rarg(x_10, x_763);
lean_dec(x_763);
x_765 = 0;
x_12 = x_765;
x_13 = x_764;
goto block_738;
}
case 3:
{
uint8_t x_766; 
x_766 = lean_ctor_get_uint8(x_744, sizeof(void*)*1);
lean_dec(x_744);
x_12 = x_766;
x_13 = x_10;
goto block_738;
}
default: 
{
uint8_t x_767; 
x_767 = !lean_is_exclusive(x_744);
if (x_767 == 0)
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; uint8_t x_773; 
x_768 = lean_ctor_get(x_744, 1);
lean_dec(x_768);
x_769 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_744, 0);
lean_ctor_set(x_744, 1, x_769);
x_770 = lean_unsigned_to_nat(1u);
x_771 = lean_mk_array(x_770, x_744);
x_772 = l_Array_append___rarg(x_10, x_771);
lean_dec(x_771);
x_773 = 0;
x_12 = x_773;
x_13 = x_772;
goto block_738;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; uint8_t x_780; 
x_774 = lean_ctor_get(x_744, 0);
lean_inc(x_774);
lean_dec(x_744);
x_775 = l_Lake_LeanConfig_decodeToml___closed__20;
x_776 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_776, 0, x_774);
lean_ctor_set(x_776, 1, x_775);
x_777 = lean_unsigned_to_nat(1u);
x_778 = lean_mk_array(x_777, x_776);
x_779 = l_Array_append___rarg(x_10, x_778);
lean_dec(x_778);
x_780 = 0;
x_12 = x_780;
x_13 = x_779;
goto block_738;
}
}
}
}
block_738:
{
lean_object* x_14; lean_object* x_15; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_684 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_685 = l_Lake_PackageConfig_decodeToml___closed__2;
lean_inc(x_1);
x_686 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_684, x_685, x_1);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; 
x_687 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_687;
x_15 = x_13;
goto block_683;
}
else
{
lean_object* x_688; lean_object* x_689; 
x_688 = lean_ctor_get(x_686, 0);
lean_inc(x_688);
lean_dec(x_686);
x_689 = lean_ctor_get(x_688, 1);
lean_inc(x_689);
lean_dec(x_688);
switch (lean_obj_tag(x_689)) {
case 0:
{
uint8_t x_690; 
x_690 = !lean_is_exclusive(x_689);
if (x_690 == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_691 = lean_ctor_get(x_689, 1);
lean_dec(x_691);
x_692 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_689, 1, x_692);
x_693 = lean_unsigned_to_nat(1u);
x_694 = lean_mk_array(x_693, x_689);
x_695 = l_Array_append___rarg(x_13, x_694);
lean_dec(x_694);
x_696 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_696;
x_15 = x_695;
goto block_683;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_697 = lean_ctor_get(x_689, 0);
lean_inc(x_697);
lean_dec(x_689);
x_698 = l_Lake_LeanConfig_decodeToml___closed__5;
x_699 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
x_700 = lean_unsigned_to_nat(1u);
x_701 = lean_mk_array(x_700, x_699);
x_702 = l_Array_append___rarg(x_13, x_701);
lean_dec(x_701);
x_703 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_703;
x_15 = x_702;
goto block_683;
}
}
case 2:
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_704 = lean_ctor_get(x_689, 0);
lean_inc(x_704);
lean_dec(x_689);
x_705 = l_Lake_LeanConfig_decodeToml___closed__5;
x_706 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
x_707 = lean_unsigned_to_nat(1u);
x_708 = lean_mk_array(x_707, x_706);
x_709 = l_Array_append___rarg(x_13, x_708);
lean_dec(x_708);
x_710 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_710;
x_15 = x_709;
goto block_683;
}
case 3:
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_711 = lean_ctor_get(x_689, 0);
lean_inc(x_711);
lean_dec(x_689);
x_712 = l_Lake_LeanConfig_decodeToml___closed__5;
x_713 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_713, 0, x_711);
lean_ctor_set(x_713, 1, x_712);
x_714 = lean_unsigned_to_nat(1u);
x_715 = lean_mk_array(x_714, x_713);
x_716 = l_Array_append___rarg(x_13, x_715);
lean_dec(x_715);
x_717 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_717;
x_15 = x_716;
goto block_683;
}
case 5:
{
lean_object* x_718; lean_object* x_719; 
x_718 = lean_ctor_get(x_689, 1);
lean_inc(x_718);
lean_dec(x_689);
x_719 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_718);
lean_dec(x_718);
if (lean_obj_tag(x_719) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; 
x_720 = lean_ctor_get(x_719, 0);
lean_inc(x_720);
lean_dec(x_719);
x_721 = l_Array_append___rarg(x_13, x_720);
lean_dec(x_720);
x_722 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_722;
x_15 = x_721;
goto block_683;
}
else
{
lean_object* x_723; 
x_723 = lean_ctor_get(x_719, 0);
lean_inc(x_723);
lean_dec(x_719);
x_14 = x_723;
x_15 = x_13;
goto block_683;
}
}
default: 
{
uint8_t x_724; 
x_724 = !lean_is_exclusive(x_689);
if (x_724 == 0)
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_725 = lean_ctor_get(x_689, 1);
lean_dec(x_725);
x_726 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_689, 0);
lean_ctor_set(x_689, 1, x_726);
x_727 = lean_unsigned_to_nat(1u);
x_728 = lean_mk_array(x_727, x_689);
x_729 = l_Array_append___rarg(x_13, x_728);
lean_dec(x_728);
x_730 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_730;
x_15 = x_729;
goto block_683;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_731 = lean_ctor_get(x_689, 0);
lean_inc(x_731);
lean_dec(x_689);
x_732 = l_Lake_LeanConfig_decodeToml___closed__5;
x_733 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_733, 0, x_731);
lean_ctor_set(x_733, 1, x_732);
x_734 = lean_unsigned_to_nat(1u);
x_735 = lean_mk_array(x_734, x_733);
x_736 = l_Array_append___rarg(x_13, x_735);
lean_dec(x_735);
x_737 = l_Lake_LeanOption_decodeToml___closed__4;
x_14 = x_737;
x_15 = x_736;
goto block_683;
}
}
}
}
block_683:
{
lean_object* x_16; lean_object* x_17; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_649 = l_Lake_PackageConfig_decodeToml___closed__35;
lean_inc(x_1);
x_650 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_648, x_649, x_1);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; 
x_651 = l_Lake_PackageConfig_decodeToml___closed__36;
x_16 = x_651;
x_17 = x_15;
goto block_647;
}
else
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_ctor_get(x_650, 0);
lean_inc(x_652);
lean_dec(x_650);
x_653 = lean_ctor_get(x_652, 1);
lean_inc(x_653);
lean_dec(x_652);
switch (lean_obj_tag(x_653)) {
case 0:
{
lean_object* x_654; 
x_654 = lean_ctor_get(x_653, 1);
lean_inc(x_654);
lean_dec(x_653);
x_16 = x_654;
x_17 = x_15;
goto block_647;
}
case 2:
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_655 = lean_ctor_get(x_653, 0);
lean_inc(x_655);
lean_dec(x_653);
x_656 = l_Lake_Glob_decodeToml___closed__2;
x_657 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_656);
x_658 = lean_unsigned_to_nat(1u);
x_659 = lean_mk_array(x_658, x_657);
x_660 = l_Array_append___rarg(x_15, x_659);
lean_dec(x_659);
x_661 = l_Lake_PackageConfig_decodeToml___closed__36;
x_16 = x_661;
x_17 = x_660;
goto block_647;
}
case 3:
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_662 = lean_ctor_get(x_653, 0);
lean_inc(x_662);
lean_dec(x_653);
x_663 = l_Lake_Glob_decodeToml___closed__2;
x_664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_664, 0, x_662);
lean_ctor_set(x_664, 1, x_663);
x_665 = lean_unsigned_to_nat(1u);
x_666 = lean_mk_array(x_665, x_664);
x_667 = l_Array_append___rarg(x_15, x_666);
lean_dec(x_666);
x_668 = l_Lake_PackageConfig_decodeToml___closed__36;
x_16 = x_668;
x_17 = x_667;
goto block_647;
}
default: 
{
uint8_t x_669; 
x_669 = !lean_is_exclusive(x_653);
if (x_669 == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_670 = lean_ctor_get(x_653, 1);
lean_dec(x_670);
x_671 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_653, 0);
lean_ctor_set(x_653, 1, x_671);
x_672 = lean_unsigned_to_nat(1u);
x_673 = lean_mk_array(x_672, x_653);
x_674 = l_Array_append___rarg(x_15, x_673);
lean_dec(x_673);
x_675 = l_Lake_PackageConfig_decodeToml___closed__36;
x_16 = x_675;
x_17 = x_674;
goto block_647;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
x_676 = lean_ctor_get(x_653, 0);
lean_inc(x_676);
lean_dec(x_653);
x_677 = l_Lake_Glob_decodeToml___closed__2;
x_678 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
x_679 = lean_unsigned_to_nat(1u);
x_680 = lean_mk_array(x_679, x_678);
x_681 = l_Array_append___rarg(x_15, x_680);
lean_dec(x_680);
x_682 = l_Lake_PackageConfig_decodeToml___closed__36;
x_16 = x_682;
x_17 = x_681;
goto block_647;
}
}
}
}
block_647:
{
lean_object* x_18; lean_object* x_19; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_612 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_613 = l_Lake_PackageConfig_decodeToml___closed__33;
lean_inc(x_1);
x_614 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_612, x_613, x_1);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; 
x_615 = l_Lake_defaultBuildDir;
x_18 = x_615;
x_19 = x_17;
goto block_611;
}
else
{
lean_object* x_616; lean_object* x_617; 
x_616 = lean_ctor_get(x_614, 0);
lean_inc(x_616);
lean_dec(x_614);
x_617 = lean_ctor_get(x_616, 1);
lean_inc(x_617);
lean_dec(x_616);
switch (lean_obj_tag(x_617)) {
case 0:
{
lean_object* x_618; 
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
lean_dec(x_617);
x_18 = x_618;
x_19 = x_17;
goto block_611;
}
case 2:
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_619 = lean_ctor_get(x_617, 0);
lean_inc(x_619);
lean_dec(x_617);
x_620 = l_Lake_Glob_decodeToml___closed__2;
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set(x_621, 1, x_620);
x_622 = lean_unsigned_to_nat(1u);
x_623 = lean_mk_array(x_622, x_621);
x_624 = l_Array_append___rarg(x_17, x_623);
lean_dec(x_623);
x_625 = l_Lake_defaultBuildDir;
x_18 = x_625;
x_19 = x_624;
goto block_611;
}
case 3:
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_626 = lean_ctor_get(x_617, 0);
lean_inc(x_626);
lean_dec(x_617);
x_627 = l_Lake_Glob_decodeToml___closed__2;
x_628 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
x_629 = lean_unsigned_to_nat(1u);
x_630 = lean_mk_array(x_629, x_628);
x_631 = l_Array_append___rarg(x_17, x_630);
lean_dec(x_630);
x_632 = l_Lake_defaultBuildDir;
x_18 = x_632;
x_19 = x_631;
goto block_611;
}
default: 
{
uint8_t x_633; 
x_633 = !lean_is_exclusive(x_617);
if (x_633 == 0)
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_634 = lean_ctor_get(x_617, 1);
lean_dec(x_634);
x_635 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_617, 0);
lean_ctor_set(x_617, 1, x_635);
x_636 = lean_unsigned_to_nat(1u);
x_637 = lean_mk_array(x_636, x_617);
x_638 = l_Array_append___rarg(x_17, x_637);
lean_dec(x_637);
x_639 = l_Lake_defaultBuildDir;
x_18 = x_639;
x_19 = x_638;
goto block_611;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_640 = lean_ctor_get(x_617, 0);
lean_inc(x_640);
lean_dec(x_617);
x_641 = l_Lake_Glob_decodeToml___closed__2;
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
x_643 = lean_unsigned_to_nat(1u);
x_644 = lean_mk_array(x_643, x_642);
x_645 = l_Array_append___rarg(x_17, x_644);
lean_dec(x_644);
x_646 = l_Lake_defaultBuildDir;
x_18 = x_646;
x_19 = x_645;
goto block_611;
}
}
}
}
block_611:
{
lean_object* x_20; lean_object* x_21; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_577 = l_Lake_PackageConfig_decodeToml___closed__31;
lean_inc(x_1);
x_578 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_576, x_577, x_1);
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_579; 
x_579 = l_Lake_defaultLeanLibDir;
x_20 = x_579;
x_21 = x_19;
goto block_575;
}
else
{
lean_object* x_580; lean_object* x_581; 
x_580 = lean_ctor_get(x_578, 0);
lean_inc(x_580);
lean_dec(x_578);
x_581 = lean_ctor_get(x_580, 1);
lean_inc(x_581);
lean_dec(x_580);
switch (lean_obj_tag(x_581)) {
case 0:
{
lean_object* x_582; 
x_582 = lean_ctor_get(x_581, 1);
lean_inc(x_582);
lean_dec(x_581);
x_20 = x_582;
x_21 = x_19;
goto block_575;
}
case 2:
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_583 = lean_ctor_get(x_581, 0);
lean_inc(x_583);
lean_dec(x_581);
x_584 = l_Lake_Glob_decodeToml___closed__2;
x_585 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
x_586 = lean_unsigned_to_nat(1u);
x_587 = lean_mk_array(x_586, x_585);
x_588 = l_Array_append___rarg(x_19, x_587);
lean_dec(x_587);
x_589 = l_Lake_defaultLeanLibDir;
x_20 = x_589;
x_21 = x_588;
goto block_575;
}
case 3:
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_590 = lean_ctor_get(x_581, 0);
lean_inc(x_590);
lean_dec(x_581);
x_591 = l_Lake_Glob_decodeToml___closed__2;
x_592 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
x_593 = lean_unsigned_to_nat(1u);
x_594 = lean_mk_array(x_593, x_592);
x_595 = l_Array_append___rarg(x_19, x_594);
lean_dec(x_594);
x_596 = l_Lake_defaultLeanLibDir;
x_20 = x_596;
x_21 = x_595;
goto block_575;
}
default: 
{
uint8_t x_597; 
x_597 = !lean_is_exclusive(x_581);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_598 = lean_ctor_get(x_581, 1);
lean_dec(x_598);
x_599 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_581, 0);
lean_ctor_set(x_581, 1, x_599);
x_600 = lean_unsigned_to_nat(1u);
x_601 = lean_mk_array(x_600, x_581);
x_602 = l_Array_append___rarg(x_19, x_601);
lean_dec(x_601);
x_603 = l_Lake_defaultLeanLibDir;
x_20 = x_603;
x_21 = x_602;
goto block_575;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_604 = lean_ctor_get(x_581, 0);
lean_inc(x_604);
lean_dec(x_581);
x_605 = l_Lake_Glob_decodeToml___closed__2;
x_606 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_606, 0, x_604);
lean_ctor_set(x_606, 1, x_605);
x_607 = lean_unsigned_to_nat(1u);
x_608 = lean_mk_array(x_607, x_606);
x_609 = l_Array_append___rarg(x_19, x_608);
lean_dec(x_608);
x_610 = l_Lake_defaultLeanLibDir;
x_20 = x_610;
x_21 = x_609;
goto block_575;
}
}
}
}
block_575:
{
lean_object* x_22; lean_object* x_23; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_540 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_541 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_542 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_540, x_541, x_1);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; 
x_543 = l_Lake_defaultNativeLibDir;
x_22 = x_543;
x_23 = x_21;
goto block_539;
}
else
{
lean_object* x_544; lean_object* x_545; 
x_544 = lean_ctor_get(x_542, 0);
lean_inc(x_544);
lean_dec(x_542);
x_545 = lean_ctor_get(x_544, 1);
lean_inc(x_545);
lean_dec(x_544);
switch (lean_obj_tag(x_545)) {
case 0:
{
lean_object* x_546; 
x_546 = lean_ctor_get(x_545, 1);
lean_inc(x_546);
lean_dec(x_545);
x_22 = x_546;
x_23 = x_21;
goto block_539;
}
case 2:
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_547 = lean_ctor_get(x_545, 0);
lean_inc(x_547);
lean_dec(x_545);
x_548 = l_Lake_Glob_decodeToml___closed__2;
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_548);
x_550 = lean_unsigned_to_nat(1u);
x_551 = lean_mk_array(x_550, x_549);
x_552 = l_Array_append___rarg(x_21, x_551);
lean_dec(x_551);
x_553 = l_Lake_defaultNativeLibDir;
x_22 = x_553;
x_23 = x_552;
goto block_539;
}
case 3:
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_554 = lean_ctor_get(x_545, 0);
lean_inc(x_554);
lean_dec(x_545);
x_555 = l_Lake_Glob_decodeToml___closed__2;
x_556 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_556, 0, x_554);
lean_ctor_set(x_556, 1, x_555);
x_557 = lean_unsigned_to_nat(1u);
x_558 = lean_mk_array(x_557, x_556);
x_559 = l_Array_append___rarg(x_21, x_558);
lean_dec(x_558);
x_560 = l_Lake_defaultNativeLibDir;
x_22 = x_560;
x_23 = x_559;
goto block_539;
}
default: 
{
uint8_t x_561; 
x_561 = !lean_is_exclusive(x_545);
if (x_561 == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_562 = lean_ctor_get(x_545, 1);
lean_dec(x_562);
x_563 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_545, 0);
lean_ctor_set(x_545, 1, x_563);
x_564 = lean_unsigned_to_nat(1u);
x_565 = lean_mk_array(x_564, x_545);
x_566 = l_Array_append___rarg(x_21, x_565);
lean_dec(x_565);
x_567 = l_Lake_defaultNativeLibDir;
x_22 = x_567;
x_23 = x_566;
goto block_539;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_568 = lean_ctor_get(x_545, 0);
lean_inc(x_568);
lean_dec(x_545);
x_569 = l_Lake_Glob_decodeToml___closed__2;
x_570 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
x_571 = lean_unsigned_to_nat(1u);
x_572 = lean_mk_array(x_571, x_570);
x_573 = l_Array_append___rarg(x_21, x_572);
lean_dec(x_572);
x_574 = l_Lake_defaultNativeLibDir;
x_22 = x_574;
x_23 = x_573;
goto block_539;
}
}
}
}
block_539:
{
lean_object* x_24; lean_object* x_25; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_505 = l_Lake_PackageConfig_decodeToml___closed__27;
lean_inc(x_1);
x_506 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_504, x_505, x_1);
if (lean_obj_tag(x_506) == 0)
{
lean_object* x_507; 
x_507 = l_Lake_defaultBinDir;
x_24 = x_507;
x_25 = x_23;
goto block_503;
}
else
{
lean_object* x_508; lean_object* x_509; 
x_508 = lean_ctor_get(x_506, 0);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
lean_dec(x_508);
switch (lean_obj_tag(x_509)) {
case 0:
{
lean_object* x_510; 
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
lean_dec(x_509);
x_24 = x_510;
x_25 = x_23;
goto block_503;
}
case 2:
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_511 = lean_ctor_get(x_509, 0);
lean_inc(x_511);
lean_dec(x_509);
x_512 = l_Lake_Glob_decodeToml___closed__2;
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
x_514 = lean_unsigned_to_nat(1u);
x_515 = lean_mk_array(x_514, x_513);
x_516 = l_Array_append___rarg(x_23, x_515);
lean_dec(x_515);
x_517 = l_Lake_defaultBinDir;
x_24 = x_517;
x_25 = x_516;
goto block_503;
}
case 3:
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
x_518 = lean_ctor_get(x_509, 0);
lean_inc(x_518);
lean_dec(x_509);
x_519 = l_Lake_Glob_decodeToml___closed__2;
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
x_521 = lean_unsigned_to_nat(1u);
x_522 = lean_mk_array(x_521, x_520);
x_523 = l_Array_append___rarg(x_23, x_522);
lean_dec(x_522);
x_524 = l_Lake_defaultBinDir;
x_24 = x_524;
x_25 = x_523;
goto block_503;
}
default: 
{
uint8_t x_525; 
x_525 = !lean_is_exclusive(x_509);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_526 = lean_ctor_get(x_509, 1);
lean_dec(x_526);
x_527 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_509, 0);
lean_ctor_set(x_509, 1, x_527);
x_528 = lean_unsigned_to_nat(1u);
x_529 = lean_mk_array(x_528, x_509);
x_530 = l_Array_append___rarg(x_23, x_529);
lean_dec(x_529);
x_531 = l_Lake_defaultBinDir;
x_24 = x_531;
x_25 = x_530;
goto block_503;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_532 = lean_ctor_get(x_509, 0);
lean_inc(x_532);
lean_dec(x_509);
x_533 = l_Lake_Glob_decodeToml___closed__2;
x_534 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
x_535 = lean_unsigned_to_nat(1u);
x_536 = lean_mk_array(x_535, x_534);
x_537 = l_Array_append___rarg(x_23, x_536);
lean_dec(x_536);
x_538 = l_Lake_defaultBinDir;
x_24 = x_538;
x_25 = x_537;
goto block_503;
}
}
}
}
block_503:
{
lean_object* x_26; lean_object* x_27; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_469 = l_Lake_PackageConfig_decodeToml___closed__25;
lean_inc(x_1);
x_470 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_468, x_469, x_1);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; 
x_471 = l_Lake_defaultIrDir;
x_26 = x_471;
x_27 = x_25;
goto block_467;
}
else
{
lean_object* x_472; lean_object* x_473; 
x_472 = lean_ctor_get(x_470, 0);
lean_inc(x_472);
lean_dec(x_470);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec(x_472);
switch (lean_obj_tag(x_473)) {
case 0:
{
lean_object* x_474; 
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec(x_473);
x_26 = x_474;
x_27 = x_25;
goto block_467;
}
case 2:
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_475 = lean_ctor_get(x_473, 0);
lean_inc(x_475);
lean_dec(x_473);
x_476 = l_Lake_Glob_decodeToml___closed__2;
x_477 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
x_478 = lean_unsigned_to_nat(1u);
x_479 = lean_mk_array(x_478, x_477);
x_480 = l_Array_append___rarg(x_25, x_479);
lean_dec(x_479);
x_481 = l_Lake_defaultIrDir;
x_26 = x_481;
x_27 = x_480;
goto block_467;
}
case 3:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_482 = lean_ctor_get(x_473, 0);
lean_inc(x_482);
lean_dec(x_473);
x_483 = l_Lake_Glob_decodeToml___closed__2;
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
x_485 = lean_unsigned_to_nat(1u);
x_486 = lean_mk_array(x_485, x_484);
x_487 = l_Array_append___rarg(x_25, x_486);
lean_dec(x_486);
x_488 = l_Lake_defaultIrDir;
x_26 = x_488;
x_27 = x_487;
goto block_467;
}
default: 
{
uint8_t x_489; 
x_489 = !lean_is_exclusive(x_473);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_490 = lean_ctor_get(x_473, 1);
lean_dec(x_490);
x_491 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_473, 0);
lean_ctor_set(x_473, 1, x_491);
x_492 = lean_unsigned_to_nat(1u);
x_493 = lean_mk_array(x_492, x_473);
x_494 = l_Array_append___rarg(x_25, x_493);
lean_dec(x_493);
x_495 = l_Lake_defaultIrDir;
x_26 = x_495;
x_27 = x_494;
goto block_467;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_496 = lean_ctor_get(x_473, 0);
lean_inc(x_496);
lean_dec(x_473);
x_497 = l_Lake_Glob_decodeToml___closed__2;
x_498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
x_499 = lean_unsigned_to_nat(1u);
x_500 = lean_mk_array(x_499, x_498);
x_501 = l_Array_append___rarg(x_25, x_500);
lean_dec(x_500);
x_502 = l_Lake_defaultIrDir;
x_26 = x_502;
x_27 = x_501;
goto block_467;
}
}
}
}
block_467:
{
lean_object* x_28; lean_object* x_29; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_412 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_413 = l_Lake_PackageConfig_decodeToml___closed__23;
lean_inc(x_1);
x_414 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_412, x_413, x_1);
x_415 = lean_box(0);
if (lean_obj_tag(x_414) == 0)
{
x_28 = x_415;
x_29 = x_27;
goto block_411;
}
else
{
uint8_t x_416; 
x_416 = !lean_is_exclusive(x_414);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_ctor_get(x_414, 0);
x_418 = lean_ctor_get(x_417, 1);
lean_inc(x_418);
lean_dec(x_417);
switch (lean_obj_tag(x_418)) {
case 0:
{
lean_object* x_419; 
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
lean_dec(x_418);
lean_ctor_set(x_414, 0, x_419);
x_28 = x_414;
x_29 = x_27;
goto block_411;
}
case 2:
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_free_object(x_414);
x_420 = lean_ctor_get(x_418, 0);
lean_inc(x_420);
lean_dec(x_418);
x_421 = l_Lake_Glob_decodeToml___closed__2;
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_420);
lean_ctor_set(x_422, 1, x_421);
x_423 = lean_unsigned_to_nat(1u);
x_424 = lean_mk_array(x_423, x_422);
x_425 = l_Array_append___rarg(x_27, x_424);
lean_dec(x_424);
x_28 = x_415;
x_29 = x_425;
goto block_411;
}
case 3:
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_free_object(x_414);
x_426 = lean_ctor_get(x_418, 0);
lean_inc(x_426);
lean_dec(x_418);
x_427 = l_Lake_Glob_decodeToml___closed__2;
x_428 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
x_429 = lean_unsigned_to_nat(1u);
x_430 = lean_mk_array(x_429, x_428);
x_431 = l_Array_append___rarg(x_27, x_430);
lean_dec(x_430);
x_28 = x_415;
x_29 = x_431;
goto block_411;
}
default: 
{
uint8_t x_432; 
lean_free_object(x_414);
x_432 = !lean_is_exclusive(x_418);
if (x_432 == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_418, 1);
lean_dec(x_433);
x_434 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_418, 0);
lean_ctor_set(x_418, 1, x_434);
x_435 = lean_unsigned_to_nat(1u);
x_436 = lean_mk_array(x_435, x_418);
x_437 = l_Array_append___rarg(x_27, x_436);
lean_dec(x_436);
x_28 = x_415;
x_29 = x_437;
goto block_411;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_438 = lean_ctor_get(x_418, 0);
lean_inc(x_438);
lean_dec(x_418);
x_439 = l_Lake_Glob_decodeToml___closed__2;
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_unsigned_to_nat(1u);
x_442 = lean_mk_array(x_441, x_440);
x_443 = l_Array_append___rarg(x_27, x_442);
lean_dec(x_442);
x_28 = x_415;
x_29 = x_443;
goto block_411;
}
}
}
}
else
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_414, 0);
lean_inc(x_444);
lean_dec(x_414);
x_445 = lean_ctor_get(x_444, 1);
lean_inc(x_445);
lean_dec(x_444);
switch (lean_obj_tag(x_445)) {
case 0:
{
lean_object* x_446; lean_object* x_447; 
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
lean_dec(x_445);
x_447 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_447, 0, x_446);
x_28 = x_447;
x_29 = x_27;
goto block_411;
}
case 2:
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_448 = lean_ctor_get(x_445, 0);
lean_inc(x_448);
lean_dec(x_445);
x_449 = l_Lake_Glob_decodeToml___closed__2;
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_unsigned_to_nat(1u);
x_452 = lean_mk_array(x_451, x_450);
x_453 = l_Array_append___rarg(x_27, x_452);
lean_dec(x_452);
x_28 = x_415;
x_29 = x_453;
goto block_411;
}
case 3:
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_454 = lean_ctor_get(x_445, 0);
lean_inc(x_454);
lean_dec(x_445);
x_455 = l_Lake_Glob_decodeToml___closed__2;
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
x_457 = lean_unsigned_to_nat(1u);
x_458 = lean_mk_array(x_457, x_456);
x_459 = l_Array_append___rarg(x_27, x_458);
lean_dec(x_458);
x_28 = x_415;
x_29 = x_459;
goto block_411;
}
default: 
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_460 = lean_ctor_get(x_445, 0);
lean_inc(x_460);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_461 = x_445;
} else {
 lean_dec_ref(x_445);
 x_461 = lean_box(0);
}
x_462 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_461;
 lean_ctor_set_tag(x_463, 0);
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_unsigned_to_nat(1u);
x_465 = lean_mk_array(x_464, x_463);
x_466 = l_Array_append___rarg(x_27, x_465);
lean_dec(x_465);
x_28 = x_415;
x_29 = x_466;
goto block_411;
}
}
}
}
block_411:
{
lean_object* x_30; lean_object* x_31; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_356 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_357 = l_Lake_PackageConfig_decodeToml___closed__21;
lean_inc(x_1);
x_358 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_356, x_357, x_1);
x_359 = lean_box(0);
if (lean_obj_tag(x_358) == 0)
{
x_30 = x_359;
x_31 = x_29;
goto block_355;
}
else
{
uint8_t x_360; 
x_360 = !lean_is_exclusive(x_358);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_358, 0);
x_362 = lean_ctor_get(x_361, 1);
lean_inc(x_362);
lean_dec(x_361);
switch (lean_obj_tag(x_362)) {
case 0:
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec(x_362);
lean_ctor_set(x_358, 0, x_363);
x_30 = x_358;
x_31 = x_29;
goto block_355;
}
case 2:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_free_object(x_358);
x_364 = lean_ctor_get(x_362, 0);
lean_inc(x_364);
lean_dec(x_362);
x_365 = l_Lake_Glob_decodeToml___closed__2;
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_unsigned_to_nat(1u);
x_368 = lean_mk_array(x_367, x_366);
x_369 = l_Array_append___rarg(x_29, x_368);
lean_dec(x_368);
x_30 = x_359;
x_31 = x_369;
goto block_355;
}
case 3:
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_free_object(x_358);
x_370 = lean_ctor_get(x_362, 0);
lean_inc(x_370);
lean_dec(x_362);
x_371 = l_Lake_Glob_decodeToml___closed__2;
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_unsigned_to_nat(1u);
x_374 = lean_mk_array(x_373, x_372);
x_375 = l_Array_append___rarg(x_29, x_374);
lean_dec(x_374);
x_30 = x_359;
x_31 = x_375;
goto block_355;
}
default: 
{
uint8_t x_376; 
lean_free_object(x_358);
x_376 = !lean_is_exclusive(x_362);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_377 = lean_ctor_get(x_362, 1);
lean_dec(x_377);
x_378 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_362, 0);
lean_ctor_set(x_362, 1, x_378);
x_379 = lean_unsigned_to_nat(1u);
x_380 = lean_mk_array(x_379, x_362);
x_381 = l_Array_append___rarg(x_29, x_380);
lean_dec(x_380);
x_30 = x_359;
x_31 = x_381;
goto block_355;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_382 = lean_ctor_get(x_362, 0);
lean_inc(x_382);
lean_dec(x_362);
x_383 = l_Lake_Glob_decodeToml___closed__2;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_385 = lean_unsigned_to_nat(1u);
x_386 = lean_mk_array(x_385, x_384);
x_387 = l_Array_append___rarg(x_29, x_386);
lean_dec(x_386);
x_30 = x_359;
x_31 = x_387;
goto block_355;
}
}
}
}
else
{
lean_object* x_388; lean_object* x_389; 
x_388 = lean_ctor_get(x_358, 0);
lean_inc(x_388);
lean_dec(x_358);
x_389 = lean_ctor_get(x_388, 1);
lean_inc(x_389);
lean_dec(x_388);
switch (lean_obj_tag(x_389)) {
case 0:
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
lean_dec(x_389);
x_391 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_391, 0, x_390);
x_30 = x_391;
x_31 = x_29;
goto block_355;
}
case 2:
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_392 = lean_ctor_get(x_389, 0);
lean_inc(x_392);
lean_dec(x_389);
x_393 = l_Lake_Glob_decodeToml___closed__2;
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_unsigned_to_nat(1u);
x_396 = lean_mk_array(x_395, x_394);
x_397 = l_Array_append___rarg(x_29, x_396);
lean_dec(x_396);
x_30 = x_359;
x_31 = x_397;
goto block_355;
}
case 3:
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_398 = lean_ctor_get(x_389, 0);
lean_inc(x_398);
lean_dec(x_389);
x_399 = l_Lake_Glob_decodeToml___closed__2;
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_unsigned_to_nat(1u);
x_402 = lean_mk_array(x_401, x_400);
x_403 = l_Array_append___rarg(x_29, x_402);
lean_dec(x_402);
x_30 = x_359;
x_31 = x_403;
goto block_355;
}
default: 
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_404 = lean_ctor_get(x_389, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_405 = x_389;
} else {
 lean_dec_ref(x_389);
 x_405 = lean_box(0);
}
x_406 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_405)) {
 x_407 = lean_alloc_ctor(0, 2, 0);
} else {
 x_407 = x_405;
 lean_ctor_set_tag(x_407, 0);
}
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_unsigned_to_nat(1u);
x_409 = lean_mk_array(x_408, x_407);
x_410 = l_Array_append___rarg(x_29, x_409);
lean_dec(x_409);
x_30 = x_359;
x_31 = x_410;
goto block_355;
}
}
}
}
block_355:
{
uint8_t x_32; lean_object* x_33; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_314 = l_Lake_PackageConfig_decodeToml___closed__19;
lean_inc(x_1);
x_315 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_313, x_314, x_1);
if (lean_obj_tag(x_315) == 0)
{
uint8_t x_316; 
x_316 = 0;
x_32 = x_316;
x_33 = x_31;
goto block_312;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
switch (lean_obj_tag(x_318)) {
case 0:
{
uint8_t x_319; 
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; 
x_320 = lean_ctor_get(x_318, 1);
lean_dec(x_320);
x_321 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_318, 1, x_321);
x_322 = lean_unsigned_to_nat(1u);
x_323 = lean_mk_array(x_322, x_318);
x_324 = l_Array_append___rarg(x_31, x_323);
lean_dec(x_323);
x_325 = 0;
x_32 = x_325;
x_33 = x_324;
goto block_312;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; 
x_326 = lean_ctor_get(x_318, 0);
lean_inc(x_326);
lean_dec(x_318);
x_327 = l_Lake_LeanConfig_decodeToml___closed__20;
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_unsigned_to_nat(1u);
x_330 = lean_mk_array(x_329, x_328);
x_331 = l_Array_append___rarg(x_31, x_330);
lean_dec(x_330);
x_332 = 0;
x_32 = x_332;
x_33 = x_331;
goto block_312;
}
}
case 2:
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_333 = lean_ctor_get(x_318, 0);
lean_inc(x_333);
lean_dec(x_318);
x_334 = l_Lake_LeanConfig_decodeToml___closed__20;
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_333);
lean_ctor_set(x_335, 1, x_334);
x_336 = lean_unsigned_to_nat(1u);
x_337 = lean_mk_array(x_336, x_335);
x_338 = l_Array_append___rarg(x_31, x_337);
lean_dec(x_337);
x_339 = 0;
x_32 = x_339;
x_33 = x_338;
goto block_312;
}
case 3:
{
uint8_t x_340; 
x_340 = lean_ctor_get_uint8(x_318, sizeof(void*)*1);
lean_dec(x_318);
x_32 = x_340;
x_33 = x_31;
goto block_312;
}
default: 
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_318);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_342 = lean_ctor_get(x_318, 1);
lean_dec(x_342);
x_343 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_318, 0);
lean_ctor_set(x_318, 1, x_343);
x_344 = lean_unsigned_to_nat(1u);
x_345 = lean_mk_array(x_344, x_318);
x_346 = l_Array_append___rarg(x_31, x_345);
lean_dec(x_345);
x_347 = 0;
x_32 = x_347;
x_33 = x_346;
goto block_312;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_348 = lean_ctor_get(x_318, 0);
lean_inc(x_348);
lean_dec(x_318);
x_349 = l_Lake_LeanConfig_decodeToml___closed__20;
x_350 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_unsigned_to_nat(1u);
x_352 = lean_mk_array(x_351, x_350);
x_353 = l_Array_append___rarg(x_31, x_352);
lean_dec(x_352);
x_354 = 0;
x_32 = x_354;
x_33 = x_353;
goto block_312;
}
}
}
}
block_312:
{
lean_object* x_34; lean_object* x_35; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_278 = l_Lake_PackageConfig_decodeToml___closed__17;
lean_inc(x_1);
x_279 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_277, x_278, x_1);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
x_280 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_280;
x_35 = x_33;
goto block_276;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_279, 0);
lean_inc(x_281);
lean_dec(x_279);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
switch (lean_obj_tag(x_282)) {
case 0:
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_282, 1);
lean_inc(x_283);
lean_dec(x_282);
x_34 = x_283;
x_35 = x_33;
goto block_276;
}
case 2:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_282, 0);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lake_Glob_decodeToml___closed__2;
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_unsigned_to_nat(1u);
x_288 = lean_mk_array(x_287, x_286);
x_289 = l_Array_append___rarg(x_33, x_288);
lean_dec(x_288);
x_290 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_290;
x_35 = x_289;
goto block_276;
}
case 3:
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_291 = lean_ctor_get(x_282, 0);
lean_inc(x_291);
lean_dec(x_282);
x_292 = l_Lake_Glob_decodeToml___closed__2;
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_291);
lean_ctor_set(x_293, 1, x_292);
x_294 = lean_unsigned_to_nat(1u);
x_295 = lean_mk_array(x_294, x_293);
x_296 = l_Array_append___rarg(x_33, x_295);
lean_dec(x_295);
x_297 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_297;
x_35 = x_296;
goto block_276;
}
default: 
{
uint8_t x_298; 
x_298 = !lean_is_exclusive(x_282);
if (x_298 == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_299 = lean_ctor_get(x_282, 1);
lean_dec(x_299);
x_300 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_282, 0);
lean_ctor_set(x_282, 1, x_300);
x_301 = lean_unsigned_to_nat(1u);
x_302 = lean_mk_array(x_301, x_282);
x_303 = l_Array_append___rarg(x_33, x_302);
lean_dec(x_302);
x_304 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_304;
x_35 = x_303;
goto block_276;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_305 = lean_ctor_get(x_282, 0);
lean_inc(x_305);
lean_dec(x_282);
x_306 = l_Lake_Glob_decodeToml___closed__2;
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_308 = lean_unsigned_to_nat(1u);
x_309 = lean_mk_array(x_308, x_307);
x_310 = l_Array_append___rarg(x_33, x_309);
lean_dec(x_309);
x_311 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_311;
x_35 = x_310;
goto block_276;
}
}
}
}
block_276:
{
lean_object* x_36; lean_object* x_37; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_242 = l_Lake_PackageConfig_decodeToml___closed__15;
lean_inc(x_1);
x_243 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_241, x_242, x_1);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; 
x_244 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_244;
x_37 = x_35;
goto block_240;
}
else
{
lean_object* x_245; lean_object* x_246; 
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
lean_dec(x_243);
x_246 = lean_ctor_get(x_245, 1);
lean_inc(x_246);
lean_dec(x_245);
switch (lean_obj_tag(x_246)) {
case 0:
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_246, 1);
lean_inc(x_247);
lean_dec(x_246);
x_36 = x_247;
x_37 = x_35;
goto block_240;
}
case 2:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_248 = lean_ctor_get(x_246, 0);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lake_Glob_decodeToml___closed__2;
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_unsigned_to_nat(1u);
x_252 = lean_mk_array(x_251, x_250);
x_253 = l_Array_append___rarg(x_35, x_252);
lean_dec(x_252);
x_254 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_254;
x_37 = x_253;
goto block_240;
}
case 3:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_255 = lean_ctor_get(x_246, 0);
lean_inc(x_255);
lean_dec(x_246);
x_256 = l_Lake_Glob_decodeToml___closed__2;
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_unsigned_to_nat(1u);
x_259 = lean_mk_array(x_258, x_257);
x_260 = l_Array_append___rarg(x_35, x_259);
lean_dec(x_259);
x_261 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_261;
x_37 = x_260;
goto block_240;
}
default: 
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_246);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_ctor_get(x_246, 1);
lean_dec(x_263);
x_264 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_246, 0);
lean_ctor_set(x_246, 1, x_264);
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_mk_array(x_265, x_246);
x_267 = l_Array_append___rarg(x_35, x_266);
lean_dec(x_266);
x_268 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_268;
x_37 = x_267;
goto block_240;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_269 = lean_ctor_get(x_246, 0);
lean_inc(x_269);
lean_dec(x_246);
x_270 = l_Lake_Glob_decodeToml___closed__2;
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_unsigned_to_nat(1u);
x_273 = lean_mk_array(x_272, x_271);
x_274 = l_Array_append___rarg(x_35, x_273);
lean_dec(x_273);
x_275 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_275;
x_37 = x_274;
goto block_240;
}
}
}
}
block_240:
{
uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = l_String_isEmpty(x_34);
x_39 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_40 = l_Lake_PackageConfig_decodeToml___closed__4;
lean_inc(x_1);
x_41 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_40, x_1);
if (x_38 == 0)
{
uint8_t x_236; 
x_236 = l_Lake_PackageConfig_decodeToml___closed__12;
if (x_236 == 0)
{
lean_dec(x_34);
x_42 = x_36;
goto block_235;
}
else
{
uint8_t x_237; 
x_237 = l_String_isEmpty(x_36);
if (x_237 == 0)
{
lean_dec(x_34);
x_42 = x_36;
goto block_235;
}
else
{
lean_dec(x_36);
x_42 = x_34;
goto block_235;
}
}
}
else
{
uint8_t x_238; 
x_238 = l_Lake_PackageConfig_decodeToml___closed__13;
if (x_238 == 0)
{
lean_dec(x_34);
x_42 = x_36;
goto block_235;
}
else
{
uint8_t x_239; 
x_239 = l_String_isEmpty(x_36);
if (x_239 == 0)
{
lean_dec(x_34);
x_42 = x_36;
goto block_235;
}
else
{
lean_dec(x_36);
x_42 = x_34;
goto block_235;
}
}
}
block_235:
{
lean_object* x_43; lean_object* x_44; 
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_184; 
x_184 = l_Lake_LeanOption_decodeToml___closed__4;
x_43 = x_184;
x_44 = x_37;
goto block_183;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_41, 0);
lean_inc(x_185);
lean_dec(x_41);
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec(x_185);
switch (lean_obj_tag(x_186)) {
case 0:
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_186, 1);
lean_dec(x_188);
x_189 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_186, 1, x_189);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_mk_array(x_190, x_186);
x_192 = l_Array_append___rarg(x_37, x_191);
lean_dec(x_191);
x_193 = l_Lake_LeanOption_decodeToml___closed__4;
x_43 = x_193;
x_44 = x_192;
goto block_183;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_186, 0);
lean_inc(x_194);
lean_dec(x_186);
x_195 = l_Lake_LeanConfig_decodeToml___closed__5;
x_196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_unsigned_to_nat(1u);
x_198 = lean_mk_array(x_197, x_196);
x_199 = l_Array_append___rarg(x_37, x_198);
lean_dec(x_198);
x_200 = l_Lake_LeanOption_decodeToml___closed__4;
x_43 = x_200;
x_44 = x_199;
goto block_183;
}
}
case 2:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_201 = lean_ctor_get(x_186, 0);
lean_inc(x_201);
lean_dec(x_186);
x_202 = l_Lake_LeanConfig_decodeToml___closed__5;
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_mk_array(x_204, x_203);
x_206 = l_Array_append___rarg(x_37, x_205);
lean_dec(x_205);
x_207 = l_Lake_LeanOption_decodeToml___closed__4;
x_43 = x_207;
x_44 = x_206;
goto block_183;
}
case 3:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_186, 0);
lean_inc(x_208);
lean_dec(x_186);
x_209 = l_Lake_LeanConfig_decodeToml___closed__5;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_mk_array(x_211, x_210);
x_213 = l_Array_append___rarg(x_37, x_212);
lean_dec(x_212);
x_214 = l_Lake_LeanOption_decodeToml___closed__4;
x_43 = x_214;
x_44 = x_213;
goto block_183;
}
case 5:
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_186, 1);
lean_inc(x_215);
lean_dec(x_186);
x_216 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_215);
lean_dec(x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec(x_216);
x_218 = l_Array_append___rarg(x_37, x_217);
lean_dec(x_217);
x_219 = l_Lake_LeanOption_decodeToml___closed__4;
x_43 = x_219;
x_44 = x_218;
goto block_183;
}
else
{
lean_object* x_220; 
x_220 = lean_ctor_get(x_216, 0);
lean_inc(x_220);
lean_dec(x_216);
x_43 = x_220;
x_44 = x_37;
goto block_183;
}
}
default: 
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_186);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_186, 1);
lean_dec(x_222);
x_223 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_186, 0);
lean_ctor_set(x_186, 1, x_223);
x_224 = lean_unsigned_to_nat(1u);
x_225 = lean_mk_array(x_224, x_186);
x_226 = l_Array_append___rarg(x_37, x_225);
lean_dec(x_225);
x_227 = l_Lake_LeanOption_decodeToml___closed__4;
x_43 = x_227;
x_44 = x_226;
goto block_183;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_228 = lean_ctor_get(x_186, 0);
lean_inc(x_228);
lean_dec(x_186);
x_229 = l_Lake_LeanConfig_decodeToml___closed__5;
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_unsigned_to_nat(1u);
x_232 = lean_mk_array(x_231, x_230);
x_233 = l_Array_append___rarg(x_37, x_232);
lean_dec(x_232);
x_234 = l_Lake_LeanOption_decodeToml___closed__4;
x_43 = x_234;
x_44 = x_233;
goto block_183;
}
}
}
}
block_183:
{
lean_object* x_45; lean_object* x_46; lean_object* x_149; lean_object* x_150; 
x_149 = l_Lake_PackageConfig_decodeToml___closed__11;
lean_inc(x_1);
x_150 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_149, x_1);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_45 = x_151;
x_46 = x_44;
goto block_148;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
switch (lean_obj_tag(x_153)) {
case 0:
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_45 = x_154;
x_46 = x_44;
goto block_148;
}
case 2:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lake_Glob_decodeToml___closed__2;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_mk_array(x_158, x_157);
x_160 = l_Array_append___rarg(x_44, x_159);
lean_dec(x_159);
x_161 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_45 = x_161;
x_46 = x_160;
goto block_148;
}
case 3:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_153, 0);
lean_inc(x_162);
lean_dec(x_153);
x_163 = l_Lake_Glob_decodeToml___closed__2;
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_mk_array(x_165, x_164);
x_167 = l_Array_append___rarg(x_44, x_166);
lean_dec(x_166);
x_168 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_45 = x_168;
x_46 = x_167;
goto block_148;
}
default: 
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_153);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_170 = lean_ctor_get(x_153, 1);
lean_dec(x_170);
x_171 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_153, 0);
lean_ctor_set(x_153, 1, x_171);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_mk_array(x_172, x_153);
x_174 = l_Array_append___rarg(x_44, x_173);
lean_dec(x_173);
x_175 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_45 = x_175;
x_46 = x_174;
goto block_148;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_153, 0);
lean_inc(x_176);
lean_dec(x_153);
x_177 = l_Lake_Glob_decodeToml___closed__2;
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_unsigned_to_nat(1u);
x_180 = lean_mk_array(x_179, x_178);
x_181 = l_Array_append___rarg(x_44, x_180);
lean_dec(x_180);
x_182 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_45 = x_182;
x_46 = x_181;
goto block_148;
}
}
}
}
block_148:
{
lean_object* x_47; lean_object* x_48; lean_object* x_95; lean_object* x_96; 
x_95 = l_Lake_PackageConfig_decodeToml___closed__9;
lean_inc(x_1);
x_96 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_95, x_1);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = l_Lake_LeanOption_decodeToml___closed__4;
x_47 = x_97;
x_48 = x_46;
goto block_94;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
switch (lean_obj_tag(x_99)) {
case 0:
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_99, 1);
lean_dec(x_101);
x_102 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_99, 1, x_102);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_mk_array(x_103, x_99);
x_105 = l_Array_append___rarg(x_46, x_104);
lean_dec(x_104);
x_106 = l_Lake_LeanOption_decodeToml___closed__4;
x_47 = x_106;
x_48 = x_105;
goto block_94;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_99, 0);
lean_inc(x_107);
lean_dec(x_99);
x_108 = l_Lake_LeanConfig_decodeToml___closed__5;
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_mk_array(x_110, x_109);
x_112 = l_Array_append___rarg(x_46, x_111);
lean_dec(x_111);
x_113 = l_Lake_LeanOption_decodeToml___closed__4;
x_47 = x_113;
x_48 = x_112;
goto block_94;
}
}
case 2:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_99, 0);
lean_inc(x_114);
lean_dec(x_99);
x_115 = l_Lake_LeanConfig_decodeToml___closed__5;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_mk_array(x_117, x_116);
x_119 = l_Array_append___rarg(x_46, x_118);
lean_dec(x_118);
x_120 = l_Lake_LeanOption_decodeToml___closed__4;
x_47 = x_120;
x_48 = x_119;
goto block_94;
}
case 3:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_121 = lean_ctor_get(x_99, 0);
lean_inc(x_121);
lean_dec(x_99);
x_122 = l_Lake_LeanConfig_decodeToml___closed__5;
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_mk_array(x_124, x_123);
x_126 = l_Array_append___rarg(x_46, x_125);
lean_dec(x_125);
x_127 = l_Lake_LeanOption_decodeToml___closed__4;
x_47 = x_127;
x_48 = x_126;
goto block_94;
}
case 5:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_99, 1);
lean_inc(x_128);
lean_dec(x_99);
x_129 = l_Lake_Toml_decodeArray___at_Lake_LeanConfig_decodeToml___spec__1(x_128);
lean_dec(x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_Array_append___rarg(x_46, x_130);
lean_dec(x_130);
x_132 = l_Lake_LeanOption_decodeToml___closed__4;
x_47 = x_132;
x_48 = x_131;
goto block_94;
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_129, 0);
lean_inc(x_133);
lean_dec(x_129);
x_47 = x_133;
x_48 = x_46;
goto block_94;
}
}
default: 
{
uint8_t x_134; 
x_134 = !lean_is_exclusive(x_99);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_135 = lean_ctor_get(x_99, 1);
lean_dec(x_135);
x_136 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_99, 0);
lean_ctor_set(x_99, 1, x_136);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_mk_array(x_137, x_99);
x_139 = l_Array_append___rarg(x_46, x_138);
lean_dec(x_138);
x_140 = l_Lake_LeanOption_decodeToml___closed__4;
x_47 = x_140;
x_48 = x_139;
goto block_94;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_141 = lean_ctor_get(x_99, 0);
lean_inc(x_141);
lean_dec(x_99);
x_142 = l_Lake_LeanConfig_decodeToml___closed__5;
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_mk_array(x_144, x_143);
x_146 = l_Array_append___rarg(x_46, x_145);
lean_dec(x_145);
x_147 = l_Lake_LeanOption_decodeToml___closed__4;
x_47 = x_147;
x_48 = x_146;
goto block_94;
}
}
}
}
block_94:
{
lean_object* x_49; lean_object* x_50; lean_object* x_89; 
lean_inc(x_1);
x_89 = l_Lake_LeanConfig_decodeToml(x_1);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
x_91 = l_Array_append___rarg(x_48, x_90);
lean_dec(x_90);
x_92 = l_Lake_PackageConfig_decodeToml___closed__7;
x_49 = x_92;
x_50 = x_91;
goto block_88;
}
else
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
x_49 = x_93;
x_50 = x_48;
goto block_88;
}
block_88:
{
lean_object* x_51; 
x_51 = l_Lake_WorkspaceConfig_decodeToml(x_1);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Array_append___rarg(x_50, x_52);
lean_dec(x_52);
x_54 = lean_box(0);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_55 = 0;
lean_inc(x_11);
x_56 = l_Lean_Name_toString(x_11, x_55);
x_57 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_58 = lean_string_append(x_57, x_56);
lean_dec(x_56);
x_59 = l_Lake_PackageConfig_decodeToml___closed__5;
x_60 = lean_string_append(x_58, x_59);
x_61 = l_System_Platform_target;
x_62 = lean_string_append(x_60, x_61);
x_63 = l_Lake_PackageConfig_decodeToml___closed__6;
x_64 = lean_string_append(x_62, x_63);
x_65 = l_Lake_LeanOption_decodeToml___closed__4;
x_66 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_66, 0, x_57);
lean_ctor_set(x_66, 1, x_49);
lean_ctor_set(x_66, 2, x_11);
lean_ctor_set(x_66, 3, x_54);
lean_ctor_set(x_66, 4, x_65);
lean_ctor_set(x_66, 5, x_65);
lean_ctor_set(x_66, 6, x_14);
lean_ctor_set(x_66, 7, x_16);
lean_ctor_set(x_66, 8, x_18);
lean_ctor_set(x_66, 9, x_20);
lean_ctor_set(x_66, 10, x_22);
lean_ctor_set(x_66, 11, x_24);
lean_ctor_set(x_66, 12, x_26);
lean_ctor_set(x_66, 13, x_54);
lean_ctor_set(x_66, 14, x_28);
lean_ctor_set(x_66, 15, x_30);
lean_ctor_set(x_66, 16, x_64);
lean_ctor_set(x_66, 17, x_42);
lean_ctor_set(x_66, 18, x_43);
lean_ctor_set(x_66, 19, x_45);
lean_ctor_set(x_66, 20, x_47);
lean_ctor_set_uint8(x_66, sizeof(void*)*21, x_12);
lean_ctor_set_uint8(x_66, sizeof(void*)*21 + 1, x_32);
x_3 = x_66;
x_4 = x_53;
goto block_8;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_30, 0);
lean_inc(x_67);
x_68 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_69 = l_Lake_LeanOption_decodeToml___closed__4;
x_70 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_49);
lean_ctor_set(x_70, 2, x_11);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_69);
lean_ctor_set(x_70, 6, x_14);
lean_ctor_set(x_70, 7, x_16);
lean_ctor_set(x_70, 8, x_18);
lean_ctor_set(x_70, 9, x_20);
lean_ctor_set(x_70, 10, x_22);
lean_ctor_set(x_70, 11, x_24);
lean_ctor_set(x_70, 12, x_26);
lean_ctor_set(x_70, 13, x_54);
lean_ctor_set(x_70, 14, x_28);
lean_ctor_set(x_70, 15, x_30);
lean_ctor_set(x_70, 16, x_67);
lean_ctor_set(x_70, 17, x_42);
lean_ctor_set(x_70, 18, x_43);
lean_ctor_set(x_70, 19, x_45);
lean_ctor_set(x_70, 20, x_47);
lean_ctor_set_uint8(x_70, sizeof(void*)*21, x_12);
lean_ctor_set_uint8(x_70, sizeof(void*)*21 + 1, x_32);
x_3 = x_70;
x_4 = x_53;
goto block_8;
}
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_51, 0);
lean_inc(x_71);
lean_dec(x_51);
x_72 = lean_box(0);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = 0;
lean_inc(x_11);
x_74 = l_Lean_Name_toString(x_11, x_73);
x_75 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_76 = lean_string_append(x_75, x_74);
lean_dec(x_74);
x_77 = l_Lake_PackageConfig_decodeToml___closed__5;
x_78 = lean_string_append(x_76, x_77);
x_79 = l_System_Platform_target;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_Lake_PackageConfig_decodeToml___closed__6;
x_82 = lean_string_append(x_80, x_81);
x_83 = l_Lake_LeanOption_decodeToml___closed__4;
x_84 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_84, 0, x_71);
lean_ctor_set(x_84, 1, x_49);
lean_ctor_set(x_84, 2, x_11);
lean_ctor_set(x_84, 3, x_72);
lean_ctor_set(x_84, 4, x_83);
lean_ctor_set(x_84, 5, x_83);
lean_ctor_set(x_84, 6, x_14);
lean_ctor_set(x_84, 7, x_16);
lean_ctor_set(x_84, 8, x_18);
lean_ctor_set(x_84, 9, x_20);
lean_ctor_set(x_84, 10, x_22);
lean_ctor_set(x_84, 11, x_24);
lean_ctor_set(x_84, 12, x_26);
lean_ctor_set(x_84, 13, x_72);
lean_ctor_set(x_84, 14, x_28);
lean_ctor_set(x_84, 15, x_30);
lean_ctor_set(x_84, 16, x_82);
lean_ctor_set(x_84, 17, x_42);
lean_ctor_set(x_84, 18, x_43);
lean_ctor_set(x_84, 19, x_45);
lean_ctor_set(x_84, 20, x_47);
lean_ctor_set_uint8(x_84, sizeof(void*)*21, x_12);
lean_ctor_set_uint8(x_84, sizeof(void*)*21 + 1, x_32);
x_3 = x_84;
x_4 = x_50;
goto block_8;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_30, 0);
lean_inc(x_85);
x_86 = l_Lake_LeanOption_decodeToml___closed__4;
x_87 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_87, 0, x_71);
lean_ctor_set(x_87, 1, x_49);
lean_ctor_set(x_87, 2, x_11);
lean_ctor_set(x_87, 3, x_72);
lean_ctor_set(x_87, 4, x_86);
lean_ctor_set(x_87, 5, x_86);
lean_ctor_set(x_87, 6, x_14);
lean_ctor_set(x_87, 7, x_16);
lean_ctor_set(x_87, 8, x_18);
lean_ctor_set(x_87, 9, x_20);
lean_ctor_set(x_87, 10, x_22);
lean_ctor_set(x_87, 11, x_24);
lean_ctor_set(x_87, 12, x_26);
lean_ctor_set(x_87, 13, x_72);
lean_ctor_set(x_87, 14, x_28);
lean_ctor_set(x_87, 15, x_30);
lean_ctor_set(x_87, 16, x_85);
lean_ctor_set(x_87, 17, x_42);
lean_ctor_set(x_87, 18, x_43);
lean_ctor_set(x_87, 19, x_45);
lean_ctor_set(x_87, 20, x_47);
lean_ctor_set_uint8(x_87, sizeof(void*)*21, x_12);
lean_ctor_set_uint8(x_87, sizeof(void*)*21 + 1, x_32);
x_3 = x_87;
x_4 = x_50;
goto block_8;
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
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_PackageConfig_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_PackageConfig_decodeToml___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlPackageConfig(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_PackageConfig_decodeToml(x_27, x_26);
return x_28;
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 1);
lean_dec(x_30);
x_31 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_array(x_32, x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_array(x_38, x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = l_String_toName(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
lean_ctor_set(x_6, 1, x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_array(x_14, x_6);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_18 = l_Lake_mergeErrors___rarg(x_4, x_16, x_17);
x_2 = x_8;
x_4 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_6);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_12);
x_21 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_22 = l_Lake_mergeErrors___rarg(x_4, x_20, x_21);
x_2 = x_8;
x_4 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = l_String_toName(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_mk_array(x_29, x_28);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_33 = l_Lake_mergeErrors___rarg(x_4, x_31, x_32);
x_2 = x_8;
x_4 = x_33;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_26);
x_36 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_37 = l_Lake_mergeErrors___rarg(x_4, x_35, x_36);
x_2 = x_8;
x_4 = x_37;
goto _start;
}
}
}
case 2:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
lean_dec(x_6);
x_40 = l_Lake_Glob_decodeToml___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_mk_array(x_42, x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_46 = l_Lake_mergeErrors___rarg(x_4, x_44, x_45);
x_2 = x_8;
x_4 = x_46;
goto _start;
}
case 3:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_6, 0);
lean_inc(x_48);
lean_dec(x_6);
x_49 = l_Lake_Glob_decodeToml___closed__2;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_mk_array(x_51, x_50);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_55 = l_Lake_mergeErrors___rarg(x_4, x_53, x_54);
x_2 = x_8;
x_4 = x_55;
goto _start;
}
default: 
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_6);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_6, 1);
lean_dec(x_58);
x_59 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_59);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_mk_array(x_60, x_6);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_64 = l_Lake_mergeErrors___rarg(x_4, x_62, x_63);
x_2 = x_8;
x_4 = x_64;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_ctor_get(x_6, 0);
lean_inc(x_66);
lean_dec(x_6);
x_67 = l_Lake_Glob_decodeToml___closed__2;
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_unsigned_to_nat(1u);
x_70 = lean_mk_array(x_69, x_68);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_73 = l_Lake_mergeErrors___rarg(x_4, x_71, x_72);
x_2 = x_8;
x_4 = x_73;
goto _start;
}
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_2, x_2);
if (x_7 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__2(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lake_Glob_decodeToml(x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_mk_array(x_12, x_11);
lean_ctor_set(x_7, 0, x_13);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_15 = l_Lake_mergeErrors___rarg(x_4, x_7, x_14);
x_2 = x_9;
x_4 = x_15;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_mk_array(x_18, x_17);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_22 = l_Lake_mergeErrors___rarg(x_4, x_20, x_21);
x_2 = x_9;
x_4 = x_22;
goto _start;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_26 = l_Lake_mergeErrors___rarg(x_4, x_7, x_25);
x_2 = x_9;
x_4 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_31 = l_Lake_mergeErrors___rarg(x_4, x_29, x_30);
x_2 = x_9;
x_4 = x_31;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_2, x_2);
if (x_7 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__4(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("o", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanOption_decodeToml___closed__2;
x_2 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("export", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1;
x_2 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanOption_decodeToml___closed__2;
x_2 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__6;
return x_3;
}
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultFacets", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanArts", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanOption_decodeToml___closed__2;
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("libName", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("globs", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("roots", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_274; lean_object* x_275; 
x_274 = l_Lake_LeanOption_decodeToml___closed__11;
lean_inc(x_1);
x_275 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(x_1, x_274, x_2);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec(x_275);
x_277 = l_Lake_LeanOption_decodeToml___closed__4;
x_278 = l_Array_append___rarg(x_277, x_276);
lean_dec(x_276);
x_279 = lean_box(0);
x_9 = x_279;
x_10 = x_278;
goto block_273;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_275, 0);
lean_inc(x_280);
lean_dec(x_275);
x_281 = l_Lake_LeanOption_decodeToml___closed__4;
x_9 = x_280;
x_10 = x_281;
goto block_273;
}
block_8:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
}
block_273:
{
lean_object* x_11; lean_object* x_12; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_239 = l_Lake_PackageConfig_decodeToml___closed__35;
lean_inc(x_1);
x_240 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_238, x_239, x_1);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; 
x_241 = l_Lake_PackageConfig_decodeToml___closed__36;
x_11 = x_241;
x_12 = x_10;
goto block_237;
}
else
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
switch (lean_obj_tag(x_243)) {
case 0:
{
lean_object* x_244; 
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_11 = x_244;
x_12 = x_10;
goto block_237;
}
case 2:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_245 = lean_ctor_get(x_243, 0);
lean_inc(x_245);
lean_dec(x_243);
x_246 = l_Lake_Glob_decodeToml___closed__2;
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_mk_array(x_248, x_247);
x_250 = l_Array_append___rarg(x_10, x_249);
lean_dec(x_249);
x_251 = l_Lake_PackageConfig_decodeToml___closed__36;
x_11 = x_251;
x_12 = x_250;
goto block_237;
}
case 3:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_252 = lean_ctor_get(x_243, 0);
lean_inc(x_252);
lean_dec(x_243);
x_253 = l_Lake_Glob_decodeToml___closed__2;
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_mk_array(x_255, x_254);
x_257 = l_Array_append___rarg(x_10, x_256);
lean_dec(x_256);
x_258 = l_Lake_PackageConfig_decodeToml___closed__36;
x_11 = x_258;
x_12 = x_257;
goto block_237;
}
default: 
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_243);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_260 = lean_ctor_get(x_243, 1);
lean_dec(x_260);
x_261 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_243, 0);
lean_ctor_set(x_243, 1, x_261);
x_262 = lean_unsigned_to_nat(1u);
x_263 = lean_mk_array(x_262, x_243);
x_264 = l_Array_append___rarg(x_10, x_263);
lean_dec(x_263);
x_265 = l_Lake_PackageConfig_decodeToml___closed__36;
x_11 = x_265;
x_12 = x_264;
goto block_237;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_243, 0);
lean_inc(x_266);
lean_dec(x_243);
x_267 = l_Lake_Glob_decodeToml___closed__2;
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_unsigned_to_nat(1u);
x_270 = lean_mk_array(x_269, x_268);
x_271 = l_Array_append___rarg(x_10, x_270);
lean_dec(x_270);
x_272 = l_Lake_PackageConfig_decodeToml___closed__36;
x_11 = x_272;
x_12 = x_271;
goto block_237;
}
}
}
}
block_237:
{
lean_object* x_13; lean_object* x_14; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = l_Lake_LeanOption_decodeToml___closed__2;
lean_inc(x_9);
x_190 = lean_array_push(x_189, x_9);
x_191 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_192 = l_Lake_LeanLibConfig_decodeToml___closed__12;
lean_inc(x_1);
x_193 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_191, x_192, x_1);
if (lean_obj_tag(x_193) == 0)
{
x_13 = x_190;
x_14 = x_12;
goto block_188;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
lean_dec(x_194);
switch (lean_obj_tag(x_195)) {
case 0:
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_195);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_195, 1);
lean_dec(x_197);
x_198 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_195, 1, x_198);
x_199 = lean_unsigned_to_nat(1u);
x_200 = lean_mk_array(x_199, x_195);
x_201 = l_Array_append___rarg(x_12, x_200);
lean_dec(x_200);
x_13 = x_190;
x_14 = x_201;
goto block_188;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_202 = lean_ctor_get(x_195, 0);
lean_inc(x_202);
lean_dec(x_195);
x_203 = l_Lake_LeanConfig_decodeToml___closed__5;
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_unsigned_to_nat(1u);
x_206 = lean_mk_array(x_205, x_204);
x_207 = l_Array_append___rarg(x_12, x_206);
lean_dec(x_206);
x_13 = x_190;
x_14 = x_207;
goto block_188;
}
}
case 2:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_195, 0);
lean_inc(x_208);
lean_dec(x_195);
x_209 = l_Lake_LeanConfig_decodeToml___closed__5;
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_mk_array(x_211, x_210);
x_213 = l_Array_append___rarg(x_12, x_212);
lean_dec(x_212);
x_13 = x_190;
x_14 = x_213;
goto block_188;
}
case 3:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_214 = lean_ctor_get(x_195, 0);
lean_inc(x_214);
lean_dec(x_195);
x_215 = l_Lake_LeanConfig_decodeToml___closed__5;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_mk_array(x_217, x_216);
x_219 = l_Array_append___rarg(x_12, x_218);
lean_dec(x_218);
x_13 = x_190;
x_14 = x_219;
goto block_188;
}
case 5:
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_195, 1);
lean_inc(x_220);
lean_dec(x_195);
x_221 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(x_220);
lean_dec(x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
lean_dec(x_221);
x_223 = l_Array_append___rarg(x_12, x_222);
lean_dec(x_222);
x_13 = x_190;
x_14 = x_223;
goto block_188;
}
else
{
lean_object* x_224; 
lean_dec(x_190);
x_224 = lean_ctor_get(x_221, 0);
lean_inc(x_224);
lean_dec(x_221);
x_13 = x_224;
x_14 = x_12;
goto block_188;
}
}
default: 
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_195);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_195, 1);
lean_dec(x_226);
x_227 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_195, 0);
lean_ctor_set(x_195, 1, x_227);
x_228 = lean_unsigned_to_nat(1u);
x_229 = lean_mk_array(x_228, x_195);
x_230 = l_Array_append___rarg(x_12, x_229);
lean_dec(x_229);
x_13 = x_190;
x_14 = x_230;
goto block_188;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_231 = lean_ctor_get(x_195, 0);
lean_inc(x_231);
lean_dec(x_195);
x_232 = l_Lake_LeanConfig_decodeToml___closed__5;
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_unsigned_to_nat(1u);
x_235 = lean_mk_array(x_234, x_233);
x_236 = l_Array_append___rarg(x_12, x_235);
lean_dec(x_235);
x_13 = x_190;
x_14 = x_236;
goto block_188;
}
}
}
}
block_188:
{
lean_object* x_15; lean_object* x_16; lean_object* x_166; size_t x_167; size_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_166 = lean_array_get_size(x_13);
x_167 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_168 = 0;
lean_inc(x_13);
x_169 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_globs___default___spec__1(x_167, x_168, x_13);
x_170 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_171 = l_Lake_LeanLibConfig_decodeToml___closed__10;
lean_inc(x_1);
x_172 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_170, x_171, x_1);
if (lean_obj_tag(x_172) == 0)
{
x_15 = x_169;
x_16 = x_14;
goto block_165;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec(x_172);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
if (lean_obj_tag(x_174) == 5)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__3(x_175);
lean_dec(x_175);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Array_append___rarg(x_14, x_177);
lean_dec(x_177);
x_15 = x_169;
x_16 = x_178;
goto block_165;
}
else
{
lean_object* x_179; 
lean_dec(x_169);
x_179 = lean_ctor_get(x_176, 0);
lean_inc(x_179);
lean_dec(x_176);
x_15 = x_179;
x_16 = x_14;
goto block_165;
}
}
else
{
lean_object* x_180; 
x_180 = l_Lake_Glob_decodeToml(x_174);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_mk_array(x_182, x_181);
x_184 = l_Array_append___rarg(x_14, x_183);
lean_dec(x_183);
x_15 = x_169;
x_16 = x_184;
goto block_165;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_169);
x_185 = lean_ctor_get(x_180, 0);
lean_inc(x_185);
lean_dec(x_180);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_mk_array(x_186, x_185);
x_15 = x_187;
x_16 = x_14;
goto block_165;
}
}
}
block_165:
{
lean_object* x_17; lean_object* x_18; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = 0;
lean_inc(x_9);
x_134 = l_Lean_Name_toString(x_9, x_133);
x_135 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_136 = l_Lake_LeanLibConfig_decodeToml___closed__8;
lean_inc(x_1);
x_137 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_135, x_136, x_1);
if (lean_obj_tag(x_137) == 0)
{
x_17 = x_134;
x_18 = x_16;
goto block_132;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
switch (lean_obj_tag(x_139)) {
case 0:
{
lean_object* x_140; 
lean_dec(x_134);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_17 = x_140;
x_18 = x_16;
goto block_132;
}
case 2:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_139, 0);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lake_Glob_decodeToml___closed__2;
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_mk_array(x_144, x_143);
x_146 = l_Array_append___rarg(x_16, x_145);
lean_dec(x_145);
x_17 = x_134;
x_18 = x_146;
goto block_132;
}
case 3:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_139, 0);
lean_inc(x_147);
lean_dec(x_139);
x_148 = l_Lake_Glob_decodeToml___closed__2;
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_unsigned_to_nat(1u);
x_151 = lean_mk_array(x_150, x_149);
x_152 = l_Array_append___rarg(x_16, x_151);
lean_dec(x_151);
x_17 = x_134;
x_18 = x_152;
goto block_132;
}
default: 
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_139);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_139, 1);
lean_dec(x_154);
x_155 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_139, 0);
lean_ctor_set(x_139, 1, x_155);
x_156 = lean_unsigned_to_nat(1u);
x_157 = lean_mk_array(x_156, x_139);
x_158 = l_Array_append___rarg(x_16, x_157);
lean_dec(x_157);
x_17 = x_134;
x_18 = x_158;
goto block_132;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_139, 0);
lean_inc(x_159);
lean_dec(x_139);
x_160 = l_Lake_Glob_decodeToml___closed__2;
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_unsigned_to_nat(1u);
x_163 = lean_mk_array(x_162, x_161);
x_164 = l_Array_append___rarg(x_16, x_163);
lean_dec(x_163);
x_17 = x_134;
x_18 = x_164;
goto block_132;
}
}
}
}
block_132:
{
uint8_t x_19; lean_object* x_20; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_91 = l_Lake_PackageConfig_decodeToml___closed__38;
lean_inc(x_1);
x_92 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_90, x_91, x_1);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = 0;
x_19 = x_93;
x_20 = x_18;
goto block_89;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
switch (lean_obj_tag(x_95)) {
case 0:
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_95, 1);
lean_dec(x_97);
x_98 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_95, 1, x_98);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_mk_array(x_99, x_95);
x_101 = l_Array_append___rarg(x_18, x_100);
lean_dec(x_100);
x_102 = 0;
x_19 = x_102;
x_20 = x_101;
goto block_89;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_103 = lean_ctor_get(x_95, 0);
lean_inc(x_103);
lean_dec(x_95);
x_104 = l_Lake_LeanConfig_decodeToml___closed__20;
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_mk_array(x_106, x_105);
x_108 = l_Array_append___rarg(x_18, x_107);
lean_dec(x_107);
x_109 = 0;
x_19 = x_109;
x_20 = x_108;
goto block_89;
}
}
case 2:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_110 = lean_ctor_get(x_95, 0);
lean_inc(x_110);
lean_dec(x_95);
x_111 = l_Lake_LeanConfig_decodeToml___closed__20;
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_mk_array(x_113, x_112);
x_115 = l_Array_append___rarg(x_18, x_114);
lean_dec(x_114);
x_116 = 0;
x_19 = x_116;
x_20 = x_115;
goto block_89;
}
case 3:
{
uint8_t x_117; 
x_117 = lean_ctor_get_uint8(x_95, sizeof(void*)*1);
lean_dec(x_95);
x_19 = x_117;
x_20 = x_18;
goto block_89;
}
default: 
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_95);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_119 = lean_ctor_get(x_95, 1);
lean_dec(x_119);
x_120 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_95, 0);
lean_ctor_set(x_95, 1, x_120);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_mk_array(x_121, x_95);
x_123 = l_Array_append___rarg(x_18, x_122);
lean_dec(x_122);
x_124 = 0;
x_19 = x_124;
x_20 = x_123;
goto block_89;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_125 = lean_ctor_get(x_95, 0);
lean_inc(x_125);
lean_dec(x_95);
x_126 = l_Lake_LeanConfig_decodeToml___closed__20;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_mk_array(x_128, x_127);
x_130 = l_Array_append___rarg(x_18, x_129);
lean_dec(x_129);
x_131 = 0;
x_19 = x_131;
x_20 = x_130;
goto block_89;
}
}
}
}
block_89:
{
lean_object* x_21; lean_object* x_22; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_36 = l_Lake_LeanLibConfig_decodeToml___closed__3;
lean_inc(x_1);
x_37 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_35, x_36, x_1);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = l_Lake_LeanLibConfig_decodeToml___closed__6;
x_21 = x_38;
x_22 = x_20;
goto block_34;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
switch (lean_obj_tag(x_40)) {
case 0:
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_40, 1);
lean_dec(x_42);
x_43 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_40, 1, x_43);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_mk_array(x_44, x_40);
x_46 = l_Array_append___rarg(x_20, x_45);
lean_dec(x_45);
x_47 = l_Lake_LeanLibConfig_decodeToml___closed__6;
x_21 = x_47;
x_22 = x_46;
goto block_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
lean_dec(x_40);
x_49 = l_Lake_LeanConfig_decodeToml___closed__5;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_mk_array(x_51, x_50);
x_53 = l_Array_append___rarg(x_20, x_52);
lean_dec(x_52);
x_54 = l_Lake_LeanLibConfig_decodeToml___closed__6;
x_21 = x_54;
x_22 = x_53;
goto block_34;
}
}
case 2:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_40, 0);
lean_inc(x_55);
lean_dec(x_40);
x_56 = l_Lake_LeanConfig_decodeToml___closed__5;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_mk_array(x_58, x_57);
x_60 = l_Array_append___rarg(x_20, x_59);
lean_dec(x_59);
x_61 = l_Lake_LeanLibConfig_decodeToml___closed__6;
x_21 = x_61;
x_22 = x_60;
goto block_34;
}
case 3:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_40, 0);
lean_inc(x_62);
lean_dec(x_40);
x_63 = l_Lake_LeanConfig_decodeToml___closed__5;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_mk_array(x_65, x_64);
x_67 = l_Array_append___rarg(x_20, x_66);
lean_dec(x_66);
x_68 = l_Lake_LeanLibConfig_decodeToml___closed__6;
x_21 = x_68;
x_22 = x_67;
goto block_34;
}
case 5:
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_40, 1);
lean_inc(x_69);
lean_dec(x_40);
x_70 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(x_69);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = l_Array_append___rarg(x_20, x_71);
lean_dec(x_71);
x_73 = l_Lake_LeanLibConfig_decodeToml___closed__6;
x_21 = x_73;
x_22 = x_72;
goto block_34;
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_70, 0);
lean_inc(x_74);
lean_dec(x_70);
x_21 = x_74;
x_22 = x_20;
goto block_34;
}
}
default: 
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_40);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_40, 1);
lean_dec(x_76);
x_77 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_40, 0);
lean_ctor_set(x_40, 1, x_77);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_mk_array(x_78, x_40);
x_80 = l_Array_append___rarg(x_20, x_79);
lean_dec(x_79);
x_81 = l_Lake_LeanLibConfig_decodeToml___closed__6;
x_21 = x_81;
x_22 = x_80;
goto block_34;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_82 = lean_ctor_get(x_40, 0);
lean_inc(x_82);
lean_dec(x_40);
x_83 = l_Lake_LeanConfig_decodeToml___closed__5;
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_mk_array(x_85, x_84);
x_87 = l_Array_append___rarg(x_20, x_86);
lean_dec(x_86);
x_88 = l_Lake_LeanLibConfig_decodeToml___closed__6;
x_21 = x_88;
x_22 = x_87;
goto block_34;
}
}
}
}
block_34:
{
lean_object* x_23; 
x_23 = l_Lake_LeanConfig_decodeToml(x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l_Array_append___rarg(x_22, x_24);
lean_dec(x_24);
x_26 = l_Lake_PackageConfig_decodeToml___closed__7;
x_27 = l_Lake_LeanOption_decodeToml___closed__4;
x_28 = l_Lake_LeanLibConfig_decodeToml___closed__1;
x_29 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_9);
lean_ctor_set(x_29, 2, x_11);
lean_ctor_set(x_29, 3, x_13);
lean_ctor_set(x_29, 4, x_15);
lean_ctor_set(x_29, 5, x_17);
lean_ctor_set(x_29, 6, x_27);
lean_ctor_set(x_29, 7, x_21);
lean_ctor_set(x_29, 8, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*9, x_19);
x_3 = x_29;
x_4 = x_25;
goto block_8;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_23, 0);
lean_inc(x_30);
lean_dec(x_23);
x_31 = l_Lake_LeanOption_decodeToml___closed__4;
x_32 = l_Lake_LeanLibConfig_decodeToml___closed__1;
x_33 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_9);
lean_ctor_set(x_33, 2, x_11);
lean_ctor_set(x_33, 3, x_13);
lean_ctor_set(x_33, 4, x_15);
lean_ctor_set(x_33, 5, x_17);
lean_ctor_set(x_33, 6, x_31);
lean_ctor_set(x_33, 7, x_21);
lean_ctor_set(x_33, 8, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*9, x_19);
x_3 = x_33;
x_4 = x_22;
goto block_8;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__3(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_LeanLibConfig_decodeToml___lambda__1(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanLibConfig(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_LeanLibConfig_decodeToml(x_27, x_26);
return x_28;
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 1);
lean_dec(x_30);
x_31 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_array(x_32, x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_array(x_38, x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("supportInterpreter", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_decodeToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exeName", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_decodeToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("root", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_decodeToml___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_191; lean_object* x_192; 
x_191 = l_Lake_LeanOption_decodeToml___closed__11;
lean_inc(x_1);
x_192 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__1(x_1, x_191, x_2);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = l_Lake_LeanOption_decodeToml___closed__4;
x_195 = l_Array_append___rarg(x_194, x_193);
lean_dec(x_193);
x_196 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_196;
x_10 = x_195;
goto block_190;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_192, 0);
lean_inc(x_197);
lean_dec(x_192);
x_198 = l_Lake_LeanOption_decodeToml___closed__4;
x_9 = x_197;
x_10 = x_198;
goto block_190;
}
block_8:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
}
block_190:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_11 = l_Lake_stringToLegalOrSimpleName(x_9);
x_155 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_156 = l_Lake_PackageConfig_decodeToml___closed__35;
lean_inc(x_1);
x_157 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_155, x_156, x_1);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; 
x_158 = l_Lake_PackageConfig_decodeToml___closed__36;
x_12 = x_158;
x_13 = x_10;
goto block_154;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
switch (lean_obj_tag(x_160)) {
case 0:
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_12 = x_161;
x_13 = x_10;
goto block_154;
}
case 2:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l_Lake_Glob_decodeToml___closed__2;
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_mk_array(x_165, x_164);
x_167 = l_Array_append___rarg(x_10, x_166);
lean_dec(x_166);
x_168 = l_Lake_PackageConfig_decodeToml___closed__36;
x_12 = x_168;
x_13 = x_167;
goto block_154;
}
case 3:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_169 = lean_ctor_get(x_160, 0);
lean_inc(x_169);
lean_dec(x_160);
x_170 = l_Lake_Glob_decodeToml___closed__2;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_172 = lean_unsigned_to_nat(1u);
x_173 = lean_mk_array(x_172, x_171);
x_174 = l_Array_append___rarg(x_10, x_173);
lean_dec(x_173);
x_175 = l_Lake_PackageConfig_decodeToml___closed__36;
x_12 = x_175;
x_13 = x_174;
goto block_154;
}
default: 
{
uint8_t x_176; 
x_176 = !lean_is_exclusive(x_160);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_160, 1);
lean_dec(x_177);
x_178 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_160, 0);
lean_ctor_set(x_160, 1, x_178);
x_179 = lean_unsigned_to_nat(1u);
x_180 = lean_mk_array(x_179, x_160);
x_181 = l_Array_append___rarg(x_10, x_180);
lean_dec(x_180);
x_182 = l_Lake_PackageConfig_decodeToml___closed__36;
x_12 = x_182;
x_13 = x_181;
goto block_154;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_183 = lean_ctor_get(x_160, 0);
lean_inc(x_183);
lean_dec(x_160);
x_184 = l_Lake_Glob_decodeToml___closed__2;
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_mk_array(x_186, x_185);
x_188 = l_Array_append___rarg(x_10, x_187);
lean_dec(x_187);
x_189 = l_Lake_PackageConfig_decodeToml___closed__36;
x_12 = x_189;
x_13 = x_188;
goto block_154;
}
}
}
}
block_154:
{
lean_object* x_14; lean_object* x_15; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_110 = l_Lake_LeanExeConfig_decodeToml___closed__6;
lean_inc(x_1);
x_111 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_109, x_110, x_1);
if (lean_obj_tag(x_111) == 0)
{
lean_inc(x_11);
x_14 = x_11;
x_15 = x_13;
goto block_108;
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
switch (lean_obj_tag(x_113)) {
case 0:
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_ctor_get(x_113, 1);
x_117 = l_String_toName(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
lean_ctor_set(x_113, 1, x_118);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_mk_array(x_119, x_113);
x_121 = l_Array_append___rarg(x_13, x_120);
lean_dec(x_120);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_121;
goto block_108;
}
else
{
lean_free_object(x_113);
lean_dec(x_115);
x_14 = x_117;
x_15 = x_13;
goto block_108;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_113, 0);
x_123 = lean_ctor_get(x_113, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_113);
x_124 = l_String_toName(x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4;
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_mk_array(x_127, x_126);
x_129 = l_Array_append___rarg(x_13, x_128);
lean_dec(x_128);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_129;
goto block_108;
}
else
{
lean_dec(x_122);
x_14 = x_124;
x_15 = x_13;
goto block_108;
}
}
}
case 2:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_113, 0);
lean_inc(x_130);
lean_dec(x_113);
x_131 = l_Lake_Glob_decodeToml___closed__2;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_mk_array(x_133, x_132);
x_135 = l_Array_append___rarg(x_13, x_134);
lean_dec(x_134);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_135;
goto block_108;
}
case 3:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_136 = lean_ctor_get(x_113, 0);
lean_inc(x_136);
lean_dec(x_113);
x_137 = l_Lake_Glob_decodeToml___closed__2;
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_mk_array(x_139, x_138);
x_141 = l_Array_append___rarg(x_13, x_140);
lean_dec(x_140);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_141;
goto block_108;
}
default: 
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_113);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_113, 1);
lean_dec(x_143);
x_144 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_113, 0);
lean_ctor_set(x_113, 1, x_144);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_mk_array(x_145, x_113);
x_147 = l_Array_append___rarg(x_13, x_146);
lean_dec(x_146);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_147;
goto block_108;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = lean_ctor_get(x_113, 0);
lean_inc(x_148);
lean_dec(x_113);
x_149 = l_Lake_Glob_decodeToml___closed__2;
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_mk_array(x_151, x_150);
x_153 = l_Array_append___rarg(x_13, x_152);
lean_dec(x_152);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_153;
goto block_108;
}
}
}
}
block_108:
{
lean_object* x_16; lean_object* x_17; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_75 = l_Lake_PackageConfig_decodeToml___closed__5;
x_76 = 0;
lean_inc(x_11);
x_77 = l_Lean_Name_toStringWithSep(x_75, x_76, x_11);
x_78 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_79 = l_Lake_LeanExeConfig_decodeToml___closed__4;
lean_inc(x_1);
x_80 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_78, x_79, x_1);
if (lean_obj_tag(x_80) == 0)
{
x_16 = x_77;
x_17 = x_15;
goto block_74;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
switch (lean_obj_tag(x_82)) {
case 0:
{
lean_object* x_83; 
lean_dec(x_77);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_16 = x_83;
x_17 = x_15;
goto block_74;
}
case 2:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lake_Glob_decodeToml___closed__2;
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_unsigned_to_nat(1u);
x_88 = lean_mk_array(x_87, x_86);
x_89 = l_Array_append___rarg(x_15, x_88);
lean_dec(x_88);
x_16 = x_77;
x_17 = x_89;
goto block_74;
}
case 3:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_90 = lean_ctor_get(x_82, 0);
lean_inc(x_90);
lean_dec(x_82);
x_91 = l_Lake_Glob_decodeToml___closed__2;
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_mk_array(x_93, x_92);
x_95 = l_Array_append___rarg(x_15, x_94);
lean_dec(x_94);
x_16 = x_77;
x_17 = x_95;
goto block_74;
}
default: 
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_82);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_82, 1);
lean_dec(x_97);
x_98 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_82, 0);
lean_ctor_set(x_82, 1, x_98);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_mk_array(x_99, x_82);
x_101 = l_Array_append___rarg(x_15, x_100);
lean_dec(x_100);
x_16 = x_77;
x_17 = x_101;
goto block_74;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_ctor_get(x_82, 0);
lean_inc(x_102);
lean_dec(x_82);
x_103 = l_Lake_Glob_decodeToml___closed__2;
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_mk_array(x_105, x_104);
x_107 = l_Array_append___rarg(x_15, x_106);
lean_dec(x_106);
x_16 = x_77;
x_17 = x_107;
goto block_74;
}
}
}
}
block_74:
{
uint8_t x_18; lean_object* x_19; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_33 = l_Lake_LeanExeConfig_decodeToml___closed__2;
lean_inc(x_1);
x_34 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_32, x_33, x_1);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = 0;
x_18 = x_35;
x_19 = x_17;
goto block_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
switch (lean_obj_tag(x_37)) {
case 0:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_37, 1);
lean_dec(x_39);
x_40 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_37, 1, x_40);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_mk_array(x_41, x_37);
x_43 = l_Array_append___rarg(x_17, x_42);
lean_dec(x_42);
x_44 = 0;
x_18 = x_44;
x_19 = x_43;
goto block_31;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_37, 0);
lean_inc(x_45);
lean_dec(x_37);
x_46 = l_Lake_LeanConfig_decodeToml___closed__20;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_mk_array(x_48, x_47);
x_50 = l_Array_append___rarg(x_17, x_49);
lean_dec(x_49);
x_51 = 0;
x_18 = x_51;
x_19 = x_50;
goto block_31;
}
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_37, 0);
lean_inc(x_52);
lean_dec(x_37);
x_53 = l_Lake_LeanConfig_decodeToml___closed__20;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_mk_array(x_55, x_54);
x_57 = l_Array_append___rarg(x_17, x_56);
lean_dec(x_56);
x_58 = 0;
x_18 = x_58;
x_19 = x_57;
goto block_31;
}
case 3:
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_37, sizeof(void*)*1);
lean_dec(x_37);
x_18 = x_59;
x_19 = x_17;
goto block_31;
}
default: 
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_37);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_61 = lean_ctor_get(x_37, 1);
lean_dec(x_61);
x_62 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_37, 0);
lean_ctor_set(x_37, 1, x_62);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_mk_array(x_63, x_37);
x_65 = l_Array_append___rarg(x_17, x_64);
lean_dec(x_64);
x_66 = 0;
x_18 = x_66;
x_19 = x_65;
goto block_31;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_37, 0);
lean_inc(x_67);
lean_dec(x_37);
x_68 = l_Lake_LeanConfig_decodeToml___closed__20;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_mk_array(x_70, x_69);
x_72 = l_Array_append___rarg(x_17, x_71);
lean_dec(x_71);
x_73 = 0;
x_18 = x_73;
x_19 = x_72;
goto block_31;
}
}
}
}
block_31:
{
lean_object* x_20; 
x_20 = l_Lake_LeanConfig_decodeToml(x_1);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Array_append___rarg(x_19, x_21);
lean_dec(x_21);
x_23 = l_Lake_PackageConfig_decodeToml___closed__7;
x_24 = l_Lake_LeanOption_decodeToml___closed__4;
x_25 = l_Lake_LeanLibConfig_decodeToml___closed__1;
x_26 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_12);
lean_ctor_set(x_26, 3, x_14);
lean_ctor_set(x_26, 4, x_16);
lean_ctor_set(x_26, 5, x_24);
lean_ctor_set(x_26, 6, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*7, x_18);
x_3 = x_26;
x_4 = x_22;
goto block_8;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Lake_LeanOption_decodeToml___closed__4;
x_29 = l_Lake_LeanLibConfig_decodeToml___closed__1;
x_30 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_12);
lean_ctor_set(x_30, 3, x_14);
lean_ctor_set(x_30, 4, x_16);
lean_ctor_set(x_30, 5, x_28);
lean_ctor_set(x_30, 6, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*7, x_18);
x_3 = x_30;
x_4 = x_19;
goto block_8;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanExeConfig(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_LeanExeConfig_decodeToml(x_27, x_26);
return x_28;
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 1);
lean_dec(x_30);
x_31 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_array(x_32, x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_array(x_38, x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = l_Lake_Toml_ppKey(x_1);
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = lean_string_append(x_15, x_10);
lean_dec(x_10);
lean_ctor_set(x_6, 1, x_16);
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_21 = lean_ctor_get(x_6, 0);
x_22 = lean_ctor_get(x_6, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_6);
x_23 = l_Lake_Toml_ppKey(x_1);
x_24 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_string_append(x_27, x_22);
lean_dec(x_22);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_28);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_32 = lean_array_uset(x_8, x_3, x_29);
x_3 = x_31;
x_4 = x_32;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_11; lean_object* x_12; 
x_11 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
lean_inc(x_2);
x_12 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_11, x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = l_Lake_Toml_ppKey(x_2);
lean_dec(x_2);
x_14 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2;
x_15 = lean_string_append(x_14, x_13);
lean_dec(x_13);
x_16 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_mk_array(x_19, x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
switch (lean_obj_tag(x_24)) {
case 0:
{
lean_object* x_25; 
lean_dec(x_2);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
lean_ctor_set(x_12, 0, x_25);
return x_12;
}
case 2:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_12);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lake_Glob_decodeToml___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_mk_array(x_29, x_28);
x_4 = x_30;
goto block_10;
}
case 3:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_12);
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec(x_24);
x_32 = l_Lake_Glob_decodeToml___closed__2;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_mk_array(x_34, x_33);
x_4 = x_35;
goto block_10;
}
default: 
{
uint8_t x_36; 
lean_free_object(x_12);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_24, 1);
lean_dec(x_37);
x_38 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_24, 0);
lean_ctor_set(x_24, 1, x_38);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_mk_array(x_39, x_24);
x_4 = x_40;
goto block_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_24, 0);
lean_inc(x_41);
lean_dec(x_24);
x_42 = l_Lake_Glob_decodeToml___closed__2;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_mk_array(x_44, x_43);
x_4 = x_45;
goto block_10;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_12, 0);
lean_inc(x_46);
lean_dec(x_12);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
switch (lean_obj_tag(x_47)) {
case 0:
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_2);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
case 2:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
x_51 = l_Lake_Glob_decodeToml___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_mk_array(x_53, x_52);
x_4 = x_54;
goto block_10;
}
case 3:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = l_Lake_Glob_decodeToml___closed__2;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_mk_array(x_58, x_57);
x_4 = x_59;
goto block_10;
}
default: 
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_47, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_61 = x_47;
} else {
 lean_dec_ref(x_47);
 x_61 = lean_box(0);
}
x_62 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
 lean_ctor_set_tag(x_63, 0);
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_mk_array(x_64, x_63);
x_4 = x_65;
goto block_10;
}
}
}
}
block_10:
{
lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__2(x_2, x_6, x_7, x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DependencySrc_decodeToml___closed__6;
x_2 = l_Lake_Toml_ppKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2;
x_2 = l_Lake_DependencySrc_decodeToml___closed__7;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_DependencySrc_decodeToml___closed__8;
x_2 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__9;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lake_DependencySrc_decodeToml___closed__10;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DependencySrc_decodeToml___closed__11;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("path", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected one of 'path' or 'git'", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("url", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dir", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_136 = l_Lake_DependencySrc_decodeToml___closed__6;
lean_inc(x_1);
x_137 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_135, x_136, x_1);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
lean_dec(x_2);
lean_dec(x_1);
x_138 = l_Lake_DependencySrc_decodeToml___closed__12;
return x_138;
}
else
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_137, 0);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
switch (lean_obj_tag(x_141)) {
case 0:
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_ctor_get(x_141, 1);
x_145 = l_Lake_DependencySrc_decodeToml___closed__13;
x_146 = lean_string_dec_eq(x_144, x_145);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
x_147 = l_Lake_DependencySrc_decodeToml___closed__14;
x_148 = lean_string_dec_eq(x_144, x_147);
lean_dec(x_144);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_2);
lean_dec(x_1);
x_149 = l_Lake_DependencySrc_decodeToml___closed__15;
lean_ctor_set(x_141, 1, x_149);
x_150 = l_Lake_LeanOption_decodeToml___closed__2;
x_151 = lean_array_push(x_150, x_141);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_151);
return x_137;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_free_object(x_141);
lean_dec(x_143);
lean_free_object(x_137);
x_152 = l_Lake_DependencySrc_decodeToml___closed__17;
lean_inc(x_1);
x_153 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__1(x_1, x_152, x_2);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec(x_153);
x_155 = l_Lake_LeanOption_decodeToml___closed__4;
x_156 = l_Array_append___rarg(x_155, x_154);
lean_dec(x_154);
x_157 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_157;
x_10 = x_156;
goto block_134;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_158);
lean_dec(x_153);
x_159 = l_Lake_LeanOption_decodeToml___closed__4;
x_9 = x_158;
x_10 = x_159;
goto block_134;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_free_object(x_141);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_2);
x_160 = l_Lake_DependencySrc_decodeToml___closed__19;
x_161 = lean_box(0);
x_162 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_160, x_161);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; 
lean_free_object(x_137);
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
return x_162;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_164);
return x_165;
}
}
else
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_162);
if (x_166 == 0)
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_162, 0);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_167);
lean_ctor_set(x_162, 0, x_137);
return x_162;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_162, 0);
lean_inc(x_168);
lean_dec(x_162);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_168);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_137);
return x_169;
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_141, 0);
x_171 = lean_ctor_get(x_141, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_141);
x_172 = l_Lake_DependencySrc_decodeToml___closed__13;
x_173 = lean_string_dec_eq(x_171, x_172);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = l_Lake_DependencySrc_decodeToml___closed__14;
x_175 = lean_string_dec_eq(x_171, x_174);
lean_dec(x_171);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_2);
lean_dec(x_1);
x_176 = l_Lake_DependencySrc_decodeToml___closed__15;
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_170);
lean_ctor_set(x_177, 1, x_176);
x_178 = l_Lake_LeanOption_decodeToml___closed__2;
x_179 = lean_array_push(x_178, x_177);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_179);
return x_137;
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_170);
lean_free_object(x_137);
x_180 = l_Lake_DependencySrc_decodeToml___closed__17;
lean_inc(x_1);
x_181 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__1(x_1, x_180, x_2);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Lake_LeanOption_decodeToml___closed__4;
x_184 = l_Array_append___rarg(x_183, x_182);
lean_dec(x_182);
x_185 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_185;
x_10 = x_184;
goto block_134;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
lean_dec(x_181);
x_187 = l_Lake_LeanOption_decodeToml___closed__4;
x_9 = x_186;
x_10 = x_187;
goto block_134;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_2);
x_188 = l_Lake_DependencySrc_decodeToml___closed__19;
x_189 = lean_box(0);
x_190 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_188, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_free_object(x_137);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_192 = x_190;
} else {
 lean_dec_ref(x_190);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 1, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_191);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_190, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_195 = x_190;
} else {
 lean_dec_ref(x_190);
 x_195 = lean_box(0);
}
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_194);
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_137);
return x_196;
}
}
}
}
case 2:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_2);
lean_dec(x_1);
x_197 = lean_ctor_get(x_141, 0);
lean_inc(x_197);
lean_dec(x_141);
x_198 = l_Lake_Glob_decodeToml___closed__2;
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_unsigned_to_nat(1u);
x_201 = lean_mk_array(x_200, x_199);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_201);
return x_137;
}
case 3:
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_ctor_get(x_141, 0);
lean_inc(x_202);
lean_dec(x_141);
x_203 = l_Lake_Glob_decodeToml___closed__2;
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_unsigned_to_nat(1u);
x_206 = lean_mk_array(x_205, x_204);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_206);
return x_137;
}
default: 
{
uint8_t x_207; 
lean_dec(x_2);
lean_dec(x_1);
x_207 = !lean_is_exclusive(x_141);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_141, 1);
lean_dec(x_208);
x_209 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_141, 0);
lean_ctor_set(x_141, 1, x_209);
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_mk_array(x_210, x_141);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_211);
return x_137;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_212 = lean_ctor_get(x_141, 0);
lean_inc(x_212);
lean_dec(x_141);
x_213 = l_Lake_Glob_decodeToml___closed__2;
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_unsigned_to_nat(1u);
x_216 = lean_mk_array(x_215, x_214);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_216);
return x_137;
}
}
}
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_137, 0);
lean_inc(x_217);
lean_dec(x_137);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
switch (lean_obj_tag(x_218)) {
case 0:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; uint8_t x_223; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_222 = l_Lake_DependencySrc_decodeToml___closed__13;
x_223 = lean_string_dec_eq(x_220, x_222);
if (x_223 == 0)
{
lean_object* x_224; uint8_t x_225; 
x_224 = l_Lake_DependencySrc_decodeToml___closed__14;
x_225 = lean_string_dec_eq(x_220, x_224);
lean_dec(x_220);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_2);
lean_dec(x_1);
x_226 = l_Lake_DependencySrc_decodeToml___closed__15;
if (lean_is_scalar(x_221)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_221;
}
lean_ctor_set(x_227, 0, x_219);
lean_ctor_set(x_227, 1, x_226);
x_228 = l_Lake_LeanOption_decodeToml___closed__2;
x_229 = lean_array_push(x_228, x_227);
x_230 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_230, 0, x_229);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; 
lean_dec(x_221);
lean_dec(x_219);
x_231 = l_Lake_DependencySrc_decodeToml___closed__17;
lean_inc(x_1);
x_232 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__1(x_1, x_231, x_2);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec(x_232);
x_234 = l_Lake_LeanOption_decodeToml___closed__4;
x_235 = l_Array_append___rarg(x_234, x_233);
lean_dec(x_233);
x_236 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_236;
x_10 = x_235;
goto block_134;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_232, 0);
lean_inc(x_237);
lean_dec(x_232);
x_238 = l_Lake_LeanOption_decodeToml___closed__4;
x_9 = x_237;
x_10 = x_238;
goto block_134;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_2);
x_239 = l_Lake_DependencySrc_decodeToml___closed__19;
x_240 = lean_box(0);
x_241 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_239, x_240);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 x_243 = x_241;
} else {
 lean_dec_ref(x_241);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(0, 1, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_245 = lean_ctor_get(x_241, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 x_246 = x_241;
} else {
 lean_dec_ref(x_241);
 x_246 = lean_box(0);
}
x_247 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_247, 0, x_245);
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(1, 1, 0);
} else {
 x_248 = x_246;
}
lean_ctor_set(x_248, 0, x_247);
return x_248;
}
}
}
case 2:
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_ctor_get(x_218, 0);
lean_inc(x_249);
lean_dec(x_218);
x_250 = l_Lake_Glob_decodeToml___closed__2;
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_249);
lean_ctor_set(x_251, 1, x_250);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_mk_array(x_252, x_251);
x_254 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_254, 0, x_253);
return x_254;
}
case 3:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_2);
lean_dec(x_1);
x_255 = lean_ctor_get(x_218, 0);
lean_inc(x_255);
lean_dec(x_218);
x_256 = l_Lake_Glob_decodeToml___closed__2;
x_257 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_unsigned_to_nat(1u);
x_259 = lean_mk_array(x_258, x_257);
x_260 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_260, 0, x_259);
return x_260;
}
default: 
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_ctor_get(x_218, 0);
lean_inc(x_261);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_262 = x_218;
} else {
 lean_dec_ref(x_218);
 x_262 = lean_box(0);
}
x_263 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_262)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_262;
 lean_ctor_set_tag(x_264, 0);
}
lean_ctor_set(x_264, 0, x_261);
lean_ctor_set(x_264, 1, x_263);
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_mk_array(x_265, x_264);
x_267 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_267, 0, x_266);
return x_267;
}
}
}
}
block_8:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
}
block_134:
{
lean_object* x_11; lean_object* x_12; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_80 = l_Lake_DependencySrc_decodeToml___closed__4;
lean_inc(x_1);
x_81 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_79, x_80, x_1);
x_82 = lean_box(0);
if (lean_obj_tag(x_81) == 0)
{
x_11 = x_82;
x_12 = x_10;
goto block_78;
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_81);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_81, 0);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
switch (lean_obj_tag(x_85)) {
case 0:
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
lean_ctor_set(x_81, 0, x_86);
x_11 = x_81;
x_12 = x_10;
goto block_78;
}
case 2:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_81);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lake_Glob_decodeToml___closed__2;
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_mk_array(x_90, x_89);
x_92 = l_Array_append___rarg(x_10, x_91);
lean_dec(x_91);
x_11 = x_82;
x_12 = x_92;
goto block_78;
}
case 3:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_free_object(x_81);
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
lean_dec(x_85);
x_94 = l_Lake_Glob_decodeToml___closed__2;
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_mk_array(x_96, x_95);
x_98 = l_Array_append___rarg(x_10, x_97);
lean_dec(x_97);
x_11 = x_82;
x_12 = x_98;
goto block_78;
}
default: 
{
uint8_t x_99; 
lean_free_object(x_81);
x_99 = !lean_is_exclusive(x_85);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_85, 1);
lean_dec(x_100);
x_101 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_85, 0);
lean_ctor_set(x_85, 1, x_101);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_mk_array(x_102, x_85);
x_104 = l_Array_append___rarg(x_10, x_103);
lean_dec(x_103);
x_11 = x_82;
x_12 = x_104;
goto block_78;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_85, 0);
lean_inc(x_105);
lean_dec(x_85);
x_106 = l_Lake_Glob_decodeToml___closed__2;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_mk_array(x_108, x_107);
x_110 = l_Array_append___rarg(x_10, x_109);
lean_dec(x_109);
x_11 = x_82;
x_12 = x_110;
goto block_78;
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_81, 0);
lean_inc(x_111);
lean_dec(x_81);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
switch (lean_obj_tag(x_112)) {
case 0:
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_11 = x_114;
x_12 = x_10;
goto block_78;
}
case 2:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
lean_dec(x_112);
x_116 = l_Lake_Glob_decodeToml___closed__2;
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_mk_array(x_118, x_117);
x_120 = l_Array_append___rarg(x_10, x_119);
lean_dec(x_119);
x_11 = x_82;
x_12 = x_120;
goto block_78;
}
case 3:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_121 = lean_ctor_get(x_112, 0);
lean_inc(x_121);
lean_dec(x_112);
x_122 = l_Lake_Glob_decodeToml___closed__2;
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_unsigned_to_nat(1u);
x_125 = lean_mk_array(x_124, x_123);
x_126 = l_Array_append___rarg(x_10, x_125);
lean_dec(x_125);
x_11 = x_82;
x_12 = x_126;
goto block_78;
}
default: 
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = lean_ctor_get(x_112, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_128 = x_112;
} else {
 lean_dec_ref(x_112);
 x_128 = lean_box(0);
}
x_129 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
 lean_ctor_set_tag(x_130, 0);
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_mk_array(x_131, x_130);
x_133 = l_Array_append___rarg(x_10, x_132);
lean_dec(x_132);
x_11 = x_82;
x_12 = x_133;
goto block_78;
}
}
}
}
block_78:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_14 = l_Lake_DependencySrc_decodeToml___closed__2;
x_15 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_13, x_14, x_1);
x_16 = lean_box(0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_3 = x_17;
x_4 = x_12;
goto block_8;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_15, 0, x_21);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_15);
x_3 = x_22;
x_4 = x_12;
goto block_8;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_15);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lake_Glob_decodeToml___closed__2;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_mk_array(x_26, x_25);
x_28 = l_Array_append___rarg(x_12, x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_16);
x_3 = x_29;
x_4 = x_28;
goto block_8;
}
case 3:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_15);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lake_Glob_decodeToml___closed__2;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_mk_array(x_33, x_32);
x_35 = l_Array_append___rarg(x_12, x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_9);
lean_ctor_set(x_36, 1, x_11);
lean_ctor_set(x_36, 2, x_16);
x_3 = x_36;
x_4 = x_35;
goto block_8;
}
default: 
{
uint8_t x_37; 
lean_free_object(x_15);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_20, 1);
lean_dec(x_38);
x_39 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 1, x_39);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_mk_array(x_40, x_20);
x_42 = l_Array_append___rarg(x_12, x_41);
lean_dec(x_41);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_9);
lean_ctor_set(x_43, 1, x_11);
lean_ctor_set(x_43, 2, x_16);
x_3 = x_43;
x_4 = x_42;
goto block_8;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_20, 0);
lean_inc(x_44);
lean_dec(x_20);
x_45 = l_Lake_Glob_decodeToml___closed__2;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_mk_array(x_47, x_46);
x_49 = l_Array_append___rarg(x_12, x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_50, 0, x_9);
lean_ctor_set(x_50, 1, x_11);
lean_ctor_set(x_50, 2, x_16);
x_3 = x_50;
x_4 = x_49;
goto block_8;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_15, 0);
lean_inc(x_51);
lean_dec(x_15);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
switch (lean_obj_tag(x_52)) {
case 0:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_55, 0, x_9);
lean_ctor_set(x_55, 1, x_11);
lean_ctor_set(x_55, 2, x_54);
x_3 = x_55;
x_4 = x_12;
goto block_8;
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = l_Lake_Glob_decodeToml___closed__2;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_mk_array(x_59, x_58);
x_61 = l_Array_append___rarg(x_12, x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_62, 0, x_9);
lean_ctor_set(x_62, 1, x_11);
lean_ctor_set(x_62, 2, x_16);
x_3 = x_62;
x_4 = x_61;
goto block_8;
}
case 3:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
lean_dec(x_52);
x_64 = l_Lake_Glob_decodeToml___closed__2;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_mk_array(x_66, x_65);
x_68 = l_Array_append___rarg(x_12, x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_9);
lean_ctor_set(x_69, 1, x_11);
lean_ctor_set(x_69, 2, x_16);
x_3 = x_69;
x_4 = x_68;
goto block_8;
}
default: 
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_52, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_71 = x_52;
} else {
 lean_dec_ref(x_52);
 x_71 = lean_box(0);
}
x_72 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
 lean_ctor_set_tag(x_73, 0);
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_mk_array(x_74, x_73);
x_76 = l_Array_append___rarg(x_12, x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_9);
lean_ctor_set(x_77, 1, x_11);
lean_ctor_set(x_77, 2, x_16);
x_3 = x_77;
x_4 = x_76;
goto block_8;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependencySrc(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_DependencySrc_decodeToml(x_27, x_26);
return x_28;
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 1);
lean_dec(x_30);
x_31 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_array(x_32, x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_array(x_38, x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___lambda__1), 3, 1);
lean_closure_set(x_12, 0, x_10);
switch (lean_obj_tag(x_11)) {
case 0:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_free_object(x_6);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lake_mergeErrors___rarg(x_4, x_14, x_12);
x_2 = x_8;
x_4 = x_15;
goto _start;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set(x_6, 1, x_18);
lean_ctor_set(x_6, 0, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_mk_array(x_19, x_6);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lake_mergeErrors___rarg(x_4, x_21, x_12);
x_2 = x_8;
x_4 = x_22;
goto _start;
}
case 3:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_6, 0, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_mk_array(x_26, x_6);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = l_Lake_mergeErrors___rarg(x_4, x_28, x_12);
x_2 = x_8;
x_4 = x_29;
goto _start;
}
default: 
{
uint8_t x_31; 
lean_free_object(x_6);
x_31 = !lean_is_exclusive(x_11);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_11, 1);
lean_dec(x_32);
x_33 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_11, 0);
lean_ctor_set(x_11, 1, x_33);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_mk_array(x_34, x_11);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = l_Lake_mergeErrors___rarg(x_4, x_36, x_12);
x_2 = x_8;
x_4 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
lean_dec(x_11);
x_40 = l_Lake_Glob_decodeToml___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_mk_array(x_42, x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = l_Lake_mergeErrors___rarg(x_4, x_44, x_12);
x_2 = x_8;
x_4 = x_45;
goto _start;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_6, 0);
x_48 = lean_ctor_get(x_6, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_6);
x_49 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___lambda__1), 3, 1);
lean_closure_set(x_49, 0, x_47);
switch (lean_obj_tag(x_48)) {
case 0:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = l_Lake_mergeErrors___rarg(x_4, x_51, x_49);
x_2 = x_8;
x_4 = x_52;
goto _start;
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_48, 0);
lean_inc(x_54);
lean_dec(x_48);
x_55 = l_Lake_Glob_decodeToml___closed__2;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_mk_array(x_57, x_56);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = l_Lake_mergeErrors___rarg(x_4, x_59, x_49);
x_2 = x_8;
x_4 = x_60;
goto _start;
}
case 3:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_48, 0);
lean_inc(x_62);
lean_dec(x_48);
x_63 = l_Lake_Glob_decodeToml___closed__2;
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_mk_array(x_65, x_64);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lake_mergeErrors___rarg(x_4, x_67, x_49);
x_2 = x_8;
x_4 = x_68;
goto _start;
}
default: 
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_70 = lean_ctor_get(x_48, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_71 = x_48;
} else {
 lean_dec_ref(x_48);
 x_71 = lean_box(0);
}
x_72 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
 lean_ctor_set_tag(x_73, 0);
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_mk_array(x_74, x_73);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lake_mergeErrors___rarg(x_4, x_76, x_49);
x_2 = x_8;
x_4 = x_77;
goto _start;
}
}
}
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_3, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1;
return x_8;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = 0;
x_10 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_11 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1;
x_12 = l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2(x_2, x_9, x_10, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("options", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_decodeToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git#", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("version", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_decodeToml___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scope", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_decodeToml___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("source", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_decodeToml___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected string or table", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_906; lean_object* x_907; 
x_906 = l_Lake_LeanOption_decodeToml___closed__11;
lean_inc(x_1);
x_907 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__1(x_1, x_906, x_2);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
lean_dec(x_907);
x_909 = l_Lake_LeanOption_decodeToml___closed__4;
x_910 = l_Array_append___rarg(x_909, x_908);
lean_dec(x_908);
x_911 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_911;
x_10 = x_910;
goto block_905;
}
else
{
lean_object* x_912; lean_object* x_913; 
x_912 = lean_ctor_get(x_907, 0);
lean_inc(x_912);
lean_dec(x_907);
x_913 = l_Lake_LeanOption_decodeToml___closed__4;
x_9 = x_912;
x_10 = x_913;
goto block_905;
}
block_8:
{
uint8_t x_5; 
x_5 = l_Array_isEmpty___rarg(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
}
block_905:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_11 = l_Lake_stringToLegalOrSimpleName(x_9);
x_850 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_851 = l_Lake_DependencySrc_decodeToml___closed__4;
lean_inc(x_1);
x_852 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_850, x_851, x_1);
x_853 = lean_box(0);
if (lean_obj_tag(x_852) == 0)
{
x_12 = x_853;
x_13 = x_10;
goto block_849;
}
else
{
uint8_t x_854; 
x_854 = !lean_is_exclusive(x_852);
if (x_854 == 0)
{
lean_object* x_855; lean_object* x_856; 
x_855 = lean_ctor_get(x_852, 0);
x_856 = lean_ctor_get(x_855, 1);
lean_inc(x_856);
lean_dec(x_855);
switch (lean_obj_tag(x_856)) {
case 0:
{
lean_object* x_857; 
x_857 = lean_ctor_get(x_856, 1);
lean_inc(x_857);
lean_dec(x_856);
lean_ctor_set(x_852, 0, x_857);
x_12 = x_852;
x_13 = x_10;
goto block_849;
}
case 2:
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_free_object(x_852);
x_858 = lean_ctor_get(x_856, 0);
lean_inc(x_858);
lean_dec(x_856);
x_859 = l_Lake_Glob_decodeToml___closed__2;
x_860 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_860, 0, x_858);
lean_ctor_set(x_860, 1, x_859);
x_861 = lean_unsigned_to_nat(1u);
x_862 = lean_mk_array(x_861, x_860);
x_863 = l_Array_append___rarg(x_10, x_862);
lean_dec(x_862);
x_12 = x_853;
x_13 = x_863;
goto block_849;
}
case 3:
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_free_object(x_852);
x_864 = lean_ctor_get(x_856, 0);
lean_inc(x_864);
lean_dec(x_856);
x_865 = l_Lake_Glob_decodeToml___closed__2;
x_866 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_866, 0, x_864);
lean_ctor_set(x_866, 1, x_865);
x_867 = lean_unsigned_to_nat(1u);
x_868 = lean_mk_array(x_867, x_866);
x_869 = l_Array_append___rarg(x_10, x_868);
lean_dec(x_868);
x_12 = x_853;
x_13 = x_869;
goto block_849;
}
default: 
{
uint8_t x_870; 
lean_free_object(x_852);
x_870 = !lean_is_exclusive(x_856);
if (x_870 == 0)
{
lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_871 = lean_ctor_get(x_856, 1);
lean_dec(x_871);
x_872 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_856, 0);
lean_ctor_set(x_856, 1, x_872);
x_873 = lean_unsigned_to_nat(1u);
x_874 = lean_mk_array(x_873, x_856);
x_875 = l_Array_append___rarg(x_10, x_874);
lean_dec(x_874);
x_12 = x_853;
x_13 = x_875;
goto block_849;
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; 
x_876 = lean_ctor_get(x_856, 0);
lean_inc(x_876);
lean_dec(x_856);
x_877 = l_Lake_Glob_decodeToml___closed__2;
x_878 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_878, 0, x_876);
lean_ctor_set(x_878, 1, x_877);
x_879 = lean_unsigned_to_nat(1u);
x_880 = lean_mk_array(x_879, x_878);
x_881 = l_Array_append___rarg(x_10, x_880);
lean_dec(x_880);
x_12 = x_853;
x_13 = x_881;
goto block_849;
}
}
}
}
else
{
lean_object* x_882; lean_object* x_883; 
x_882 = lean_ctor_get(x_852, 0);
lean_inc(x_882);
lean_dec(x_852);
x_883 = lean_ctor_get(x_882, 1);
lean_inc(x_883);
lean_dec(x_882);
switch (lean_obj_tag(x_883)) {
case 0:
{
lean_object* x_884; lean_object* x_885; 
x_884 = lean_ctor_get(x_883, 1);
lean_inc(x_884);
lean_dec(x_883);
x_885 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_885, 0, x_884);
x_12 = x_885;
x_13 = x_10;
goto block_849;
}
case 2:
{
lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_886 = lean_ctor_get(x_883, 0);
lean_inc(x_886);
lean_dec(x_883);
x_887 = l_Lake_Glob_decodeToml___closed__2;
x_888 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_888, 0, x_886);
lean_ctor_set(x_888, 1, x_887);
x_889 = lean_unsigned_to_nat(1u);
x_890 = lean_mk_array(x_889, x_888);
x_891 = l_Array_append___rarg(x_10, x_890);
lean_dec(x_890);
x_12 = x_853;
x_13 = x_891;
goto block_849;
}
case 3:
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_892 = lean_ctor_get(x_883, 0);
lean_inc(x_892);
lean_dec(x_883);
x_893 = l_Lake_Glob_decodeToml___closed__2;
x_894 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_894, 0, x_892);
lean_ctor_set(x_894, 1, x_893);
x_895 = lean_unsigned_to_nat(1u);
x_896 = lean_mk_array(x_895, x_894);
x_897 = l_Array_append___rarg(x_10, x_896);
lean_dec(x_896);
x_12 = x_853;
x_13 = x_897;
goto block_849;
}
default: 
{
lean_object* x_898; lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_898 = lean_ctor_get(x_883, 0);
lean_inc(x_898);
if (lean_is_exclusive(x_883)) {
 lean_ctor_release(x_883, 0);
 lean_ctor_release(x_883, 1);
 x_899 = x_883;
} else {
 lean_dec_ref(x_883);
 x_899 = lean_box(0);
}
x_900 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_899)) {
 x_901 = lean_alloc_ctor(0, 2, 0);
} else {
 x_901 = x_899;
 lean_ctor_set_tag(x_901, 0);
}
lean_ctor_set(x_901, 0, x_898);
lean_ctor_set(x_901, 1, x_900);
x_902 = lean_unsigned_to_nat(1u);
x_903 = lean_mk_array(x_902, x_901);
x_904 = l_Array_append___rarg(x_10, x_903);
lean_dec(x_903);
x_12 = x_853;
x_13 = x_904;
goto block_849;
}
}
}
}
block_849:
{
lean_object* x_14; lean_object* x_15; lean_object* x_189; lean_object* x_190; lean_object* x_514; lean_object* x_515; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_794 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_795 = l_Lake_Dependency_decodeToml___closed__12;
lean_inc(x_1);
x_796 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_794, x_795, x_1);
x_797 = lean_box(0);
if (lean_obj_tag(x_796) == 0)
{
x_514 = x_797;
x_515 = x_13;
goto block_793;
}
else
{
uint8_t x_798; 
x_798 = !lean_is_exclusive(x_796);
if (x_798 == 0)
{
lean_object* x_799; lean_object* x_800; 
x_799 = lean_ctor_get(x_796, 0);
x_800 = lean_ctor_get(x_799, 1);
lean_inc(x_800);
lean_dec(x_799);
switch (lean_obj_tag(x_800)) {
case 0:
{
lean_object* x_801; 
x_801 = lean_ctor_get(x_800, 1);
lean_inc(x_801);
lean_dec(x_800);
lean_ctor_set(x_796, 0, x_801);
x_514 = x_796;
x_515 = x_13;
goto block_793;
}
case 2:
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_free_object(x_796);
x_802 = lean_ctor_get(x_800, 0);
lean_inc(x_802);
lean_dec(x_800);
x_803 = l_Lake_Glob_decodeToml___closed__2;
x_804 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
x_805 = lean_unsigned_to_nat(1u);
x_806 = lean_mk_array(x_805, x_804);
x_807 = l_Array_append___rarg(x_13, x_806);
lean_dec(x_806);
x_514 = x_797;
x_515 = x_807;
goto block_793;
}
case 3:
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; lean_object* x_813; 
lean_free_object(x_796);
x_808 = lean_ctor_get(x_800, 0);
lean_inc(x_808);
lean_dec(x_800);
x_809 = l_Lake_Glob_decodeToml___closed__2;
x_810 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_810, 0, x_808);
lean_ctor_set(x_810, 1, x_809);
x_811 = lean_unsigned_to_nat(1u);
x_812 = lean_mk_array(x_811, x_810);
x_813 = l_Array_append___rarg(x_13, x_812);
lean_dec(x_812);
x_514 = x_797;
x_515 = x_813;
goto block_793;
}
default: 
{
uint8_t x_814; 
lean_free_object(x_796);
x_814 = !lean_is_exclusive(x_800);
if (x_814 == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_800, 1);
lean_dec(x_815);
x_816 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_800, 0);
lean_ctor_set(x_800, 1, x_816);
x_817 = lean_unsigned_to_nat(1u);
x_818 = lean_mk_array(x_817, x_800);
x_819 = l_Array_append___rarg(x_13, x_818);
lean_dec(x_818);
x_514 = x_797;
x_515 = x_819;
goto block_793;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_820 = lean_ctor_get(x_800, 0);
lean_inc(x_820);
lean_dec(x_800);
x_821 = l_Lake_Glob_decodeToml___closed__2;
x_822 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_821);
x_823 = lean_unsigned_to_nat(1u);
x_824 = lean_mk_array(x_823, x_822);
x_825 = l_Array_append___rarg(x_13, x_824);
lean_dec(x_824);
x_514 = x_797;
x_515 = x_825;
goto block_793;
}
}
}
}
else
{
lean_object* x_826; lean_object* x_827; 
x_826 = lean_ctor_get(x_796, 0);
lean_inc(x_826);
lean_dec(x_796);
x_827 = lean_ctor_get(x_826, 1);
lean_inc(x_827);
lean_dec(x_826);
switch (lean_obj_tag(x_827)) {
case 0:
{
lean_object* x_828; lean_object* x_829; 
x_828 = lean_ctor_get(x_827, 1);
lean_inc(x_828);
lean_dec(x_827);
x_829 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_829, 0, x_828);
x_514 = x_829;
x_515 = x_13;
goto block_793;
}
case 2:
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; 
x_830 = lean_ctor_get(x_827, 0);
lean_inc(x_830);
lean_dec(x_827);
x_831 = l_Lake_Glob_decodeToml___closed__2;
x_832 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_832, 0, x_830);
lean_ctor_set(x_832, 1, x_831);
x_833 = lean_unsigned_to_nat(1u);
x_834 = lean_mk_array(x_833, x_832);
x_835 = l_Array_append___rarg(x_13, x_834);
lean_dec(x_834);
x_514 = x_797;
x_515 = x_835;
goto block_793;
}
case 3:
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_836 = lean_ctor_get(x_827, 0);
lean_inc(x_836);
lean_dec(x_827);
x_837 = l_Lake_Glob_decodeToml___closed__2;
x_838 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_838, 0, x_836);
lean_ctor_set(x_838, 1, x_837);
x_839 = lean_unsigned_to_nat(1u);
x_840 = lean_mk_array(x_839, x_838);
x_841 = l_Array_append___rarg(x_13, x_840);
lean_dec(x_840);
x_514 = x_797;
x_515 = x_841;
goto block_793;
}
default: 
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_842 = lean_ctor_get(x_827, 0);
lean_inc(x_842);
if (lean_is_exclusive(x_827)) {
 lean_ctor_release(x_827, 0);
 lean_ctor_release(x_827, 1);
 x_843 = x_827;
} else {
 lean_dec_ref(x_827);
 x_843 = lean_box(0);
}
x_844 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_843)) {
 x_845 = lean_alloc_ctor(0, 2, 0);
} else {
 x_845 = x_843;
 lean_ctor_set_tag(x_845, 0);
}
lean_ctor_set(x_845, 0, x_842);
lean_ctor_set(x_845, 1, x_844);
x_846 = lean_unsigned_to_nat(1u);
x_847 = lean_mk_array(x_846, x_845);
x_848 = l_Array_append___rarg(x_13, x_847);
lean_dec(x_847);
x_514 = x_797;
x_515 = x_848;
goto block_793;
}
}
}
}
block_188:
{
lean_object* x_16; lean_object* x_17; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_154 = l_Lake_Dependency_decodeToml___closed__7;
lean_inc(x_1);
x_155 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_153, x_154, x_1);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; 
x_156 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_16 = x_156;
x_17 = x_15;
goto block_152;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
switch (lean_obj_tag(x_158)) {
case 0:
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_16 = x_159;
x_17 = x_15;
goto block_152;
}
case 2:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lake_Glob_decodeToml___closed__2;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_unsigned_to_nat(1u);
x_164 = lean_mk_array(x_163, x_162);
x_165 = l_Array_append___rarg(x_15, x_164);
lean_dec(x_164);
x_166 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_16 = x_166;
x_17 = x_165;
goto block_152;
}
case 3:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_158, 0);
lean_inc(x_167);
lean_dec(x_158);
x_168 = l_Lake_Glob_decodeToml___closed__2;
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_unsigned_to_nat(1u);
x_171 = lean_mk_array(x_170, x_169);
x_172 = l_Array_append___rarg(x_15, x_171);
lean_dec(x_171);
x_173 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_16 = x_173;
x_17 = x_172;
goto block_152;
}
default: 
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_158);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_158, 1);
lean_dec(x_175);
x_176 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_158, 0);
lean_ctor_set(x_158, 1, x_176);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_mk_array(x_177, x_158);
x_179 = l_Array_append___rarg(x_15, x_178);
lean_dec(x_178);
x_180 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_16 = x_180;
x_17 = x_179;
goto block_152;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get(x_158, 0);
lean_inc(x_181);
lean_dec(x_158);
x_182 = l_Lake_Glob_decodeToml___closed__2;
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_unsigned_to_nat(1u);
x_185 = lean_mk_array(x_184, x_183);
x_186 = l_Array_append___rarg(x_15, x_185);
lean_dec(x_185);
x_187 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_16 = x_187;
x_17 = x_186;
goto block_152;
}
}
}
}
block_152:
{
lean_object* x_18; lean_object* x_19; lean_object* x_77; lean_object* x_78; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_98 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_99 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_97, x_98, x_1);
x_100 = lean_box(0);
if (lean_obj_tag(x_99) == 0)
{
x_77 = x_100;
x_78 = x_17;
goto block_96;
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 0);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
switch (lean_obj_tag(x_103)) {
case 0:
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
lean_ctor_set(x_99, 0, x_104);
x_77 = x_99;
x_78 = x_17;
goto block_96;
}
case 2:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_free_object(x_99);
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Lake_Glob_decodeToml___closed__2;
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_mk_array(x_108, x_107);
x_110 = l_Array_append___rarg(x_17, x_109);
lean_dec(x_109);
x_77 = x_100;
x_78 = x_110;
goto block_96;
}
case 3:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_free_object(x_99);
x_111 = lean_ctor_get(x_103, 0);
lean_inc(x_111);
lean_dec(x_103);
x_112 = l_Lake_Glob_decodeToml___closed__2;
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_mk_array(x_114, x_113);
x_116 = l_Array_append___rarg(x_17, x_115);
lean_dec(x_115);
x_77 = x_100;
x_78 = x_116;
goto block_96;
}
default: 
{
uint8_t x_117; 
lean_free_object(x_99);
x_117 = !lean_is_exclusive(x_103);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_118 = lean_ctor_get(x_103, 1);
lean_dec(x_118);
x_119 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_103, 0);
lean_ctor_set(x_103, 1, x_119);
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_mk_array(x_120, x_103);
x_122 = l_Array_append___rarg(x_17, x_121);
lean_dec(x_121);
x_77 = x_100;
x_78 = x_122;
goto block_96;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_ctor_get(x_103, 0);
lean_inc(x_123);
lean_dec(x_103);
x_124 = l_Lake_Glob_decodeToml___closed__2;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_mk_array(x_126, x_125);
x_128 = l_Array_append___rarg(x_17, x_127);
lean_dec(x_127);
x_77 = x_100;
x_78 = x_128;
goto block_96;
}
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_99, 0);
lean_inc(x_129);
lean_dec(x_99);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
switch (lean_obj_tag(x_130)) {
case 0:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_77 = x_132;
x_78 = x_17;
goto block_96;
}
case 2:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
lean_dec(x_130);
x_134 = l_Lake_Glob_decodeToml___closed__2;
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_mk_array(x_136, x_135);
x_138 = l_Array_append___rarg(x_17, x_137);
lean_dec(x_137);
x_77 = x_100;
x_78 = x_138;
goto block_96;
}
case 3:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_139 = lean_ctor_get(x_130, 0);
lean_inc(x_139);
lean_dec(x_130);
x_140 = l_Lake_Glob_decodeToml___closed__2;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_unsigned_to_nat(1u);
x_143 = lean_mk_array(x_142, x_141);
x_144 = l_Array_append___rarg(x_17, x_143);
lean_dec(x_143);
x_77 = x_100;
x_78 = x_144;
goto block_96;
}
default: 
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_130, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_146 = x_130;
} else {
 lean_dec_ref(x_130);
 x_146 = lean_box(0);
}
x_147 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_146)) {
 x_148 = lean_alloc_ctor(0, 2, 0);
} else {
 x_148 = x_146;
 lean_ctor_set_tag(x_148, 0);
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_mk_array(x_149, x_148);
x_151 = l_Array_append___rarg(x_17, x_150);
lean_dec(x_150);
x_77 = x_100;
x_78 = x_151;
goto block_96;
}
}
}
}
block_76:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_box(0);
x_21 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_22 = l_Lake_Dependency_decodeToml___closed__2;
x_23 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_21, x_22, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_18);
lean_ctor_set(x_24, 3, x_14);
lean_ctor_set(x_24, 4, x_20);
x_3 = x_24;
x_4 = x_19;
goto block_8;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
switch (lean_obj_tag(x_26)) {
case 0:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_26, 1);
lean_dec(x_28);
x_29 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_26, 1, x_29);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_mk_array(x_30, x_26);
x_32 = l_Array_append___rarg(x_19, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_16);
lean_ctor_set(x_33, 2, x_18);
lean_ctor_set(x_33, 3, x_14);
lean_ctor_set(x_33, 4, x_20);
x_3 = x_33;
x_4 = x_32;
goto block_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_mk_array(x_37, x_36);
x_39 = l_Array_append___rarg(x_19, x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_40, 0, x_11);
lean_ctor_set(x_40, 1, x_16);
lean_ctor_set(x_40, 2, x_18);
lean_ctor_set(x_40, 3, x_14);
lean_ctor_set(x_40, 4, x_20);
x_3 = x_40;
x_4 = x_39;
goto block_8;
}
}
case 2:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
lean_dec(x_26);
x_42 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_mk_array(x_44, x_43);
x_46 = l_Array_append___rarg(x_19, x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_16);
lean_ctor_set(x_47, 2, x_18);
lean_ctor_set(x_47, 3, x_14);
lean_ctor_set(x_47, 4, x_20);
x_3 = x_47;
x_4 = x_46;
goto block_8;
}
case 3:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_26, 0);
lean_inc(x_48);
lean_dec(x_26);
x_49 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_mk_array(x_51, x_50);
x_53 = l_Array_append___rarg(x_19, x_52);
lean_dec(x_52);
x_54 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_54, 0, x_11);
lean_ctor_set(x_54, 1, x_16);
lean_ctor_set(x_54, 2, x_18);
lean_ctor_set(x_54, 3, x_14);
lean_ctor_set(x_54, 4, x_20);
x_3 = x_54;
x_4 = x_53;
goto block_8;
}
case 6:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_dec(x_26);
x_56 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Array_append___rarg(x_19, x_57);
lean_dec(x_57);
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_11);
lean_ctor_set(x_59, 1, x_16);
lean_ctor_set(x_59, 2, x_18);
lean_ctor_set(x_59, 3, x_14);
lean_ctor_set(x_59, 4, x_20);
x_3 = x_59;
x_4 = x_58;
goto block_8;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
lean_dec(x_56);
x_61 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_61, 0, x_11);
lean_ctor_set(x_61, 1, x_16);
lean_ctor_set(x_61, 2, x_18);
lean_ctor_set(x_61, 3, x_14);
lean_ctor_set(x_61, 4, x_60);
x_3 = x_61;
x_4 = x_19;
goto block_8;
}
}
default: 
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_26);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_26, 1);
lean_dec(x_63);
x_64 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_26, 0);
lean_ctor_set(x_26, 1, x_64);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_mk_array(x_65, x_26);
x_67 = l_Array_append___rarg(x_19, x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_68, 0, x_11);
lean_ctor_set(x_68, 1, x_16);
lean_ctor_set(x_68, 2, x_18);
lean_ctor_set(x_68, 3, x_14);
lean_ctor_set(x_68, 4, x_20);
x_3 = x_68;
x_4 = x_67;
goto block_8;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_26, 0);
lean_inc(x_69);
lean_dec(x_26);
x_70 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_mk_array(x_72, x_71);
x_74 = l_Array_append___rarg(x_19, x_73);
lean_dec(x_73);
x_75 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_75, 0, x_11);
lean_ctor_set(x_75, 1, x_16);
lean_ctor_set(x_75, 2, x_18);
lean_ctor_set(x_75, 3, x_14);
lean_ctor_set(x_75, 4, x_20);
x_3 = x_75;
x_4 = x_74;
goto block_8;
}
}
}
}
}
block_96:
{
if (lean_obj_tag(x_77) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_79; 
x_79 = lean_box(0);
x_18 = x_79;
x_19 = x_78;
goto block_76;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_12);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_12, 0);
x_82 = l_Lake_Dependency_decodeToml___closed__3;
x_83 = lean_string_append(x_82, x_81);
lean_dec(x_81);
x_84 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_85 = lean_string_append(x_83, x_84);
lean_ctor_set(x_12, 0, x_85);
x_18 = x_12;
x_19 = x_78;
goto block_76;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_86 = lean_ctor_get(x_12, 0);
lean_inc(x_86);
lean_dec(x_12);
x_87 = l_Lake_Dependency_decodeToml___closed__3;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
x_89 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_90 = lean_string_append(x_88, x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_18 = x_91;
x_19 = x_78;
goto block_76;
}
}
else
{
lean_object* x_92; 
lean_dec(x_12);
x_92 = lean_box(0);
x_18 = x_92;
x_19 = x_78;
goto block_76;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_12);
x_93 = !lean_is_exclusive(x_77);
if (x_93 == 0)
{
x_18 = x_77;
x_19 = x_78;
goto block_76;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_77, 0);
lean_inc(x_94);
lean_dec(x_77);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_18 = x_95;
x_19 = x_78;
goto block_76;
}
}
}
}
}
block_513:
{
lean_object* x_191; lean_object* x_192; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_328 = l_Lake_Dependency_decodeToml___closed__7;
lean_inc(x_1);
x_329 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_327, x_328, x_1);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_397; lean_object* x_398; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_417 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_327, x_416, x_1);
x_418 = lean_box(0);
if (lean_obj_tag(x_417) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
x_330 = x_418;
x_331 = x_190;
goto block_396;
}
else
{
uint8_t x_419; 
x_419 = !lean_is_exclusive(x_12);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_420 = lean_ctor_get(x_12, 0);
x_421 = l_Lake_Dependency_decodeToml___closed__3;
x_422 = lean_string_append(x_421, x_420);
lean_dec(x_420);
x_423 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_424 = lean_string_append(x_422, x_423);
lean_ctor_set(x_12, 0, x_424);
x_330 = x_12;
x_331 = x_190;
goto block_396;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_425 = lean_ctor_get(x_12, 0);
lean_inc(x_425);
lean_dec(x_12);
x_426 = l_Lake_Dependency_decodeToml___closed__3;
x_427 = lean_string_append(x_426, x_425);
lean_dec(x_425);
x_428 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_429 = lean_string_append(x_427, x_428);
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_429);
x_330 = x_430;
x_331 = x_190;
goto block_396;
}
}
}
else
{
uint8_t x_431; 
x_431 = !lean_is_exclusive(x_417);
if (x_431 == 0)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_417, 0);
x_433 = lean_ctor_get(x_432, 1);
lean_inc(x_433);
lean_dec(x_432);
switch (lean_obj_tag(x_433)) {
case 0:
{
lean_object* x_434; 
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
lean_dec(x_433);
lean_ctor_set(x_417, 0, x_434);
x_397 = x_417;
x_398 = x_190;
goto block_415;
}
case 2:
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_free_object(x_417);
x_435 = lean_ctor_get(x_433, 0);
lean_inc(x_435);
lean_dec(x_433);
x_436 = l_Lake_Glob_decodeToml___closed__2;
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_unsigned_to_nat(1u);
x_439 = lean_mk_array(x_438, x_437);
x_440 = l_Array_append___rarg(x_190, x_439);
lean_dec(x_439);
x_397 = x_418;
x_398 = x_440;
goto block_415;
}
case 3:
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
lean_free_object(x_417);
x_441 = lean_ctor_get(x_433, 0);
lean_inc(x_441);
lean_dec(x_433);
x_442 = l_Lake_Glob_decodeToml___closed__2;
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_unsigned_to_nat(1u);
x_445 = lean_mk_array(x_444, x_443);
x_446 = l_Array_append___rarg(x_190, x_445);
lean_dec(x_445);
x_397 = x_418;
x_398 = x_446;
goto block_415;
}
default: 
{
uint8_t x_447; 
lean_free_object(x_417);
x_447 = !lean_is_exclusive(x_433);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_448 = lean_ctor_get(x_433, 1);
lean_dec(x_448);
x_449 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_433, 0);
lean_ctor_set(x_433, 1, x_449);
x_450 = lean_unsigned_to_nat(1u);
x_451 = lean_mk_array(x_450, x_433);
x_452 = l_Array_append___rarg(x_190, x_451);
lean_dec(x_451);
x_397 = x_418;
x_398 = x_452;
goto block_415;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_453 = lean_ctor_get(x_433, 0);
lean_inc(x_453);
lean_dec(x_433);
x_454 = l_Lake_Glob_decodeToml___closed__2;
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_unsigned_to_nat(1u);
x_457 = lean_mk_array(x_456, x_455);
x_458 = l_Array_append___rarg(x_190, x_457);
lean_dec(x_457);
x_397 = x_418;
x_398 = x_458;
goto block_415;
}
}
}
}
else
{
lean_object* x_459; lean_object* x_460; 
x_459 = lean_ctor_get(x_417, 0);
lean_inc(x_459);
lean_dec(x_417);
x_460 = lean_ctor_get(x_459, 1);
lean_inc(x_460);
lean_dec(x_459);
switch (lean_obj_tag(x_460)) {
case 0:
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
lean_dec(x_460);
x_462 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_462, 0, x_461);
x_397 = x_462;
x_398 = x_190;
goto block_415;
}
case 2:
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_463 = lean_ctor_get(x_460, 0);
lean_inc(x_463);
lean_dec(x_460);
x_464 = l_Lake_Glob_decodeToml___closed__2;
x_465 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
x_466 = lean_unsigned_to_nat(1u);
x_467 = lean_mk_array(x_466, x_465);
x_468 = l_Array_append___rarg(x_190, x_467);
lean_dec(x_467);
x_397 = x_418;
x_398 = x_468;
goto block_415;
}
case 3:
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_469 = lean_ctor_get(x_460, 0);
lean_inc(x_469);
lean_dec(x_460);
x_470 = l_Lake_Glob_decodeToml___closed__2;
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_469);
lean_ctor_set(x_471, 1, x_470);
x_472 = lean_unsigned_to_nat(1u);
x_473 = lean_mk_array(x_472, x_471);
x_474 = l_Array_append___rarg(x_190, x_473);
lean_dec(x_473);
x_397 = x_418;
x_398 = x_474;
goto block_415;
}
default: 
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_475 = lean_ctor_get(x_460, 0);
lean_inc(x_475);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_476 = x_460;
} else {
 lean_dec_ref(x_460);
 x_476 = lean_box(0);
}
x_477 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_476)) {
 x_478 = lean_alloc_ctor(0, 2, 0);
} else {
 x_478 = x_476;
 lean_ctor_set_tag(x_478, 0);
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_477);
x_479 = lean_unsigned_to_nat(1u);
x_480 = lean_mk_array(x_479, x_478);
x_481 = l_Array_append___rarg(x_190, x_480);
lean_dec(x_480);
x_397 = x_418;
x_398 = x_481;
goto block_415;
}
}
}
}
block_396:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_box(0);
x_333 = l_Lake_Dependency_decodeToml___closed__2;
x_334 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_327, x_333, x_1);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; 
x_335 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_336 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_336, 0, x_11);
lean_ctor_set(x_336, 1, x_335);
lean_ctor_set(x_336, 2, x_330);
lean_ctor_set(x_336, 3, x_189);
lean_ctor_set(x_336, 4, x_332);
x_3 = x_336;
x_4 = x_331;
goto block_8;
}
else
{
lean_object* x_337; lean_object* x_338; 
x_337 = lean_ctor_get(x_334, 0);
lean_inc(x_337);
lean_dec(x_334);
x_338 = lean_ctor_get(x_337, 1);
lean_inc(x_338);
lean_dec(x_337);
switch (lean_obj_tag(x_338)) {
case 0:
{
uint8_t x_339; 
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_340 = lean_ctor_get(x_338, 1);
lean_dec(x_340);
x_341 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_338, 1, x_341);
x_342 = lean_unsigned_to_nat(1u);
x_343 = lean_mk_array(x_342, x_338);
x_344 = l_Array_append___rarg(x_331, x_343);
lean_dec(x_343);
x_345 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_346 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_346, 0, x_11);
lean_ctor_set(x_346, 1, x_345);
lean_ctor_set(x_346, 2, x_330);
lean_ctor_set(x_346, 3, x_189);
lean_ctor_set(x_346, 4, x_332);
x_3 = x_346;
x_4 = x_344;
goto block_8;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_347 = lean_ctor_get(x_338, 0);
lean_inc(x_347);
lean_dec(x_338);
x_348 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
x_350 = lean_unsigned_to_nat(1u);
x_351 = lean_mk_array(x_350, x_349);
x_352 = l_Array_append___rarg(x_331, x_351);
lean_dec(x_351);
x_353 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_354 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_354, 0, x_11);
lean_ctor_set(x_354, 1, x_353);
lean_ctor_set(x_354, 2, x_330);
lean_ctor_set(x_354, 3, x_189);
lean_ctor_set(x_354, 4, x_332);
x_3 = x_354;
x_4 = x_352;
goto block_8;
}
}
case 2:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_355 = lean_ctor_get(x_338, 0);
lean_inc(x_355);
lean_dec(x_338);
x_356 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_unsigned_to_nat(1u);
x_359 = lean_mk_array(x_358, x_357);
x_360 = l_Array_append___rarg(x_331, x_359);
lean_dec(x_359);
x_361 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_362 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_362, 0, x_11);
lean_ctor_set(x_362, 1, x_361);
lean_ctor_set(x_362, 2, x_330);
lean_ctor_set(x_362, 3, x_189);
lean_ctor_set(x_362, 4, x_332);
x_3 = x_362;
x_4 = x_360;
goto block_8;
}
case 3:
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_363 = lean_ctor_get(x_338, 0);
lean_inc(x_363);
lean_dec(x_338);
x_364 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
x_366 = lean_unsigned_to_nat(1u);
x_367 = lean_mk_array(x_366, x_365);
x_368 = l_Array_append___rarg(x_331, x_367);
lean_dec(x_367);
x_369 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_370 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_370, 0, x_11);
lean_ctor_set(x_370, 1, x_369);
lean_ctor_set(x_370, 2, x_330);
lean_ctor_set(x_370, 3, x_189);
lean_ctor_set(x_370, 4, x_332);
x_3 = x_370;
x_4 = x_368;
goto block_8;
}
case 6:
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_338, 1);
lean_inc(x_371);
lean_dec(x_338);
x_372 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_371);
lean_dec(x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_373 = lean_ctor_get(x_372, 0);
lean_inc(x_373);
lean_dec(x_372);
x_374 = l_Array_append___rarg(x_331, x_373);
lean_dec(x_373);
x_375 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_376 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_376, 0, x_11);
lean_ctor_set(x_376, 1, x_375);
lean_ctor_set(x_376, 2, x_330);
lean_ctor_set(x_376, 3, x_189);
lean_ctor_set(x_376, 4, x_332);
x_3 = x_376;
x_4 = x_374;
goto block_8;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_372, 0);
lean_inc(x_377);
lean_dec(x_372);
x_378 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_379 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_379, 0, x_11);
lean_ctor_set(x_379, 1, x_378);
lean_ctor_set(x_379, 2, x_330);
lean_ctor_set(x_379, 3, x_189);
lean_ctor_set(x_379, 4, x_377);
x_3 = x_379;
x_4 = x_331;
goto block_8;
}
}
default: 
{
uint8_t x_380; 
x_380 = !lean_is_exclusive(x_338);
if (x_380 == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_381 = lean_ctor_get(x_338, 1);
lean_dec(x_381);
x_382 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_338, 0);
lean_ctor_set(x_338, 1, x_382);
x_383 = lean_unsigned_to_nat(1u);
x_384 = lean_mk_array(x_383, x_338);
x_385 = l_Array_append___rarg(x_331, x_384);
lean_dec(x_384);
x_386 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_387 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_387, 0, x_11);
lean_ctor_set(x_387, 1, x_386);
lean_ctor_set(x_387, 2, x_330);
lean_ctor_set(x_387, 3, x_189);
lean_ctor_set(x_387, 4, x_332);
x_3 = x_387;
x_4 = x_385;
goto block_8;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_388 = lean_ctor_get(x_338, 0);
lean_inc(x_388);
lean_dec(x_338);
x_389 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
x_391 = lean_unsigned_to_nat(1u);
x_392 = lean_mk_array(x_391, x_390);
x_393 = l_Array_append___rarg(x_331, x_392);
lean_dec(x_392);
x_394 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_395 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_395, 0, x_11);
lean_ctor_set(x_395, 1, x_394);
lean_ctor_set(x_395, 2, x_330);
lean_ctor_set(x_395, 3, x_189);
lean_ctor_set(x_395, 4, x_332);
x_3 = x_395;
x_4 = x_393;
goto block_8;
}
}
}
}
}
block_415:
{
if (lean_obj_tag(x_397) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_399; 
x_399 = lean_box(0);
x_330 = x_399;
x_331 = x_398;
goto block_396;
}
else
{
uint8_t x_400; 
x_400 = !lean_is_exclusive(x_12);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_12, 0);
x_402 = l_Lake_Dependency_decodeToml___closed__3;
x_403 = lean_string_append(x_402, x_401);
lean_dec(x_401);
x_404 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_405 = lean_string_append(x_403, x_404);
lean_ctor_set(x_12, 0, x_405);
x_330 = x_12;
x_331 = x_398;
goto block_396;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_406 = lean_ctor_get(x_12, 0);
lean_inc(x_406);
lean_dec(x_12);
x_407 = l_Lake_Dependency_decodeToml___closed__3;
x_408 = lean_string_append(x_407, x_406);
lean_dec(x_406);
x_409 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_410 = lean_string_append(x_408, x_409);
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_410);
x_330 = x_411;
x_331 = x_398;
goto block_396;
}
}
}
else
{
uint8_t x_412; 
lean_dec(x_12);
x_412 = !lean_is_exclusive(x_397);
if (x_412 == 0)
{
x_330 = x_397;
x_331 = x_398;
goto block_396;
}
else
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_397, 0);
lean_inc(x_413);
lean_dec(x_397);
x_414 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_414, 0, x_413);
x_330 = x_414;
x_331 = x_398;
goto block_396;
}
}
}
}
else
{
lean_object* x_482; lean_object* x_483; 
x_482 = lean_ctor_get(x_329, 0);
lean_inc(x_482);
lean_dec(x_329);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
lean_dec(x_482);
switch (lean_obj_tag(x_483)) {
case 0:
{
lean_object* x_484; 
x_484 = lean_ctor_get(x_483, 1);
lean_inc(x_484);
lean_dec(x_483);
x_191 = x_484;
x_192 = x_190;
goto block_326;
}
case 2:
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_485 = lean_ctor_get(x_483, 0);
lean_inc(x_485);
lean_dec(x_483);
x_486 = l_Lake_Glob_decodeToml___closed__2;
x_487 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
x_488 = lean_unsigned_to_nat(1u);
x_489 = lean_mk_array(x_488, x_487);
x_490 = l_Array_append___rarg(x_190, x_489);
lean_dec(x_489);
x_491 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_191 = x_491;
x_192 = x_490;
goto block_326;
}
case 3:
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_492 = lean_ctor_get(x_483, 0);
lean_inc(x_492);
lean_dec(x_483);
x_493 = l_Lake_Glob_decodeToml___closed__2;
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
x_495 = lean_unsigned_to_nat(1u);
x_496 = lean_mk_array(x_495, x_494);
x_497 = l_Array_append___rarg(x_190, x_496);
lean_dec(x_496);
x_498 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_191 = x_498;
x_192 = x_497;
goto block_326;
}
default: 
{
uint8_t x_499; 
x_499 = !lean_is_exclusive(x_483);
if (x_499 == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_500 = lean_ctor_get(x_483, 1);
lean_dec(x_500);
x_501 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_483, 0);
lean_ctor_set(x_483, 1, x_501);
x_502 = lean_unsigned_to_nat(1u);
x_503 = lean_mk_array(x_502, x_483);
x_504 = l_Array_append___rarg(x_190, x_503);
lean_dec(x_503);
x_505 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_191 = x_505;
x_192 = x_504;
goto block_326;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_483, 0);
lean_inc(x_506);
lean_dec(x_483);
x_507 = l_Lake_Glob_decodeToml___closed__2;
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
x_509 = lean_unsigned_to_nat(1u);
x_510 = lean_mk_array(x_509, x_508);
x_511 = l_Array_append___rarg(x_190, x_510);
lean_dec(x_510);
x_512 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_191 = x_512;
x_192 = x_511;
goto block_326;
}
}
}
}
block_326:
{
lean_object* x_193; lean_object* x_194; lean_object* x_252; lean_object* x_253; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_272 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_273 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_271, x_272, x_1);
x_274 = lean_box(0);
if (lean_obj_tag(x_273) == 0)
{
x_252 = x_274;
x_253 = x_192;
goto block_270;
}
else
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_273);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_273, 0);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
switch (lean_obj_tag(x_277)) {
case 0:
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
lean_ctor_set(x_273, 0, x_278);
x_252 = x_273;
x_253 = x_192;
goto block_270;
}
case 2:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_free_object(x_273);
x_279 = lean_ctor_get(x_277, 0);
lean_inc(x_279);
lean_dec(x_277);
x_280 = l_Lake_Glob_decodeToml___closed__2;
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_unsigned_to_nat(1u);
x_283 = lean_mk_array(x_282, x_281);
x_284 = l_Array_append___rarg(x_192, x_283);
lean_dec(x_283);
x_252 = x_274;
x_253 = x_284;
goto block_270;
}
case 3:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_free_object(x_273);
x_285 = lean_ctor_get(x_277, 0);
lean_inc(x_285);
lean_dec(x_277);
x_286 = l_Lake_Glob_decodeToml___closed__2;
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_unsigned_to_nat(1u);
x_289 = lean_mk_array(x_288, x_287);
x_290 = l_Array_append___rarg(x_192, x_289);
lean_dec(x_289);
x_252 = x_274;
x_253 = x_290;
goto block_270;
}
default: 
{
uint8_t x_291; 
lean_free_object(x_273);
x_291 = !lean_is_exclusive(x_277);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = lean_ctor_get(x_277, 1);
lean_dec(x_292);
x_293 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_277, 0);
lean_ctor_set(x_277, 1, x_293);
x_294 = lean_unsigned_to_nat(1u);
x_295 = lean_mk_array(x_294, x_277);
x_296 = l_Array_append___rarg(x_192, x_295);
lean_dec(x_295);
x_252 = x_274;
x_253 = x_296;
goto block_270;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_297 = lean_ctor_get(x_277, 0);
lean_inc(x_297);
lean_dec(x_277);
x_298 = l_Lake_Glob_decodeToml___closed__2;
x_299 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
x_300 = lean_unsigned_to_nat(1u);
x_301 = lean_mk_array(x_300, x_299);
x_302 = l_Array_append___rarg(x_192, x_301);
lean_dec(x_301);
x_252 = x_274;
x_253 = x_302;
goto block_270;
}
}
}
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_273, 0);
lean_inc(x_303);
lean_dec(x_273);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
switch (lean_obj_tag(x_304)) {
case 0:
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_304, 1);
lean_inc(x_305);
lean_dec(x_304);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_305);
x_252 = x_306;
x_253 = x_192;
goto block_270;
}
case 2:
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_307 = lean_ctor_get(x_304, 0);
lean_inc(x_307);
lean_dec(x_304);
x_308 = l_Lake_Glob_decodeToml___closed__2;
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_unsigned_to_nat(1u);
x_311 = lean_mk_array(x_310, x_309);
x_312 = l_Array_append___rarg(x_192, x_311);
lean_dec(x_311);
x_252 = x_274;
x_253 = x_312;
goto block_270;
}
case 3:
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_313 = lean_ctor_get(x_304, 0);
lean_inc(x_313);
lean_dec(x_304);
x_314 = l_Lake_Glob_decodeToml___closed__2;
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
x_316 = lean_unsigned_to_nat(1u);
x_317 = lean_mk_array(x_316, x_315);
x_318 = l_Array_append___rarg(x_192, x_317);
lean_dec(x_317);
x_252 = x_274;
x_253 = x_318;
goto block_270;
}
default: 
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_319 = lean_ctor_get(x_304, 0);
lean_inc(x_319);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 x_320 = x_304;
} else {
 lean_dec_ref(x_304);
 x_320 = lean_box(0);
}
x_321 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_320)) {
 x_322 = lean_alloc_ctor(0, 2, 0);
} else {
 x_322 = x_320;
 lean_ctor_set_tag(x_322, 0);
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_321);
x_323 = lean_unsigned_to_nat(1u);
x_324 = lean_mk_array(x_323, x_322);
x_325 = l_Array_append___rarg(x_192, x_324);
lean_dec(x_324);
x_252 = x_274;
x_253 = x_325;
goto block_270;
}
}
}
}
block_251:
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_box(0);
x_196 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_197 = l_Lake_Dependency_decodeToml___closed__2;
x_198 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_196, x_197, x_1);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_199, 0, x_11);
lean_ctor_set(x_199, 1, x_191);
lean_ctor_set(x_199, 2, x_193);
lean_ctor_set(x_199, 3, x_189);
lean_ctor_set(x_199, 4, x_195);
x_3 = x_199;
x_4 = x_194;
goto block_8;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
switch (lean_obj_tag(x_201)) {
case 0:
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_201, 1);
lean_dec(x_203);
x_204 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_201, 1, x_204);
x_205 = lean_unsigned_to_nat(1u);
x_206 = lean_mk_array(x_205, x_201);
x_207 = l_Array_append___rarg(x_194, x_206);
lean_dec(x_206);
x_208 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_208, 0, x_11);
lean_ctor_set(x_208, 1, x_191);
lean_ctor_set(x_208, 2, x_193);
lean_ctor_set(x_208, 3, x_189);
lean_ctor_set(x_208, 4, x_195);
x_3 = x_208;
x_4 = x_207;
goto block_8;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_209 = lean_ctor_get(x_201, 0);
lean_inc(x_209);
lean_dec(x_201);
x_210 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_mk_array(x_212, x_211);
x_214 = l_Array_append___rarg(x_194, x_213);
lean_dec(x_213);
x_215 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_215, 0, x_11);
lean_ctor_set(x_215, 1, x_191);
lean_ctor_set(x_215, 2, x_193);
lean_ctor_set(x_215, 3, x_189);
lean_ctor_set(x_215, 4, x_195);
x_3 = x_215;
x_4 = x_214;
goto block_8;
}
}
case 2:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_216 = lean_ctor_get(x_201, 0);
lean_inc(x_216);
lean_dec(x_201);
x_217 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_unsigned_to_nat(1u);
x_220 = lean_mk_array(x_219, x_218);
x_221 = l_Array_append___rarg(x_194, x_220);
lean_dec(x_220);
x_222 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_222, 0, x_11);
lean_ctor_set(x_222, 1, x_191);
lean_ctor_set(x_222, 2, x_193);
lean_ctor_set(x_222, 3, x_189);
lean_ctor_set(x_222, 4, x_195);
x_3 = x_222;
x_4 = x_221;
goto block_8;
}
case 3:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_223 = lean_ctor_get(x_201, 0);
lean_inc(x_223);
lean_dec(x_201);
x_224 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_unsigned_to_nat(1u);
x_227 = lean_mk_array(x_226, x_225);
x_228 = l_Array_append___rarg(x_194, x_227);
lean_dec(x_227);
x_229 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_229, 0, x_11);
lean_ctor_set(x_229, 1, x_191);
lean_ctor_set(x_229, 2, x_193);
lean_ctor_set(x_229, 3, x_189);
lean_ctor_set(x_229, 4, x_195);
x_3 = x_229;
x_4 = x_228;
goto block_8;
}
case 6:
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_201, 1);
lean_inc(x_230);
lean_dec(x_201);
x_231 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_230);
lean_dec(x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
lean_dec(x_231);
x_233 = l_Array_append___rarg(x_194, x_232);
lean_dec(x_232);
x_234 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_234, 0, x_11);
lean_ctor_set(x_234, 1, x_191);
lean_ctor_set(x_234, 2, x_193);
lean_ctor_set(x_234, 3, x_189);
lean_ctor_set(x_234, 4, x_195);
x_3 = x_234;
x_4 = x_233;
goto block_8;
}
else
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_231, 0);
lean_inc(x_235);
lean_dec(x_231);
x_236 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_236, 0, x_11);
lean_ctor_set(x_236, 1, x_191);
lean_ctor_set(x_236, 2, x_193);
lean_ctor_set(x_236, 3, x_189);
lean_ctor_set(x_236, 4, x_235);
x_3 = x_236;
x_4 = x_194;
goto block_8;
}
}
default: 
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_201);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_238 = lean_ctor_get(x_201, 1);
lean_dec(x_238);
x_239 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_201, 0);
lean_ctor_set(x_201, 1, x_239);
x_240 = lean_unsigned_to_nat(1u);
x_241 = lean_mk_array(x_240, x_201);
x_242 = l_Array_append___rarg(x_194, x_241);
lean_dec(x_241);
x_243 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_243, 0, x_11);
lean_ctor_set(x_243, 1, x_191);
lean_ctor_set(x_243, 2, x_193);
lean_ctor_set(x_243, 3, x_189);
lean_ctor_set(x_243, 4, x_195);
x_3 = x_243;
x_4 = x_242;
goto block_8;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_244 = lean_ctor_get(x_201, 0);
lean_inc(x_244);
lean_dec(x_201);
x_245 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_unsigned_to_nat(1u);
x_248 = lean_mk_array(x_247, x_246);
x_249 = l_Array_append___rarg(x_194, x_248);
lean_dec(x_248);
x_250 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_250, 0, x_11);
lean_ctor_set(x_250, 1, x_191);
lean_ctor_set(x_250, 2, x_193);
lean_ctor_set(x_250, 3, x_189);
lean_ctor_set(x_250, 4, x_195);
x_3 = x_250;
x_4 = x_249;
goto block_8;
}
}
}
}
}
block_270:
{
if (lean_obj_tag(x_252) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_254; 
x_254 = lean_box(0);
x_193 = x_254;
x_194 = x_253;
goto block_251;
}
else
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_12);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_256 = lean_ctor_get(x_12, 0);
x_257 = l_Lake_Dependency_decodeToml___closed__3;
x_258 = lean_string_append(x_257, x_256);
lean_dec(x_256);
x_259 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_260 = lean_string_append(x_258, x_259);
lean_ctor_set(x_12, 0, x_260);
x_193 = x_12;
x_194 = x_253;
goto block_251;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_261 = lean_ctor_get(x_12, 0);
lean_inc(x_261);
lean_dec(x_12);
x_262 = l_Lake_Dependency_decodeToml___closed__3;
x_263 = lean_string_append(x_262, x_261);
lean_dec(x_261);
x_264 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_265 = lean_string_append(x_263, x_264);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_265);
x_193 = x_266;
x_194 = x_253;
goto block_251;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_12);
x_267 = !lean_is_exclusive(x_252);
if (x_267 == 0)
{
x_193 = x_252;
x_194 = x_253;
goto block_251;
}
else
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_252, 0);
lean_inc(x_268);
lean_dec(x_252);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
x_193 = x_269;
x_194 = x_253;
goto block_251;
}
}
}
}
}
block_793:
{
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_516 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_517 = l_Lake_Dependency_decodeToml___closed__8;
lean_inc(x_1);
x_518 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_516, x_517, x_1);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = l_Lake_Dependency_decodeToml___closed__10;
lean_inc(x_1);
x_520 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_516, x_519, x_1);
x_521 = lean_box(0);
if (lean_obj_tag(x_520) == 0)
{
x_14 = x_521;
x_15 = x_515;
goto block_188;
}
else
{
uint8_t x_522; 
x_522 = !lean_is_exclusive(x_520);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; 
x_523 = lean_ctor_get(x_520, 0);
x_524 = lean_ctor_get(x_523, 1);
lean_inc(x_524);
lean_dec(x_523);
switch (lean_obj_tag(x_524)) {
case 0:
{
uint8_t x_525; 
lean_free_object(x_520);
x_525 = !lean_is_exclusive(x_524);
if (x_525 == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_526 = lean_ctor_get(x_524, 1);
lean_dec(x_526);
x_527 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_524, 1, x_527);
x_528 = lean_unsigned_to_nat(1u);
x_529 = lean_mk_array(x_528, x_524);
x_530 = l_Array_append___rarg(x_515, x_529);
lean_dec(x_529);
x_14 = x_521;
x_15 = x_530;
goto block_188;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_531 = lean_ctor_get(x_524, 0);
lean_inc(x_531);
lean_dec(x_524);
x_532 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_531);
lean_ctor_set(x_533, 1, x_532);
x_534 = lean_unsigned_to_nat(1u);
x_535 = lean_mk_array(x_534, x_533);
x_536 = l_Array_append___rarg(x_515, x_535);
lean_dec(x_535);
x_14 = x_521;
x_15 = x_536;
goto block_188;
}
}
case 2:
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_free_object(x_520);
x_537 = lean_ctor_get(x_524, 0);
lean_inc(x_537);
lean_dec(x_524);
x_538 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
x_540 = lean_unsigned_to_nat(1u);
x_541 = lean_mk_array(x_540, x_539);
x_542 = l_Array_append___rarg(x_515, x_541);
lean_dec(x_541);
x_14 = x_521;
x_15 = x_542;
goto block_188;
}
case 3:
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_free_object(x_520);
x_543 = lean_ctor_get(x_524, 0);
lean_inc(x_543);
lean_dec(x_524);
x_544 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
x_546 = lean_unsigned_to_nat(1u);
x_547 = lean_mk_array(x_546, x_545);
x_548 = l_Array_append___rarg(x_515, x_547);
lean_dec(x_547);
x_14 = x_521;
x_15 = x_548;
goto block_188;
}
case 6:
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_524, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_524, 1);
lean_inc(x_550);
lean_dec(x_524);
x_551 = l_Lake_DependencySrc_decodeToml(x_550, x_549);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; 
lean_free_object(x_520);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
lean_dec(x_551);
x_553 = l_Array_append___rarg(x_515, x_552);
lean_dec(x_552);
x_14 = x_521;
x_15 = x_553;
goto block_188;
}
else
{
lean_object* x_554; 
x_554 = lean_ctor_get(x_551, 0);
lean_inc(x_554);
lean_dec(x_551);
lean_ctor_set(x_520, 0, x_554);
x_14 = x_520;
x_15 = x_515;
goto block_188;
}
}
default: 
{
uint8_t x_555; 
lean_free_object(x_520);
x_555 = !lean_is_exclusive(x_524);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_556 = lean_ctor_get(x_524, 1);
lean_dec(x_556);
x_557 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_524, 0);
lean_ctor_set(x_524, 1, x_557);
x_558 = lean_unsigned_to_nat(1u);
x_559 = lean_mk_array(x_558, x_524);
x_560 = l_Array_append___rarg(x_515, x_559);
lean_dec(x_559);
x_14 = x_521;
x_15 = x_560;
goto block_188;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_561 = lean_ctor_get(x_524, 0);
lean_inc(x_561);
lean_dec(x_524);
x_562 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_563 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
x_564 = lean_unsigned_to_nat(1u);
x_565 = lean_mk_array(x_564, x_563);
x_566 = l_Array_append___rarg(x_515, x_565);
lean_dec(x_565);
x_14 = x_521;
x_15 = x_566;
goto block_188;
}
}
}
}
else
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_520, 0);
lean_inc(x_567);
lean_dec(x_520);
x_568 = lean_ctor_get(x_567, 1);
lean_inc(x_568);
lean_dec(x_567);
switch (lean_obj_tag(x_568)) {
case 0:
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_570 = x_568;
} else {
 lean_dec_ref(x_568);
 x_570 = lean_box(0);
}
x_571 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
if (lean_is_scalar(x_570)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_570;
}
lean_ctor_set(x_572, 0, x_569);
lean_ctor_set(x_572, 1, x_571);
x_573 = lean_unsigned_to_nat(1u);
x_574 = lean_mk_array(x_573, x_572);
x_575 = l_Array_append___rarg(x_515, x_574);
lean_dec(x_574);
x_14 = x_521;
x_15 = x_575;
goto block_188;
}
case 2:
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_576 = lean_ctor_get(x_568, 0);
lean_inc(x_576);
lean_dec(x_568);
x_577 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
x_579 = lean_unsigned_to_nat(1u);
x_580 = lean_mk_array(x_579, x_578);
x_581 = l_Array_append___rarg(x_515, x_580);
lean_dec(x_580);
x_14 = x_521;
x_15 = x_581;
goto block_188;
}
case 3:
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_582 = lean_ctor_get(x_568, 0);
lean_inc(x_582);
lean_dec(x_568);
x_583 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_582);
lean_ctor_set(x_584, 1, x_583);
x_585 = lean_unsigned_to_nat(1u);
x_586 = lean_mk_array(x_585, x_584);
x_587 = l_Array_append___rarg(x_515, x_586);
lean_dec(x_586);
x_14 = x_521;
x_15 = x_587;
goto block_188;
}
case 6:
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_568, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_568, 1);
lean_inc(x_589);
lean_dec(x_568);
x_590 = l_Lake_DependencySrc_decodeToml(x_589, x_588);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
lean_dec(x_590);
x_592 = l_Array_append___rarg(x_515, x_591);
lean_dec(x_591);
x_14 = x_521;
x_15 = x_592;
goto block_188;
}
else
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_ctor_get(x_590, 0);
lean_inc(x_593);
lean_dec(x_590);
x_594 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_594, 0, x_593);
x_14 = x_594;
x_15 = x_515;
goto block_188;
}
}
default: 
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_595 = lean_ctor_get(x_568, 0);
lean_inc(x_595);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_596 = x_568;
} else {
 lean_dec_ref(x_568);
 x_596 = lean_box(0);
}
x_597 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
if (lean_is_scalar(x_596)) {
 x_598 = lean_alloc_ctor(0, 2, 0);
} else {
 x_598 = x_596;
 lean_ctor_set_tag(x_598, 0);
}
lean_ctor_set(x_598, 0, x_595);
lean_ctor_set(x_598, 1, x_597);
x_599 = lean_unsigned_to_nat(1u);
x_600 = lean_mk_array(x_599, x_598);
x_601 = l_Array_append___rarg(x_515, x_600);
lean_dec(x_600);
x_14 = x_521;
x_15 = x_601;
goto block_188;
}
}
}
}
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_518, 0);
lean_inc(x_602);
if (lean_is_exclusive(x_518)) {
 lean_ctor_release(x_518, 0);
 x_603 = x_518;
} else {
 lean_dec_ref(x_518);
 x_603 = lean_box(0);
}
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
lean_dec(x_602);
switch (lean_obj_tag(x_604)) {
case 0:
{
uint8_t x_605; 
x_605 = !lean_is_exclusive(x_604);
if (x_605 == 0)
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_606 = lean_ctor_get(x_604, 1);
x_607 = lean_ctor_get(x_604, 0);
lean_dec(x_607);
x_613 = l_Lake_DependencySrc_decodeToml___closed__2;
lean_inc(x_1);
x_614 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_516, x_613, x_1);
x_615 = lean_box(0);
if (lean_obj_tag(x_614) == 0)
{
lean_free_object(x_604);
x_608 = x_615;
x_609 = x_515;
goto block_612;
}
else
{
uint8_t x_616; 
x_616 = !lean_is_exclusive(x_614);
if (x_616 == 0)
{
lean_object* x_617; lean_object* x_618; 
x_617 = lean_ctor_get(x_614, 0);
x_618 = lean_ctor_get(x_617, 1);
lean_inc(x_618);
lean_dec(x_617);
switch (lean_obj_tag(x_618)) {
case 0:
{
lean_object* x_619; 
lean_free_object(x_604);
x_619 = lean_ctor_get(x_618, 1);
lean_inc(x_619);
lean_dec(x_618);
lean_ctor_set(x_614, 0, x_619);
x_608 = x_614;
x_609 = x_515;
goto block_612;
}
case 2:
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_free_object(x_614);
x_620 = lean_ctor_get(x_618, 0);
lean_inc(x_620);
lean_dec(x_618);
x_621 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set(x_604, 1, x_621);
lean_ctor_set(x_604, 0, x_620);
x_622 = lean_unsigned_to_nat(1u);
x_623 = lean_mk_array(x_622, x_604);
x_624 = l_Array_append___rarg(x_515, x_623);
lean_dec(x_623);
x_608 = x_615;
x_609 = x_624;
goto block_612;
}
case 3:
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_free_object(x_614);
x_625 = lean_ctor_get(x_618, 0);
lean_inc(x_625);
lean_dec(x_618);
x_626 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set(x_604, 1, x_626);
lean_ctor_set(x_604, 0, x_625);
x_627 = lean_unsigned_to_nat(1u);
x_628 = lean_mk_array(x_627, x_604);
x_629 = l_Array_append___rarg(x_515, x_628);
lean_dec(x_628);
x_608 = x_615;
x_609 = x_629;
goto block_612;
}
default: 
{
uint8_t x_630; 
lean_free_object(x_614);
lean_free_object(x_604);
x_630 = !lean_is_exclusive(x_618);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_631 = lean_ctor_get(x_618, 1);
lean_dec(x_631);
x_632 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_618, 0);
lean_ctor_set(x_618, 1, x_632);
x_633 = lean_unsigned_to_nat(1u);
x_634 = lean_mk_array(x_633, x_618);
x_635 = l_Array_append___rarg(x_515, x_634);
lean_dec(x_634);
x_608 = x_615;
x_609 = x_635;
goto block_612;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_636 = lean_ctor_get(x_618, 0);
lean_inc(x_636);
lean_dec(x_618);
x_637 = l_Lake_Glob_decodeToml___closed__2;
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
x_639 = lean_unsigned_to_nat(1u);
x_640 = lean_mk_array(x_639, x_638);
x_641 = l_Array_append___rarg(x_515, x_640);
lean_dec(x_640);
x_608 = x_615;
x_609 = x_641;
goto block_612;
}
}
}
}
else
{
lean_object* x_642; lean_object* x_643; 
x_642 = lean_ctor_get(x_614, 0);
lean_inc(x_642);
lean_dec(x_614);
x_643 = lean_ctor_get(x_642, 1);
lean_inc(x_643);
lean_dec(x_642);
switch (lean_obj_tag(x_643)) {
case 0:
{
lean_object* x_644; lean_object* x_645; 
lean_free_object(x_604);
x_644 = lean_ctor_get(x_643, 1);
lean_inc(x_644);
lean_dec(x_643);
x_645 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_645, 0, x_644);
x_608 = x_645;
x_609 = x_515;
goto block_612;
}
case 2:
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_646 = lean_ctor_get(x_643, 0);
lean_inc(x_646);
lean_dec(x_643);
x_647 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set(x_604, 1, x_647);
lean_ctor_set(x_604, 0, x_646);
x_648 = lean_unsigned_to_nat(1u);
x_649 = lean_mk_array(x_648, x_604);
x_650 = l_Array_append___rarg(x_515, x_649);
lean_dec(x_649);
x_608 = x_615;
x_609 = x_650;
goto block_612;
}
case 3:
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_651 = lean_ctor_get(x_643, 0);
lean_inc(x_651);
lean_dec(x_643);
x_652 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set(x_604, 1, x_652);
lean_ctor_set(x_604, 0, x_651);
x_653 = lean_unsigned_to_nat(1u);
x_654 = lean_mk_array(x_653, x_604);
x_655 = l_Array_append___rarg(x_515, x_654);
lean_dec(x_654);
x_608 = x_615;
x_609 = x_655;
goto block_612;
}
default: 
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; 
lean_free_object(x_604);
x_656 = lean_ctor_get(x_643, 0);
lean_inc(x_656);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 x_657 = x_643;
} else {
 lean_dec_ref(x_643);
 x_657 = lean_box(0);
}
x_658 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_657)) {
 x_659 = lean_alloc_ctor(0, 2, 0);
} else {
 x_659 = x_657;
 lean_ctor_set_tag(x_659, 0);
}
lean_ctor_set(x_659, 0, x_656);
lean_ctor_set(x_659, 1, x_658);
x_660 = lean_unsigned_to_nat(1u);
x_661 = lean_mk_array(x_660, x_659);
x_662 = l_Array_append___rarg(x_515, x_661);
lean_dec(x_661);
x_608 = x_615;
x_609 = x_662;
goto block_612;
}
}
}
}
block_612:
{
lean_object* x_610; lean_object* x_611; 
lean_inc(x_12);
x_610 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_610, 0, x_606);
lean_ctor_set(x_610, 1, x_12);
lean_ctor_set(x_610, 2, x_608);
if (lean_is_scalar(x_603)) {
 x_611 = lean_alloc_ctor(1, 1, 0);
} else {
 x_611 = x_603;
}
lean_ctor_set(x_611, 0, x_610);
x_14 = x_611;
x_15 = x_609;
goto block_188;
}
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_663 = lean_ctor_get(x_604, 1);
lean_inc(x_663);
lean_dec(x_604);
x_669 = l_Lake_DependencySrc_decodeToml___closed__2;
lean_inc(x_1);
x_670 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_516, x_669, x_1);
x_671 = lean_box(0);
if (lean_obj_tag(x_670) == 0)
{
x_664 = x_671;
x_665 = x_515;
goto block_668;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_672 = lean_ctor_get(x_670, 0);
lean_inc(x_672);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 x_673 = x_670;
} else {
 lean_dec_ref(x_670);
 x_673 = lean_box(0);
}
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
switch (lean_obj_tag(x_674)) {
case 0:
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_674, 1);
lean_inc(x_675);
lean_dec(x_674);
if (lean_is_scalar(x_673)) {
 x_676 = lean_alloc_ctor(1, 1, 0);
} else {
 x_676 = x_673;
}
lean_ctor_set(x_676, 0, x_675);
x_664 = x_676;
x_665 = x_515;
goto block_668;
}
case 2:
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; 
lean_dec(x_673);
x_677 = lean_ctor_get(x_674, 0);
lean_inc(x_677);
lean_dec(x_674);
x_678 = l_Lake_Glob_decodeToml___closed__2;
x_679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
x_680 = lean_unsigned_to_nat(1u);
x_681 = lean_mk_array(x_680, x_679);
x_682 = l_Array_append___rarg(x_515, x_681);
lean_dec(x_681);
x_664 = x_671;
x_665 = x_682;
goto block_668;
}
case 3:
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_673);
x_683 = lean_ctor_get(x_674, 0);
lean_inc(x_683);
lean_dec(x_674);
x_684 = l_Lake_Glob_decodeToml___closed__2;
x_685 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_685, 0, x_683);
lean_ctor_set(x_685, 1, x_684);
x_686 = lean_unsigned_to_nat(1u);
x_687 = lean_mk_array(x_686, x_685);
x_688 = l_Array_append___rarg(x_515, x_687);
lean_dec(x_687);
x_664 = x_671;
x_665 = x_688;
goto block_668;
}
default: 
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; 
lean_dec(x_673);
x_689 = lean_ctor_get(x_674, 0);
lean_inc(x_689);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_690 = x_674;
} else {
 lean_dec_ref(x_674);
 x_690 = lean_box(0);
}
x_691 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_690)) {
 x_692 = lean_alloc_ctor(0, 2, 0);
} else {
 x_692 = x_690;
 lean_ctor_set_tag(x_692, 0);
}
lean_ctor_set(x_692, 0, x_689);
lean_ctor_set(x_692, 1, x_691);
x_693 = lean_unsigned_to_nat(1u);
x_694 = lean_mk_array(x_693, x_692);
x_695 = l_Array_append___rarg(x_515, x_694);
lean_dec(x_694);
x_664 = x_671;
x_665 = x_695;
goto block_668;
}
}
}
block_668:
{
lean_object* x_666; lean_object* x_667; 
lean_inc(x_12);
x_666 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_666, 0, x_663);
lean_ctor_set(x_666, 1, x_12);
lean_ctor_set(x_666, 2, x_664);
if (lean_is_scalar(x_603)) {
 x_667 = lean_alloc_ctor(1, 1, 0);
} else {
 x_667 = x_603;
}
lean_ctor_set(x_667, 0, x_666);
x_14 = x_667;
x_15 = x_665;
goto block_188;
}
}
}
case 2:
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
lean_dec(x_603);
x_696 = lean_ctor_get(x_604, 0);
lean_inc(x_696);
lean_dec(x_604);
x_697 = l_Lake_Dependency_decodeToml___closed__11;
x_698 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_697);
x_699 = lean_array_push(x_515, x_698);
x_700 = lean_box(0);
x_189 = x_700;
x_190 = x_699;
goto block_513;
}
case 3:
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_603);
x_701 = lean_ctor_get(x_604, 0);
lean_inc(x_701);
lean_dec(x_604);
x_702 = l_Lake_Dependency_decodeToml___closed__11;
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set(x_703, 1, x_702);
x_704 = lean_array_push(x_515, x_703);
x_705 = lean_box(0);
x_189 = x_705;
x_190 = x_704;
goto block_513;
}
case 6:
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_771; lean_object* x_772; 
x_706 = lean_ctor_get(x_604, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_604, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_708 = x_604;
} else {
 lean_dec_ref(x_604);
 x_708 = lean_box(0);
}
x_771 = l_Lake_DependencySrc_decodeToml___closed__17;
lean_inc(x_707);
x_772 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__1(x_707, x_771, x_706);
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; 
x_773 = lean_ctor_get(x_772, 0);
lean_inc(x_773);
lean_dec(x_772);
x_774 = l_Array_append___rarg(x_515, x_773);
lean_dec(x_773);
x_775 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_709 = x_775;
x_710 = x_774;
goto block_770;
}
else
{
lean_object* x_776; 
x_776 = lean_ctor_get(x_772, 0);
lean_inc(x_776);
lean_dec(x_772);
x_709 = x_776;
x_710 = x_515;
goto block_770;
}
block_770:
{
lean_object* x_711; lean_object* x_712; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_716 = l_Lake_DependencySrc_decodeToml___closed__2;
x_717 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_516, x_716, x_707);
x_718 = lean_box(0);
if (lean_obj_tag(x_717) == 0)
{
lean_dec(x_708);
x_711 = x_718;
x_712 = x_710;
goto block_715;
}
else
{
uint8_t x_719; 
x_719 = !lean_is_exclusive(x_717);
if (x_719 == 0)
{
lean_object* x_720; lean_object* x_721; 
x_720 = lean_ctor_get(x_717, 0);
x_721 = lean_ctor_get(x_720, 1);
lean_inc(x_721);
lean_dec(x_720);
switch (lean_obj_tag(x_721)) {
case 0:
{
lean_object* x_722; 
lean_dec(x_708);
x_722 = lean_ctor_get(x_721, 1);
lean_inc(x_722);
lean_dec(x_721);
lean_ctor_set(x_717, 0, x_722);
x_711 = x_717;
x_712 = x_710;
goto block_715;
}
case 2:
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_free_object(x_717);
x_723 = lean_ctor_get(x_721, 0);
lean_inc(x_723);
lean_dec(x_721);
x_724 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_708)) {
 x_725 = lean_alloc_ctor(0, 2, 0);
} else {
 x_725 = x_708;
 lean_ctor_set_tag(x_725, 0);
}
lean_ctor_set(x_725, 0, x_723);
lean_ctor_set(x_725, 1, x_724);
x_726 = lean_unsigned_to_nat(1u);
x_727 = lean_mk_array(x_726, x_725);
x_728 = l_Array_append___rarg(x_710, x_727);
lean_dec(x_727);
x_711 = x_718;
x_712 = x_728;
goto block_715;
}
case 3:
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_free_object(x_717);
x_729 = lean_ctor_get(x_721, 0);
lean_inc(x_729);
lean_dec(x_721);
x_730 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_708)) {
 x_731 = lean_alloc_ctor(0, 2, 0);
} else {
 x_731 = x_708;
 lean_ctor_set_tag(x_731, 0);
}
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
x_732 = lean_unsigned_to_nat(1u);
x_733 = lean_mk_array(x_732, x_731);
x_734 = l_Array_append___rarg(x_710, x_733);
lean_dec(x_733);
x_711 = x_718;
x_712 = x_734;
goto block_715;
}
default: 
{
uint8_t x_735; 
lean_free_object(x_717);
lean_dec(x_708);
x_735 = !lean_is_exclusive(x_721);
if (x_735 == 0)
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_736 = lean_ctor_get(x_721, 1);
lean_dec(x_736);
x_737 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_721, 0);
lean_ctor_set(x_721, 1, x_737);
x_738 = lean_unsigned_to_nat(1u);
x_739 = lean_mk_array(x_738, x_721);
x_740 = l_Array_append___rarg(x_710, x_739);
lean_dec(x_739);
x_711 = x_718;
x_712 = x_740;
goto block_715;
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_741 = lean_ctor_get(x_721, 0);
lean_inc(x_741);
lean_dec(x_721);
x_742 = l_Lake_Glob_decodeToml___closed__2;
x_743 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_743, 0, x_741);
lean_ctor_set(x_743, 1, x_742);
x_744 = lean_unsigned_to_nat(1u);
x_745 = lean_mk_array(x_744, x_743);
x_746 = l_Array_append___rarg(x_710, x_745);
lean_dec(x_745);
x_711 = x_718;
x_712 = x_746;
goto block_715;
}
}
}
}
else
{
lean_object* x_747; lean_object* x_748; 
x_747 = lean_ctor_get(x_717, 0);
lean_inc(x_747);
lean_dec(x_717);
x_748 = lean_ctor_get(x_747, 1);
lean_inc(x_748);
lean_dec(x_747);
switch (lean_obj_tag(x_748)) {
case 0:
{
lean_object* x_749; lean_object* x_750; 
lean_dec(x_708);
x_749 = lean_ctor_get(x_748, 1);
lean_inc(x_749);
lean_dec(x_748);
x_750 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_750, 0, x_749);
x_711 = x_750;
x_712 = x_710;
goto block_715;
}
case 2:
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_751 = lean_ctor_get(x_748, 0);
lean_inc(x_751);
lean_dec(x_748);
x_752 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_708)) {
 x_753 = lean_alloc_ctor(0, 2, 0);
} else {
 x_753 = x_708;
 lean_ctor_set_tag(x_753, 0);
}
lean_ctor_set(x_753, 0, x_751);
lean_ctor_set(x_753, 1, x_752);
x_754 = lean_unsigned_to_nat(1u);
x_755 = lean_mk_array(x_754, x_753);
x_756 = l_Array_append___rarg(x_710, x_755);
lean_dec(x_755);
x_711 = x_718;
x_712 = x_756;
goto block_715;
}
case 3:
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_757 = lean_ctor_get(x_748, 0);
lean_inc(x_757);
lean_dec(x_748);
x_758 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_708)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_708;
 lean_ctor_set_tag(x_759, 0);
}
lean_ctor_set(x_759, 0, x_757);
lean_ctor_set(x_759, 1, x_758);
x_760 = lean_unsigned_to_nat(1u);
x_761 = lean_mk_array(x_760, x_759);
x_762 = l_Array_append___rarg(x_710, x_761);
lean_dec(x_761);
x_711 = x_718;
x_712 = x_762;
goto block_715;
}
default: 
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_708);
x_763 = lean_ctor_get(x_748, 0);
lean_inc(x_763);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_764 = x_748;
} else {
 lean_dec_ref(x_748);
 x_764 = lean_box(0);
}
x_765 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_764)) {
 x_766 = lean_alloc_ctor(0, 2, 0);
} else {
 x_766 = x_764;
 lean_ctor_set_tag(x_766, 0);
}
lean_ctor_set(x_766, 0, x_763);
lean_ctor_set(x_766, 1, x_765);
x_767 = lean_unsigned_to_nat(1u);
x_768 = lean_mk_array(x_767, x_766);
x_769 = l_Array_append___rarg(x_710, x_768);
lean_dec(x_768);
x_711 = x_718;
x_712 = x_769;
goto block_715;
}
}
}
}
block_715:
{
lean_object* x_713; lean_object* x_714; 
lean_inc(x_12);
x_713 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_713, 0, x_709);
lean_ctor_set(x_713, 1, x_12);
lean_ctor_set(x_713, 2, x_711);
if (lean_is_scalar(x_603)) {
 x_714 = lean_alloc_ctor(1, 1, 0);
} else {
 x_714 = x_603;
}
lean_ctor_set(x_714, 0, x_713);
x_14 = x_714;
x_15 = x_712;
goto block_188;
}
}
}
default: 
{
uint8_t x_777; 
lean_dec(x_603);
x_777 = !lean_is_exclusive(x_604);
if (x_777 == 0)
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_778 = lean_ctor_get(x_604, 1);
lean_dec(x_778);
x_779 = l_Lake_Dependency_decodeToml___closed__11;
lean_ctor_set_tag(x_604, 0);
lean_ctor_set(x_604, 1, x_779);
x_780 = lean_array_push(x_515, x_604);
x_781 = lean_box(0);
x_189 = x_781;
x_190 = x_780;
goto block_513;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_782 = lean_ctor_get(x_604, 0);
lean_inc(x_782);
lean_dec(x_604);
x_783 = l_Lake_Dependency_decodeToml___closed__11;
x_784 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
x_785 = lean_array_push(x_515, x_784);
x_786 = lean_box(0);
x_189 = x_786;
x_190 = x_785;
goto block_513;
}
}
}
}
}
else
{
uint8_t x_787; 
x_787 = !lean_is_exclusive(x_514);
if (x_787 == 0)
{
lean_object* x_788; lean_object* x_789; 
x_788 = lean_ctor_get(x_514, 0);
x_789 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_514, 0, x_789);
x_14 = x_514;
x_15 = x_515;
goto block_188;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_514, 0);
lean_inc(x_790);
lean_dec(x_514);
x_791 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_791, 0, x_790);
x_792 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_792, 0, x_791);
x_14 = x_792;
x_15 = x_515;
goto block_188;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependency(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_mk_array(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 3:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_mk_array(x_23, x_22);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 6:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_Dependency_decodeToml(x_27, x_26);
return x_28;
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 1);
lean_dec(x_30);
x_31 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_31);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_mk_array(x_32, x_1);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_array(x_38, x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
x_9 = lean_array_uget(x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = 0;
x_14 = l_Lean_Syntax_getPos_x3f(x_10, x_13);
lean_dec(x_10);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
x_16 = lean_box(0);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_FileMap_toPosition(x_12, x_17);
x_19 = l_Lean_mkErrorStringWithPos(x_15, x_18, x_11, x_16);
lean_dec(x_11);
lean_dec(x_15);
x_20 = 3;
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = lean_array_push(x_6, x_21);
x_23 = 1;
x_24 = lean_usize_add(x_3, x_23);
x_25 = lean_box(0);
x_3 = x_24;
x_5 = x_25;
x_6 = x_22;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; 
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
lean_dec(x_14);
x_28 = l_Lean_FileMap_toPosition(x_12, x_27);
lean_dec(x_27);
x_29 = l_Lean_mkErrorStringWithPos(x_15, x_28, x_11, x_16);
lean_dec(x_11);
lean_dec(x_15);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_array_push(x_6, x_31);
x_33 = 1;
x_34 = lean_usize_add(x_3, x_33);
x_35 = lean_box(0);
x_3 = x_34;
x_5 = x_35;
x_6 = x_32;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_6);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_7);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_10 = l_Lean_PersistentArray_forMAux___at_Lake_loadTomlConfig___spec__4(x_1, x_9, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_loadTomlConfig___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_19 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__5(x_1, x_5, x_16, x_17, x_18, x_3, x_4);
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
x_34 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__6(x_1, x_20, x_31, x_32, x_33, x_3, x_4);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_loadTomlConfig___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_1);
x_6 = l_Lean_PersistentArray_forMAux___at_Lake_loadTomlConfig___spec__4(x_1, x_5, x_3, x_4);
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
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7(x_1, x_14, x_21, x_22, x_23, x_12, x_9);
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
x_38 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7(x_1, x_26, x_35, x_36, x_37, x_25, x_9);
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
x_56 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7(x_1, x_42, x_53, x_54, x_55, x_40, x_39);
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
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_PersistentArray_forM___at_Lake_loadTomlConfig___spec__3(x_2, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__9(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_6, 1);
lean_dec(x_10);
x_11 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_6, 1, x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_mk_array(x_12, x_6);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_16 = l_Lake_mergeErrors___rarg(x_4, x_14, x_15);
x_2 = x_8;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_array(x_21, x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_25 = l_Lake_mergeErrors___rarg(x_4, x_23, x_24);
x_2 = x_8;
x_4 = x_25;
goto _start;
}
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_mk_array(x_30, x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_34 = l_Lake_mergeErrors___rarg(x_4, x_32, x_33);
x_2 = x_8;
x_4 = x_34;
goto _start;
}
case 3:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_mk_array(x_39, x_38);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_43 = l_Lake_mergeErrors___rarg(x_4, x_41, x_42);
x_2 = x_8;
x_4 = x_43;
goto _start;
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
lean_dec(x_6);
x_47 = l_Lake_Dependency_decodeToml(x_46, x_45);
x_48 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_49 = l_Lake_mergeErrors___rarg(x_4, x_47, x_48);
x_2 = x_8;
x_4 = x_49;
goto _start;
}
default: 
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_6, 1);
lean_dec(x_52);
x_53 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_53);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_mk_array(x_54, x_6);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_58 = l_Lake_mergeErrors___rarg(x_4, x_56, x_57);
x_2 = x_8;
x_4 = x_58;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_6, 0);
lean_inc(x_60);
lean_dec(x_6);
x_61 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_mk_array(x_63, x_62);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_67 = l_Lake_mergeErrors___rarg(x_4, x_65, x_66);
x_2 = x_8;
x_4 = x_67;
goto _start;
}
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__8(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_2, x_2);
if (x_7 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__9(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_9 = l_Lake_RBArray_insert___rarg(x_8, x_4, x_7, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_6, 1);
lean_dec(x_10);
x_11 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_6, 1, x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_mk_array(x_12, x_6);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_16 = l_Lake_mergeErrors___rarg(x_4, x_14, x_15);
x_2 = x_8;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_array(x_21, x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_25 = l_Lake_mergeErrors___rarg(x_4, x_23, x_24);
x_2 = x_8;
x_4 = x_25;
goto _start;
}
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_mk_array(x_30, x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_34 = l_Lake_mergeErrors___rarg(x_4, x_32, x_33);
x_2 = x_8;
x_4 = x_34;
goto _start;
}
case 3:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_mk_array(x_39, x_38);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_43 = l_Lake_mergeErrors___rarg(x_4, x_41, x_42);
x_2 = x_8;
x_4 = x_43;
goto _start;
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
lean_dec(x_6);
x_47 = l_Lake_LeanExeConfig_decodeToml(x_46, x_45);
x_48 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_49 = l_Lake_mergeErrors___rarg(x_4, x_47, x_48);
x_2 = x_8;
x_4 = x_49;
goto _start;
}
default: 
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_6, 1);
lean_dec(x_52);
x_53 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_53);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_mk_array(x_54, x_6);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_58 = l_Lake_mergeErrors___rarg(x_4, x_56, x_57);
x_2 = x_8;
x_4 = x_58;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_6, 0);
lean_inc(x_60);
lean_dec(x_6);
x_61 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_mk_array(x_63, x_62);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_67 = l_Lake_mergeErrors___rarg(x_4, x_65, x_66);
x_2 = x_8;
x_4 = x_67;
goto _start;
}
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__11(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_2, x_2);
if (x_7 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__12(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_9 = l_Lake_RBArray_insert___rarg(x_8, x_4, x_7, x_6);
x_10 = 1;
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__15(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_6, 1);
lean_dec(x_10);
x_11 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set(x_6, 1, x_11);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_mk_array(x_12, x_6);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_16 = l_Lake_mergeErrors___rarg(x_4, x_14, x_15);
x_2 = x_8;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_6, 0);
lean_inc(x_18);
lean_dec(x_6);
x_19 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_mk_array(x_21, x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_25 = l_Lake_mergeErrors___rarg(x_4, x_23, x_24);
x_2 = x_8;
x_4 = x_25;
goto _start;
}
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_mk_array(x_30, x_29);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_34 = l_Lake_mergeErrors___rarg(x_4, x_32, x_33);
x_2 = x_8;
x_4 = x_34;
goto _start;
}
case 3:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_mk_array(x_39, x_38);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_43 = l_Lake_mergeErrors___rarg(x_4, x_41, x_42);
x_2 = x_8;
x_4 = x_43;
goto _start;
}
case 6:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_6, 1);
lean_inc(x_46);
lean_dec(x_6);
x_47 = l_Lake_LeanLibConfig_decodeToml(x_46, x_45);
x_48 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_49 = l_Lake_mergeErrors___rarg(x_4, x_47, x_48);
x_2 = x_8;
x_4 = x_49;
goto _start;
}
default: 
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_6);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_6, 1);
lean_dec(x_52);
x_53 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_53);
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_mk_array(x_54, x_6);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_58 = l_Lake_mergeErrors___rarg(x_4, x_56, x_57);
x_2 = x_8;
x_4 = x_58;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_6, 0);
lean_inc(x_60);
lean_dec(x_6);
x_61 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_mk_array(x_63, x_62);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_67 = l_Lake_mergeErrors___rarg(x_4, x_65, x_66);
x_2 = x_8;
x_4 = x_67;
goto _start;
}
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__14(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_2);
if (x_6 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_2, x_2);
if (x_7 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_2);
lean_dec(x_2);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__15(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = l_Lean_Message_toString(x_1, x_4, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = 3;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_array_push(x_2, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = 3;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_array_push(x_2, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_io_error_to_string(x_22);
x_24 = 3;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_array_get_size(x_2);
x_27 = lean_array_push(x_2, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_io_error_to_string(x_29);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_array_get_size(x_2);
x_35 = lean_array_push(x_2, x_33);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_30);
return x_37;
}
}
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_loadTomlConfig___lambda__1), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("require", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_loadTomlConfig___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultTargets", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_loadTomlConfig___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_exe", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_loadTomlConfig___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_loadTomlConfig___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_3 = l_Lake_PackageConfig_decodeToml___closed__7;
x_4 = lean_box(0);
x_5 = l_Lake_LeanOption_decodeToml___closed__4;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_1);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_5);
lean_ctor_set(x_7, 6, x_5);
lean_ctor_set(x_7, 7, x_2);
lean_ctor_set(x_7, 8, x_2);
lean_ctor_set(x_7, 9, x_2);
lean_ctor_set(x_7, 10, x_2);
lean_ctor_set(x_7, 11, x_2);
lean_ctor_set(x_7, 12, x_2);
lean_ctor_set(x_7, 13, x_1);
lean_ctor_set(x_7, 14, x_1);
lean_ctor_set(x_7, 15, x_1);
lean_ctor_set(x_7, 16, x_2);
lean_ctor_set(x_7, 17, x_2);
lean_ctor_set(x_7, 18, x_5);
lean_ctor_set(x_7, 19, x_2);
lean_ctor_set(x_7, 20, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*21, x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*21 + 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_667; 
lean_inc(x_3);
lean_inc(x_1);
x_6 = l_System_FilePath_join(x_1, x_3);
x_667 = l_IO_FS_readFile(x_6, x_5);
lean_dec(x_6);
if (lean_obj_tag(x_667) == 0)
{
uint8_t x_668; 
x_668 = !lean_is_exclusive(x_667);
if (x_668 == 0)
{
lean_object* x_669; 
x_669 = lean_ctor_get(x_667, 1);
lean_ctor_set(x_667, 1, x_4);
x_7 = x_667;
x_8 = x_669;
goto block_666;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_667, 0);
x_671 = lean_ctor_get(x_667, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_667);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_4);
x_7 = x_672;
x_8 = x_671;
goto block_666;
}
}
else
{
uint8_t x_673; 
x_673 = !lean_is_exclusive(x_667);
if (x_673 == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; uint8_t x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_674 = lean_ctor_get(x_667, 0);
x_675 = lean_ctor_get(x_667, 1);
x_676 = lean_io_error_to_string(x_674);
x_677 = 3;
x_678 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set_uint8(x_678, sizeof(void*)*1, x_677);
x_679 = lean_array_get_size(x_4);
x_680 = lean_array_push(x_4, x_678);
lean_ctor_set(x_667, 1, x_680);
lean_ctor_set(x_667, 0, x_679);
x_7 = x_667;
x_8 = x_675;
goto block_666;
}
else
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; 
x_681 = lean_ctor_get(x_667, 0);
x_682 = lean_ctor_get(x_667, 1);
lean_inc(x_682);
lean_inc(x_681);
lean_dec(x_667);
x_683 = lean_io_error_to_string(x_681);
x_684 = 3;
x_685 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_685, 0, x_683);
lean_ctor_set_uint8(x_685, sizeof(void*)*1, x_684);
x_686 = lean_array_get_size(x_4);
x_687 = lean_array_push(x_4, x_685);
x_688 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_688, 0, x_686);
lean_ctor_set(x_688, 1, x_687);
x_7 = x_688;
x_8 = x_682;
goto block_666;
}
}
block_666:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_358; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = 1;
lean_inc(x_3);
x_12 = l_Lean_Parser_mkInputContext(x_10, x_3, x_11);
lean_inc(x_12);
x_358 = l_Lake_Toml_loadToml(x_12, x_8);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_359);
lean_ctor_set(x_7, 0, x_361);
x_13 = x_7;
x_14 = x_360;
goto block_357;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_358, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_358, 1);
lean_inc(x_363);
lean_dec(x_358);
x_364 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_7, 0, x_364);
x_13 = x_7;
x_14 = x_363;
goto block_357;
}
block_357:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
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
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_array_get_size(x_16);
x_51 = l_Lake_loadTomlConfig___closed__1;
x_52 = l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(x_49, x_51, x_16, x_14);
lean_dec(x_49);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_53, 0);
lean_dec(x_57);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_50);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_50);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_52, 0, x_59);
return x_52;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_dec(x_52);
x_61 = lean_ctor_get(x_53, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_62 = x_53;
} else {
 lean_dec_ref(x_53);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
 lean_ctor_set_tag(x_63, 1);
}
lean_ctor_set(x_63, 0, x_50);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
return x_64;
}
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_52);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_52, 0);
lean_dec(x_66);
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_53, 0);
lean_dec(x_68);
lean_ctor_set(x_53, 0, x_50);
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_53, 1);
lean_inc(x_69);
lean_dec(x_53);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_50);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_52, 0, x_70);
return x_52;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_52, 1);
lean_inc(x_71);
lean_dec(x_52);
x_72 = lean_ctor_get(x_53, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_73 = x_53;
} else {
 lean_dec_ref(x_53);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_50);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_71);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_50);
x_76 = !lean_is_exclusive(x_52);
if (x_76 == 0)
{
return x_52;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_52, 0);
x_78 = lean_ctor_get(x_52, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_52);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_349; lean_object* x_350; 
x_80 = lean_ctor_get(x_15, 0);
lean_inc(x_80);
lean_dec(x_15);
x_349 = lean_box(0);
lean_inc(x_80);
x_350 = l_Lake_PackageConfig_decodeToml(x_80, x_349);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec(x_350);
x_352 = l_Lake_LeanOption_decodeToml___closed__4;
x_353 = l_Array_append___rarg(x_352, x_351);
lean_dec(x_351);
x_354 = l_Lake_loadTomlConfig___closed__10;
x_81 = x_354;
x_82 = x_353;
goto block_348;
}
else
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_350, 0);
lean_inc(x_355);
lean_dec(x_350);
x_356 = l_Lake_LeanOption_decodeToml___closed__4;
x_81 = x_355;
x_82 = x_356;
goto block_348;
}
block_348:
{
lean_object* x_83; lean_object* x_84; lean_object* x_282; lean_object* x_283; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_295 = l_Lake_loadTomlConfig___closed__9;
lean_inc(x_80);
x_296 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_294, x_295, x_80);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; 
x_297 = l_Lake_LeanOption_decodeToml___closed__4;
x_282 = x_297;
x_283 = x_82;
goto block_293;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_296, 0);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
switch (lean_obj_tag(x_299)) {
case 0:
{
uint8_t x_300; 
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_301 = lean_ctor_get(x_299, 1);
lean_dec(x_301);
x_302 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_299, 1, x_302);
x_303 = lean_unsigned_to_nat(1u);
x_304 = lean_mk_array(x_303, x_299);
x_305 = l_Array_append___rarg(x_82, x_304);
lean_dec(x_304);
x_306 = l_Lake_LeanOption_decodeToml___closed__4;
x_282 = x_306;
x_283 = x_305;
goto block_293;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_307 = lean_ctor_get(x_299, 0);
lean_inc(x_307);
lean_dec(x_299);
x_308 = l_Lake_LeanConfig_decodeToml___closed__5;
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_unsigned_to_nat(1u);
x_311 = lean_mk_array(x_310, x_309);
x_312 = l_Array_append___rarg(x_82, x_311);
lean_dec(x_311);
x_313 = l_Lake_LeanOption_decodeToml___closed__4;
x_282 = x_313;
x_283 = x_312;
goto block_293;
}
}
case 2:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_314 = lean_ctor_get(x_299, 0);
lean_inc(x_314);
lean_dec(x_299);
x_315 = l_Lake_LeanConfig_decodeToml___closed__5;
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_unsigned_to_nat(1u);
x_318 = lean_mk_array(x_317, x_316);
x_319 = l_Array_append___rarg(x_82, x_318);
lean_dec(x_318);
x_320 = l_Lake_LeanOption_decodeToml___closed__4;
x_282 = x_320;
x_283 = x_319;
goto block_293;
}
case 3:
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_321 = lean_ctor_get(x_299, 0);
lean_inc(x_321);
lean_dec(x_299);
x_322 = l_Lake_LeanConfig_decodeToml___closed__5;
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_unsigned_to_nat(1u);
x_325 = lean_mk_array(x_324, x_323);
x_326 = l_Array_append___rarg(x_82, x_325);
lean_dec(x_325);
x_327 = l_Lake_LeanOption_decodeToml___closed__4;
x_282 = x_327;
x_283 = x_326;
goto block_293;
}
case 5:
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_299, 1);
lean_inc(x_328);
lean_dec(x_299);
x_329 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__14(x_328);
lean_dec(x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
lean_dec(x_329);
x_331 = l_Array_append___rarg(x_82, x_330);
lean_dec(x_330);
x_332 = l_Lake_LeanOption_decodeToml___closed__4;
x_282 = x_332;
x_283 = x_331;
goto block_293;
}
else
{
lean_object* x_333; 
x_333 = lean_ctor_get(x_329, 0);
lean_inc(x_333);
lean_dec(x_329);
x_282 = x_333;
x_283 = x_82;
goto block_293;
}
}
default: 
{
uint8_t x_334; 
x_334 = !lean_is_exclusive(x_299);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_335 = lean_ctor_get(x_299, 1);
lean_dec(x_335);
x_336 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_299, 0);
lean_ctor_set(x_299, 1, x_336);
x_337 = lean_unsigned_to_nat(1u);
x_338 = lean_mk_array(x_337, x_299);
x_339 = l_Array_append___rarg(x_82, x_338);
lean_dec(x_338);
x_340 = l_Lake_LeanOption_decodeToml___closed__4;
x_282 = x_340;
x_283 = x_339;
goto block_293;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_341 = lean_ctor_get(x_299, 0);
lean_inc(x_341);
lean_dec(x_299);
x_342 = l_Lake_LeanConfig_decodeToml___closed__5;
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
x_344 = lean_unsigned_to_nat(1u);
x_345 = lean_mk_array(x_344, x_343);
x_346 = l_Array_append___rarg(x_82, x_345);
lean_dec(x_345);
x_347 = l_Lake_LeanOption_decodeToml___closed__4;
x_282 = x_347;
x_283 = x_346;
goto block_293;
}
}
}
}
block_281:
{
lean_object* x_85; lean_object* x_86; lean_object* x_215; lean_object* x_216; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_227 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_228 = l_Lake_loadTomlConfig___closed__7;
lean_inc(x_80);
x_229 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_227, x_228, x_80);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; 
x_230 = l_Lake_LeanOption_decodeToml___closed__4;
x_215 = x_230;
x_216 = x_84;
goto block_226;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_ctor_get(x_229, 0);
lean_inc(x_231);
lean_dec(x_229);
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
lean_dec(x_231);
switch (lean_obj_tag(x_232)) {
case 0:
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_232);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_232, 1);
lean_dec(x_234);
x_235 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_232, 1, x_235);
x_236 = lean_unsigned_to_nat(1u);
x_237 = lean_mk_array(x_236, x_232);
x_238 = l_Array_append___rarg(x_84, x_237);
lean_dec(x_237);
x_239 = l_Lake_LeanOption_decodeToml___closed__4;
x_215 = x_239;
x_216 = x_238;
goto block_226;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_240 = lean_ctor_get(x_232, 0);
lean_inc(x_240);
lean_dec(x_232);
x_241 = l_Lake_LeanConfig_decodeToml___closed__5;
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_unsigned_to_nat(1u);
x_244 = lean_mk_array(x_243, x_242);
x_245 = l_Array_append___rarg(x_84, x_244);
lean_dec(x_244);
x_246 = l_Lake_LeanOption_decodeToml___closed__4;
x_215 = x_246;
x_216 = x_245;
goto block_226;
}
}
case 2:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_247 = lean_ctor_get(x_232, 0);
lean_inc(x_247);
lean_dec(x_232);
x_248 = l_Lake_LeanConfig_decodeToml___closed__5;
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_unsigned_to_nat(1u);
x_251 = lean_mk_array(x_250, x_249);
x_252 = l_Array_append___rarg(x_84, x_251);
lean_dec(x_251);
x_253 = l_Lake_LeanOption_decodeToml___closed__4;
x_215 = x_253;
x_216 = x_252;
goto block_226;
}
case 3:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_254 = lean_ctor_get(x_232, 0);
lean_inc(x_254);
lean_dec(x_232);
x_255 = l_Lake_LeanConfig_decodeToml___closed__5;
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_unsigned_to_nat(1u);
x_258 = lean_mk_array(x_257, x_256);
x_259 = l_Array_append___rarg(x_84, x_258);
lean_dec(x_258);
x_260 = l_Lake_LeanOption_decodeToml___closed__4;
x_215 = x_260;
x_216 = x_259;
goto block_226;
}
case 5:
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_232, 1);
lean_inc(x_261);
lean_dec(x_232);
x_262 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__11(x_261);
lean_dec(x_261);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec(x_262);
x_264 = l_Array_append___rarg(x_84, x_263);
lean_dec(x_263);
x_265 = l_Lake_LeanOption_decodeToml___closed__4;
x_215 = x_265;
x_216 = x_264;
goto block_226;
}
else
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_262, 0);
lean_inc(x_266);
lean_dec(x_262);
x_215 = x_266;
x_216 = x_84;
goto block_226;
}
}
default: 
{
uint8_t x_267; 
x_267 = !lean_is_exclusive(x_232);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_268 = lean_ctor_get(x_232, 1);
lean_dec(x_268);
x_269 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_232, 0);
lean_ctor_set(x_232, 1, x_269);
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_mk_array(x_270, x_232);
x_272 = l_Array_append___rarg(x_84, x_271);
lean_dec(x_271);
x_273 = l_Lake_LeanOption_decodeToml___closed__4;
x_215 = x_273;
x_216 = x_272;
goto block_226;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_274 = lean_ctor_get(x_232, 0);
lean_inc(x_274);
lean_dec(x_232);
x_275 = l_Lake_LeanConfig_decodeToml___closed__5;
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_unsigned_to_nat(1u);
x_278 = lean_mk_array(x_277, x_276);
x_279 = l_Array_append___rarg(x_84, x_278);
lean_dec(x_278);
x_280 = l_Lake_LeanOption_decodeToml___closed__4;
x_215 = x_280;
x_216 = x_279;
goto block_226;
}
}
}
}
block_214:
{
lean_object* x_87; lean_object* x_88; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_161 = l_Lake_loadTomlConfig___closed__5;
lean_inc(x_80);
x_162 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_160, x_161, x_80);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = l_Lake_LeanOption_decodeToml___closed__4;
x_87 = x_163;
x_88 = x_86;
goto block_159;
}
else
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_162, 0);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
switch (lean_obj_tag(x_165)) {
case 0:
{
uint8_t x_166; 
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_165, 1);
lean_dec(x_167);
x_168 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_165, 1, x_168);
x_169 = lean_unsigned_to_nat(1u);
x_170 = lean_mk_array(x_169, x_165);
x_171 = l_Array_append___rarg(x_86, x_170);
lean_dec(x_170);
x_172 = l_Lake_LeanOption_decodeToml___closed__4;
x_87 = x_172;
x_88 = x_171;
goto block_159;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_173 = lean_ctor_get(x_165, 0);
lean_inc(x_173);
lean_dec(x_165);
x_174 = l_Lake_LeanConfig_decodeToml___closed__5;
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_unsigned_to_nat(1u);
x_177 = lean_mk_array(x_176, x_175);
x_178 = l_Array_append___rarg(x_86, x_177);
lean_dec(x_177);
x_179 = l_Lake_LeanOption_decodeToml___closed__4;
x_87 = x_179;
x_88 = x_178;
goto block_159;
}
}
case 2:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_180 = lean_ctor_get(x_165, 0);
lean_inc(x_180);
lean_dec(x_165);
x_181 = l_Lake_LeanConfig_decodeToml___closed__5;
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_180);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_mk_array(x_183, x_182);
x_185 = l_Array_append___rarg(x_86, x_184);
lean_dec(x_184);
x_186 = l_Lake_LeanOption_decodeToml___closed__4;
x_87 = x_186;
x_88 = x_185;
goto block_159;
}
case 3:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_187 = lean_ctor_get(x_165, 0);
lean_inc(x_187);
lean_dec(x_165);
x_188 = l_Lake_LeanConfig_decodeToml___closed__5;
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_mk_array(x_190, x_189);
x_192 = l_Array_append___rarg(x_86, x_191);
lean_dec(x_191);
x_193 = l_Lake_LeanOption_decodeToml___closed__4;
x_87 = x_193;
x_88 = x_192;
goto block_159;
}
case 5:
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_165, 1);
lean_inc(x_194);
lean_dec(x_165);
x_195 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(x_194);
lean_dec(x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
lean_dec(x_195);
x_197 = l_Array_append___rarg(x_86, x_196);
lean_dec(x_196);
x_198 = l_Lake_LeanOption_decodeToml___closed__4;
x_87 = x_198;
x_88 = x_197;
goto block_159;
}
else
{
lean_object* x_199; 
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
lean_dec(x_195);
x_87 = x_199;
x_88 = x_86;
goto block_159;
}
}
default: 
{
uint8_t x_200; 
x_200 = !lean_is_exclusive(x_165);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_201 = lean_ctor_get(x_165, 1);
lean_dec(x_201);
x_202 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_165, 0);
lean_ctor_set(x_165, 1, x_202);
x_203 = lean_unsigned_to_nat(1u);
x_204 = lean_mk_array(x_203, x_165);
x_205 = l_Array_append___rarg(x_86, x_204);
lean_dec(x_204);
x_206 = l_Lake_LeanOption_decodeToml___closed__4;
x_87 = x_206;
x_88 = x_205;
goto block_159;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_207 = lean_ctor_get(x_165, 0);
lean_inc(x_207);
lean_dec(x_165);
x_208 = l_Lake_LeanConfig_decodeToml___closed__5;
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_mk_array(x_210, x_209);
x_212 = l_Array_append___rarg(x_86, x_211);
lean_dec(x_211);
x_213 = l_Lake_LeanOption_decodeToml___closed__4;
x_87 = x_213;
x_88 = x_212;
goto block_159;
}
}
}
}
block_159:
{
lean_object* x_89; lean_object* x_90; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_106 = l_Lake_loadTomlConfig___closed__3;
x_107 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_105, x_106, x_80);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = l_Lake_LeanOption_decodeToml___closed__4;
x_89 = x_108;
x_90 = x_88;
goto block_104;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
switch (lean_obj_tag(x_110)) {
case 0:
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_112 = lean_ctor_get(x_110, 1);
lean_dec(x_112);
x_113 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_110, 1, x_113);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_mk_array(x_114, x_110);
x_116 = l_Array_append___rarg(x_88, x_115);
lean_dec(x_115);
x_117 = l_Lake_LeanOption_decodeToml___closed__4;
x_89 = x_117;
x_90 = x_116;
goto block_104;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_118 = lean_ctor_get(x_110, 0);
lean_inc(x_118);
lean_dec(x_110);
x_119 = l_Lake_LeanConfig_decodeToml___closed__5;
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_mk_array(x_121, x_120);
x_123 = l_Array_append___rarg(x_88, x_122);
lean_dec(x_122);
x_124 = l_Lake_LeanOption_decodeToml___closed__4;
x_89 = x_124;
x_90 = x_123;
goto block_104;
}
}
case 2:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_125 = lean_ctor_get(x_110, 0);
lean_inc(x_125);
lean_dec(x_110);
x_126 = l_Lake_LeanConfig_decodeToml___closed__5;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_mk_array(x_128, x_127);
x_130 = l_Array_append___rarg(x_88, x_129);
lean_dec(x_129);
x_131 = l_Lake_LeanOption_decodeToml___closed__4;
x_89 = x_131;
x_90 = x_130;
goto block_104;
}
case 3:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_132 = lean_ctor_get(x_110, 0);
lean_inc(x_132);
lean_dec(x_110);
x_133 = l_Lake_LeanConfig_decodeToml___closed__5;
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_mk_array(x_135, x_134);
x_137 = l_Array_append___rarg(x_88, x_136);
lean_dec(x_136);
x_138 = l_Lake_LeanOption_decodeToml___closed__4;
x_89 = x_138;
x_90 = x_137;
goto block_104;
}
case 5:
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_110, 1);
lean_inc(x_139);
lean_dec(x_110);
x_140 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__8(x_139);
lean_dec(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec(x_140);
x_142 = l_Array_append___rarg(x_88, x_141);
lean_dec(x_141);
x_143 = l_Lake_LeanOption_decodeToml___closed__4;
x_89 = x_143;
x_90 = x_142;
goto block_104;
}
else
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_140, 0);
lean_inc(x_144);
lean_dec(x_140);
x_89 = x_144;
x_90 = x_88;
goto block_104;
}
}
default: 
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_110);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_146 = lean_ctor_get(x_110, 1);
lean_dec(x_146);
x_147 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_110, 0);
lean_ctor_set(x_110, 1, x_147);
x_148 = lean_unsigned_to_nat(1u);
x_149 = lean_mk_array(x_148, x_110);
x_150 = l_Array_append___rarg(x_88, x_149);
lean_dec(x_149);
x_151 = l_Lake_LeanOption_decodeToml___closed__4;
x_89 = x_151;
x_90 = x_150;
goto block_104;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_152 = lean_ctor_get(x_110, 0);
lean_inc(x_152);
lean_dec(x_110);
x_153 = l_Lake_LeanConfig_decodeToml___closed__5;
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_mk_array(x_155, x_154);
x_157 = l_Array_append___rarg(x_88, x_156);
lean_dec(x_156);
x_158 = l_Lake_LeanOption_decodeToml___closed__4;
x_89 = x_158;
x_90 = x_157;
goto block_104;
}
}
}
}
block_104:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_81, 3);
lean_inc(x_91);
x_92 = lean_box(0);
x_93 = lean_box(0);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_81, 17);
lean_inc(x_94);
x_95 = lean_ctor_get(x_81, 19);
lean_inc(x_95);
x_96 = l_Lake_defaultManifestFile;
x_97 = l_Lake_LeanOption_decodeToml___closed__4;
x_98 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_2);
lean_ctor_set(x_98, 2, x_81);
lean_ctor_set(x_98, 3, x_3);
lean_ctor_set(x_98, 4, x_96);
lean_ctor_set(x_98, 5, x_92);
lean_ctor_set(x_98, 6, x_97);
lean_ctor_set(x_98, 7, x_89);
lean_ctor_set(x_98, 8, x_83);
lean_ctor_set(x_98, 9, x_85);
lean_ctor_set(x_98, 10, x_93);
lean_ctor_set(x_98, 11, x_93);
lean_ctor_set(x_98, 12, x_87);
lean_ctor_set(x_98, 13, x_93);
lean_ctor_set(x_98, 14, x_97);
lean_ctor_set(x_98, 15, x_97);
lean_ctor_set(x_98, 16, x_94);
lean_ctor_set(x_98, 17, x_95);
x_18 = x_98;
x_19 = x_90;
goto block_48;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_81, 17);
lean_inc(x_99);
x_100 = lean_ctor_get(x_81, 19);
lean_inc(x_100);
x_101 = lean_ctor_get(x_91, 0);
lean_inc(x_101);
lean_dec(x_91);
x_102 = l_Lake_LeanOption_decodeToml___closed__4;
x_103 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_2);
lean_ctor_set(x_103, 2, x_81);
lean_ctor_set(x_103, 3, x_3);
lean_ctor_set(x_103, 4, x_101);
lean_ctor_set(x_103, 5, x_92);
lean_ctor_set(x_103, 6, x_102);
lean_ctor_set(x_103, 7, x_89);
lean_ctor_set(x_103, 8, x_83);
lean_ctor_set(x_103, 9, x_85);
lean_ctor_set(x_103, 10, x_93);
lean_ctor_set(x_103, 11, x_93);
lean_ctor_set(x_103, 12, x_87);
lean_ctor_set(x_103, 13, x_93);
lean_ctor_set(x_103, 14, x_102);
lean_ctor_set(x_103, 15, x_102);
lean_ctor_set(x_103, 16, x_99);
lean_ctor_set(x_103, 17, x_100);
x_18 = x_103;
x_19 = x_90;
goto block_48;
}
}
}
}
block_226:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_217 = lean_array_get_size(x_215);
x_218 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_219 = l_Lake_RBArray_mkEmpty___rarg(x_218, x_217);
x_220 = lean_unsigned_to_nat(0u);
x_221 = lean_nat_dec_lt(x_220, x_217);
if (x_221 == 0)
{
lean_dec(x_217);
lean_dec(x_215);
x_85 = x_219;
x_86 = x_216;
goto block_214;
}
else
{
uint8_t x_222; 
x_222 = lean_nat_dec_le(x_217, x_217);
if (x_222 == 0)
{
lean_dec(x_217);
lean_dec(x_215);
x_85 = x_219;
x_86 = x_216;
goto block_214;
}
else
{
size_t x_223; size_t x_224; lean_object* x_225; 
x_223 = 0;
x_224 = lean_usize_of_nat(x_217);
lean_dec(x_217);
x_225 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10(x_215, x_223, x_224, x_219);
lean_dec(x_215);
x_85 = x_225;
x_86 = x_216;
goto block_214;
}
}
}
}
block_293:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
x_284 = lean_array_get_size(x_282);
x_285 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_286 = l_Lake_RBArray_mkEmpty___rarg(x_285, x_284);
x_287 = lean_unsigned_to_nat(0u);
x_288 = lean_nat_dec_lt(x_287, x_284);
if (x_288 == 0)
{
lean_dec(x_284);
lean_dec(x_282);
x_83 = x_286;
x_84 = x_283;
goto block_281;
}
else
{
uint8_t x_289; 
x_289 = lean_nat_dec_le(x_284, x_284);
if (x_289 == 0)
{
lean_dec(x_284);
lean_dec(x_282);
x_83 = x_286;
x_84 = x_283;
goto block_281;
}
else
{
size_t x_290; size_t x_291; lean_object* x_292; 
x_290 = 0;
x_291 = lean_usize_of_nat(x_284);
lean_dec(x_284);
x_292 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13(x_282, x_290, x_291, x_286);
lean_dec(x_282);
x_83 = x_292;
x_84 = x_283;
goto block_281;
}
}
}
}
}
block_48:
{
uint8_t x_20; 
x_20 = l_Array_isEmpty___rarg(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_18);
x_21 = lean_array_get_size(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
x_24 = lean_array_get_size(x_16);
if (x_23 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_12);
if (lean_is_scalar(x_17)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_17;
 lean_ctor_set_tag(x_25, 1);
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_14);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_21, x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_12);
if (lean_is_scalar(x_17)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_17;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_16);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_14);
return x_29;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_17);
x_30 = 0;
x_31 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_32 = lean_box(0);
x_33 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1(x_12, x_19, x_30, x_31, x_32, x_16, x_14);
lean_dec(x_19);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_24);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_33, 0, x_39);
return x_33;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
 lean_ctor_set_tag(x_44, 1);
}
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
return x_45;
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_19);
lean_dec(x_12);
if (lean_is_scalar(x_17)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_17;
}
lean_ctor_set(x_46, 0, x_18);
lean_ctor_set(x_46, 1, x_16);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_14);
return x_47;
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_651; 
x_365 = lean_ctor_get(x_7, 0);
x_366 = lean_ctor_get(x_7, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_7);
x_367 = 1;
lean_inc(x_3);
x_368 = l_Lean_Parser_mkInputContext(x_365, x_3, x_367);
lean_inc(x_368);
x_651 = l_Lake_Toml_loadToml(x_368, x_8);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
x_653 = lean_ctor_get(x_651, 1);
lean_inc(x_653);
lean_dec(x_651);
x_654 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_654, 0, x_652);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_366);
x_369 = x_655;
x_370 = x_653;
goto block_650;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_656 = lean_ctor_get(x_651, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_651, 1);
lean_inc(x_657);
lean_dec(x_651);
x_658 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_658, 0, x_656);
x_659 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_659, 0, x_658);
lean_ctor_set(x_659, 1, x_366);
x_369 = x_659;
x_370 = x_657;
goto block_650;
}
block_650:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_371 = lean_ctor_get(x_369, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_369, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 x_373 = x_369;
} else {
 lean_dec_ref(x_369);
 x_373 = lean_box(0);
}
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_373);
lean_dec(x_368);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_400 = lean_ctor_get(x_371, 0);
lean_inc(x_400);
lean_dec(x_371);
x_401 = lean_array_get_size(x_372);
x_402 = l_Lake_loadTomlConfig___closed__1;
x_403 = l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(x_400, x_402, x_372, x_370);
lean_dec(x_400);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_406 = x_403;
} else {
 lean_dec_ref(x_403);
 x_406 = lean_box(0);
}
x_407 = lean_ctor_get(x_404, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_408 = x_404;
} else {
 lean_dec_ref(x_404);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 2, 0);
} else {
 x_409 = x_408;
 lean_ctor_set_tag(x_409, 1);
}
lean_ctor_set(x_409, 0, x_401);
lean_ctor_set(x_409, 1, x_407);
if (lean_is_scalar(x_406)) {
 x_410 = lean_alloc_ctor(0, 2, 0);
} else {
 x_410 = x_406;
}
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_405);
return x_410;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_411 = lean_ctor_get(x_403, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_412 = x_403;
} else {
 lean_dec_ref(x_403);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_404, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_414 = x_404;
} else {
 lean_dec_ref(x_404);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_401);
lean_ctor_set(x_415, 1, x_413);
if (lean_is_scalar(x_412)) {
 x_416 = lean_alloc_ctor(0, 2, 0);
} else {
 x_416 = x_412;
}
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_411);
return x_416;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_401);
x_417 = lean_ctor_get(x_403, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_403, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_419 = x_403;
} else {
 lean_dec_ref(x_403);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_642; lean_object* x_643; 
x_421 = lean_ctor_get(x_371, 0);
lean_inc(x_421);
lean_dec(x_371);
x_642 = lean_box(0);
lean_inc(x_421);
x_643 = l_Lake_PackageConfig_decodeToml(x_421, x_642);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
lean_dec(x_643);
x_645 = l_Lake_LeanOption_decodeToml___closed__4;
x_646 = l_Array_append___rarg(x_645, x_644);
lean_dec(x_644);
x_647 = l_Lake_loadTomlConfig___closed__10;
x_422 = x_647;
x_423 = x_646;
goto block_641;
}
else
{
lean_object* x_648; lean_object* x_649; 
x_648 = lean_ctor_get(x_643, 0);
lean_inc(x_648);
lean_dec(x_643);
x_649 = l_Lake_LeanOption_decodeToml___closed__4;
x_422 = x_648;
x_423 = x_649;
goto block_641;
}
block_641:
{
lean_object* x_424; lean_object* x_425; lean_object* x_587; lean_object* x_588; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_599 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_600 = l_Lake_loadTomlConfig___closed__9;
lean_inc(x_421);
x_601 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_599, x_600, x_421);
if (lean_obj_tag(x_601) == 0)
{
lean_object* x_602; 
x_602 = l_Lake_LeanOption_decodeToml___closed__4;
x_587 = x_602;
x_588 = x_423;
goto block_598;
}
else
{
lean_object* x_603; lean_object* x_604; 
x_603 = lean_ctor_get(x_601, 0);
lean_inc(x_603);
lean_dec(x_601);
x_604 = lean_ctor_get(x_603, 1);
lean_inc(x_604);
lean_dec(x_603);
switch (lean_obj_tag(x_604)) {
case 0:
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_606 = x_604;
} else {
 lean_dec_ref(x_604);
 x_606 = lean_box(0);
}
x_607 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_606)) {
 x_608 = lean_alloc_ctor(0, 2, 0);
} else {
 x_608 = x_606;
}
lean_ctor_set(x_608, 0, x_605);
lean_ctor_set(x_608, 1, x_607);
x_609 = lean_unsigned_to_nat(1u);
x_610 = lean_mk_array(x_609, x_608);
x_611 = l_Array_append___rarg(x_423, x_610);
lean_dec(x_610);
x_612 = l_Lake_LeanOption_decodeToml___closed__4;
x_587 = x_612;
x_588 = x_611;
goto block_598;
}
case 2:
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_613 = lean_ctor_get(x_604, 0);
lean_inc(x_613);
lean_dec(x_604);
x_614 = l_Lake_LeanConfig_decodeToml___closed__5;
x_615 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
x_616 = lean_unsigned_to_nat(1u);
x_617 = lean_mk_array(x_616, x_615);
x_618 = l_Array_append___rarg(x_423, x_617);
lean_dec(x_617);
x_619 = l_Lake_LeanOption_decodeToml___closed__4;
x_587 = x_619;
x_588 = x_618;
goto block_598;
}
case 3:
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_620 = lean_ctor_get(x_604, 0);
lean_inc(x_620);
lean_dec(x_604);
x_621 = l_Lake_LeanConfig_decodeToml___closed__5;
x_622 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_622, 0, x_620);
lean_ctor_set(x_622, 1, x_621);
x_623 = lean_unsigned_to_nat(1u);
x_624 = lean_mk_array(x_623, x_622);
x_625 = l_Array_append___rarg(x_423, x_624);
lean_dec(x_624);
x_626 = l_Lake_LeanOption_decodeToml___closed__4;
x_587 = x_626;
x_588 = x_625;
goto block_598;
}
case 5:
{
lean_object* x_627; lean_object* x_628; 
x_627 = lean_ctor_get(x_604, 1);
lean_inc(x_627);
lean_dec(x_604);
x_628 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__14(x_627);
lean_dec(x_627);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
lean_dec(x_628);
x_630 = l_Array_append___rarg(x_423, x_629);
lean_dec(x_629);
x_631 = l_Lake_LeanOption_decodeToml___closed__4;
x_587 = x_631;
x_588 = x_630;
goto block_598;
}
else
{
lean_object* x_632; 
x_632 = lean_ctor_get(x_628, 0);
lean_inc(x_632);
lean_dec(x_628);
x_587 = x_632;
x_588 = x_423;
goto block_598;
}
}
default: 
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_633 = lean_ctor_get(x_604, 0);
lean_inc(x_633);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_634 = x_604;
} else {
 lean_dec_ref(x_604);
 x_634 = lean_box(0);
}
x_635 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_634)) {
 x_636 = lean_alloc_ctor(0, 2, 0);
} else {
 x_636 = x_634;
 lean_ctor_set_tag(x_636, 0);
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_635);
x_637 = lean_unsigned_to_nat(1u);
x_638 = lean_mk_array(x_637, x_636);
x_639 = l_Array_append___rarg(x_423, x_638);
lean_dec(x_638);
x_640 = l_Lake_LeanOption_decodeToml___closed__4;
x_587 = x_640;
x_588 = x_639;
goto block_598;
}
}
}
block_586:
{
lean_object* x_426; lean_object* x_427; lean_object* x_532; lean_object* x_533; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_544 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_545 = l_Lake_loadTomlConfig___closed__7;
lean_inc(x_421);
x_546 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_544, x_545, x_421);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; 
x_547 = l_Lake_LeanOption_decodeToml___closed__4;
x_532 = x_547;
x_533 = x_425;
goto block_543;
}
else
{
lean_object* x_548; lean_object* x_549; 
x_548 = lean_ctor_get(x_546, 0);
lean_inc(x_548);
lean_dec(x_546);
x_549 = lean_ctor_get(x_548, 1);
lean_inc(x_549);
lean_dec(x_548);
switch (lean_obj_tag(x_549)) {
case 0:
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_551 = x_549;
} else {
 lean_dec_ref(x_549);
 x_551 = lean_box(0);
}
x_552 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_551)) {
 x_553 = lean_alloc_ctor(0, 2, 0);
} else {
 x_553 = x_551;
}
lean_ctor_set(x_553, 0, x_550);
lean_ctor_set(x_553, 1, x_552);
x_554 = lean_unsigned_to_nat(1u);
x_555 = lean_mk_array(x_554, x_553);
x_556 = l_Array_append___rarg(x_425, x_555);
lean_dec(x_555);
x_557 = l_Lake_LeanOption_decodeToml___closed__4;
x_532 = x_557;
x_533 = x_556;
goto block_543;
}
case 2:
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_558 = lean_ctor_get(x_549, 0);
lean_inc(x_558);
lean_dec(x_549);
x_559 = l_Lake_LeanConfig_decodeToml___closed__5;
x_560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
x_561 = lean_unsigned_to_nat(1u);
x_562 = lean_mk_array(x_561, x_560);
x_563 = l_Array_append___rarg(x_425, x_562);
lean_dec(x_562);
x_564 = l_Lake_LeanOption_decodeToml___closed__4;
x_532 = x_564;
x_533 = x_563;
goto block_543;
}
case 3:
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_565 = lean_ctor_get(x_549, 0);
lean_inc(x_565);
lean_dec(x_549);
x_566 = l_Lake_LeanConfig_decodeToml___closed__5;
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
x_568 = lean_unsigned_to_nat(1u);
x_569 = lean_mk_array(x_568, x_567);
x_570 = l_Array_append___rarg(x_425, x_569);
lean_dec(x_569);
x_571 = l_Lake_LeanOption_decodeToml___closed__4;
x_532 = x_571;
x_533 = x_570;
goto block_543;
}
case 5:
{
lean_object* x_572; lean_object* x_573; 
x_572 = lean_ctor_get(x_549, 1);
lean_inc(x_572);
lean_dec(x_549);
x_573 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__11(x_572);
lean_dec(x_572);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
lean_dec(x_573);
x_575 = l_Array_append___rarg(x_425, x_574);
lean_dec(x_574);
x_576 = l_Lake_LeanOption_decodeToml___closed__4;
x_532 = x_576;
x_533 = x_575;
goto block_543;
}
else
{
lean_object* x_577; 
x_577 = lean_ctor_get(x_573, 0);
lean_inc(x_577);
lean_dec(x_573);
x_532 = x_577;
x_533 = x_425;
goto block_543;
}
}
default: 
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_578 = lean_ctor_get(x_549, 0);
lean_inc(x_578);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 x_579 = x_549;
} else {
 lean_dec_ref(x_549);
 x_579 = lean_box(0);
}
x_580 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_579)) {
 x_581 = lean_alloc_ctor(0, 2, 0);
} else {
 x_581 = x_579;
 lean_ctor_set_tag(x_581, 0);
}
lean_ctor_set(x_581, 0, x_578);
lean_ctor_set(x_581, 1, x_580);
x_582 = lean_unsigned_to_nat(1u);
x_583 = lean_mk_array(x_582, x_581);
x_584 = l_Array_append___rarg(x_425, x_583);
lean_dec(x_583);
x_585 = l_Lake_LeanOption_decodeToml___closed__4;
x_532 = x_585;
x_533 = x_584;
goto block_543;
}
}
}
block_531:
{
lean_object* x_428; lean_object* x_429; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_490 = l_Lake_loadTomlConfig___closed__5;
lean_inc(x_421);
x_491 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_489, x_490, x_421);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; 
x_492 = l_Lake_LeanOption_decodeToml___closed__4;
x_428 = x_492;
x_429 = x_427;
goto block_488;
}
else
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_ctor_get(x_491, 0);
lean_inc(x_493);
lean_dec(x_491);
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec(x_493);
switch (lean_obj_tag(x_494)) {
case 0:
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_496 = x_494;
} else {
 lean_dec_ref(x_494);
 x_496 = lean_box(0);
}
x_497 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_496)) {
 x_498 = lean_alloc_ctor(0, 2, 0);
} else {
 x_498 = x_496;
}
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_497);
x_499 = lean_unsigned_to_nat(1u);
x_500 = lean_mk_array(x_499, x_498);
x_501 = l_Array_append___rarg(x_427, x_500);
lean_dec(x_500);
x_502 = l_Lake_LeanOption_decodeToml___closed__4;
x_428 = x_502;
x_429 = x_501;
goto block_488;
}
case 2:
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_503 = lean_ctor_get(x_494, 0);
lean_inc(x_503);
lean_dec(x_494);
x_504 = l_Lake_LeanConfig_decodeToml___closed__5;
x_505 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_505, 0, x_503);
lean_ctor_set(x_505, 1, x_504);
x_506 = lean_unsigned_to_nat(1u);
x_507 = lean_mk_array(x_506, x_505);
x_508 = l_Array_append___rarg(x_427, x_507);
lean_dec(x_507);
x_509 = l_Lake_LeanOption_decodeToml___closed__4;
x_428 = x_509;
x_429 = x_508;
goto block_488;
}
case 3:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_510 = lean_ctor_get(x_494, 0);
lean_inc(x_510);
lean_dec(x_494);
x_511 = l_Lake_LeanConfig_decodeToml___closed__5;
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_unsigned_to_nat(1u);
x_514 = lean_mk_array(x_513, x_512);
x_515 = l_Array_append___rarg(x_427, x_514);
lean_dec(x_514);
x_516 = l_Lake_LeanOption_decodeToml___closed__4;
x_428 = x_516;
x_429 = x_515;
goto block_488;
}
case 5:
{
lean_object* x_517; lean_object* x_518; 
x_517 = lean_ctor_get(x_494, 1);
lean_inc(x_517);
lean_dec(x_494);
x_518 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(x_517);
lean_dec(x_517);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
lean_dec(x_518);
x_520 = l_Array_append___rarg(x_427, x_519);
lean_dec(x_519);
x_521 = l_Lake_LeanOption_decodeToml___closed__4;
x_428 = x_521;
x_429 = x_520;
goto block_488;
}
else
{
lean_object* x_522; 
x_522 = lean_ctor_get(x_518, 0);
lean_inc(x_522);
lean_dec(x_518);
x_428 = x_522;
x_429 = x_427;
goto block_488;
}
}
default: 
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_523 = lean_ctor_get(x_494, 0);
lean_inc(x_523);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_524 = x_494;
} else {
 lean_dec_ref(x_494);
 x_524 = lean_box(0);
}
x_525 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_524)) {
 x_526 = lean_alloc_ctor(0, 2, 0);
} else {
 x_526 = x_524;
 lean_ctor_set_tag(x_526, 0);
}
lean_ctor_set(x_526, 0, x_523);
lean_ctor_set(x_526, 1, x_525);
x_527 = lean_unsigned_to_nat(1u);
x_528 = lean_mk_array(x_527, x_526);
x_529 = l_Array_append___rarg(x_427, x_528);
lean_dec(x_528);
x_530 = l_Lake_LeanOption_decodeToml___closed__4;
x_428 = x_530;
x_429 = x_529;
goto block_488;
}
}
}
block_488:
{
lean_object* x_430; lean_object* x_431; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_447 = l_Lake_loadTomlConfig___closed__3;
x_448 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_446, x_447, x_421);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; 
x_449 = l_Lake_LeanOption_decodeToml___closed__4;
x_430 = x_449;
x_431 = x_429;
goto block_445;
}
else
{
lean_object* x_450; lean_object* x_451; 
x_450 = lean_ctor_get(x_448, 0);
lean_inc(x_450);
lean_dec(x_448);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
lean_dec(x_450);
switch (lean_obj_tag(x_451)) {
case 0:
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_453 = x_451;
} else {
 lean_dec_ref(x_451);
 x_453 = lean_box(0);
}
x_454 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(0, 2, 0);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_452);
lean_ctor_set(x_455, 1, x_454);
x_456 = lean_unsigned_to_nat(1u);
x_457 = lean_mk_array(x_456, x_455);
x_458 = l_Array_append___rarg(x_429, x_457);
lean_dec(x_457);
x_459 = l_Lake_LeanOption_decodeToml___closed__4;
x_430 = x_459;
x_431 = x_458;
goto block_445;
}
case 2:
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_460 = lean_ctor_get(x_451, 0);
lean_inc(x_460);
lean_dec(x_451);
x_461 = l_Lake_LeanConfig_decodeToml___closed__5;
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_460);
lean_ctor_set(x_462, 1, x_461);
x_463 = lean_unsigned_to_nat(1u);
x_464 = lean_mk_array(x_463, x_462);
x_465 = l_Array_append___rarg(x_429, x_464);
lean_dec(x_464);
x_466 = l_Lake_LeanOption_decodeToml___closed__4;
x_430 = x_466;
x_431 = x_465;
goto block_445;
}
case 3:
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_467 = lean_ctor_get(x_451, 0);
lean_inc(x_467);
lean_dec(x_451);
x_468 = l_Lake_LeanConfig_decodeToml___closed__5;
x_469 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
x_470 = lean_unsigned_to_nat(1u);
x_471 = lean_mk_array(x_470, x_469);
x_472 = l_Array_append___rarg(x_429, x_471);
lean_dec(x_471);
x_473 = l_Lake_LeanOption_decodeToml___closed__4;
x_430 = x_473;
x_431 = x_472;
goto block_445;
}
case 5:
{
lean_object* x_474; lean_object* x_475; 
x_474 = lean_ctor_get(x_451, 1);
lean_inc(x_474);
lean_dec(x_451);
x_475 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__8(x_474);
lean_dec(x_474);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
lean_dec(x_475);
x_477 = l_Array_append___rarg(x_429, x_476);
lean_dec(x_476);
x_478 = l_Lake_LeanOption_decodeToml___closed__4;
x_430 = x_478;
x_431 = x_477;
goto block_445;
}
else
{
lean_object* x_479; 
x_479 = lean_ctor_get(x_475, 0);
lean_inc(x_479);
lean_dec(x_475);
x_430 = x_479;
x_431 = x_429;
goto block_445;
}
}
default: 
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_480 = lean_ctor_get(x_451, 0);
lean_inc(x_480);
if (lean_is_exclusive(x_451)) {
 lean_ctor_release(x_451, 0);
 lean_ctor_release(x_451, 1);
 x_481 = x_451;
} else {
 lean_dec_ref(x_451);
 x_481 = lean_box(0);
}
x_482 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_481;
 lean_ctor_set_tag(x_483, 0);
}
lean_ctor_set(x_483, 0, x_480);
lean_ctor_set(x_483, 1, x_482);
x_484 = lean_unsigned_to_nat(1u);
x_485 = lean_mk_array(x_484, x_483);
x_486 = l_Array_append___rarg(x_429, x_485);
lean_dec(x_485);
x_487 = l_Lake_LeanOption_decodeToml___closed__4;
x_430 = x_487;
x_431 = x_486;
goto block_445;
}
}
}
block_445:
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_422, 3);
lean_inc(x_432);
x_433 = lean_box(0);
x_434 = lean_box(0);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_435 = lean_ctor_get(x_422, 17);
lean_inc(x_435);
x_436 = lean_ctor_get(x_422, 19);
lean_inc(x_436);
x_437 = l_Lake_defaultManifestFile;
x_438 = l_Lake_LeanOption_decodeToml___closed__4;
x_439 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_439, 0, x_1);
lean_ctor_set(x_439, 1, x_2);
lean_ctor_set(x_439, 2, x_422);
lean_ctor_set(x_439, 3, x_3);
lean_ctor_set(x_439, 4, x_437);
lean_ctor_set(x_439, 5, x_433);
lean_ctor_set(x_439, 6, x_438);
lean_ctor_set(x_439, 7, x_430);
lean_ctor_set(x_439, 8, x_424);
lean_ctor_set(x_439, 9, x_426);
lean_ctor_set(x_439, 10, x_434);
lean_ctor_set(x_439, 11, x_434);
lean_ctor_set(x_439, 12, x_428);
lean_ctor_set(x_439, 13, x_434);
lean_ctor_set(x_439, 14, x_438);
lean_ctor_set(x_439, 15, x_438);
lean_ctor_set(x_439, 16, x_435);
lean_ctor_set(x_439, 17, x_436);
x_374 = x_439;
x_375 = x_431;
goto block_399;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_440 = lean_ctor_get(x_422, 17);
lean_inc(x_440);
x_441 = lean_ctor_get(x_422, 19);
lean_inc(x_441);
x_442 = lean_ctor_get(x_432, 0);
lean_inc(x_442);
lean_dec(x_432);
x_443 = l_Lake_LeanOption_decodeToml___closed__4;
x_444 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_444, 0, x_1);
lean_ctor_set(x_444, 1, x_2);
lean_ctor_set(x_444, 2, x_422);
lean_ctor_set(x_444, 3, x_3);
lean_ctor_set(x_444, 4, x_442);
lean_ctor_set(x_444, 5, x_433);
lean_ctor_set(x_444, 6, x_443);
lean_ctor_set(x_444, 7, x_430);
lean_ctor_set(x_444, 8, x_424);
lean_ctor_set(x_444, 9, x_426);
lean_ctor_set(x_444, 10, x_434);
lean_ctor_set(x_444, 11, x_434);
lean_ctor_set(x_444, 12, x_428);
lean_ctor_set(x_444, 13, x_434);
lean_ctor_set(x_444, 14, x_443);
lean_ctor_set(x_444, 15, x_443);
lean_ctor_set(x_444, 16, x_440);
lean_ctor_set(x_444, 17, x_441);
x_374 = x_444;
x_375 = x_431;
goto block_399;
}
}
}
}
block_543:
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_534 = lean_array_get_size(x_532);
x_535 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_536 = l_Lake_RBArray_mkEmpty___rarg(x_535, x_534);
x_537 = lean_unsigned_to_nat(0u);
x_538 = lean_nat_dec_lt(x_537, x_534);
if (x_538 == 0)
{
lean_dec(x_534);
lean_dec(x_532);
x_426 = x_536;
x_427 = x_533;
goto block_531;
}
else
{
uint8_t x_539; 
x_539 = lean_nat_dec_le(x_534, x_534);
if (x_539 == 0)
{
lean_dec(x_534);
lean_dec(x_532);
x_426 = x_536;
x_427 = x_533;
goto block_531;
}
else
{
size_t x_540; size_t x_541; lean_object* x_542; 
x_540 = 0;
x_541 = lean_usize_of_nat(x_534);
lean_dec(x_534);
x_542 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10(x_532, x_540, x_541, x_536);
lean_dec(x_532);
x_426 = x_542;
x_427 = x_533;
goto block_531;
}
}
}
}
block_598:
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; 
x_589 = lean_array_get_size(x_587);
x_590 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_591 = l_Lake_RBArray_mkEmpty___rarg(x_590, x_589);
x_592 = lean_unsigned_to_nat(0u);
x_593 = lean_nat_dec_lt(x_592, x_589);
if (x_593 == 0)
{
lean_dec(x_589);
lean_dec(x_587);
x_424 = x_591;
x_425 = x_588;
goto block_586;
}
else
{
uint8_t x_594; 
x_594 = lean_nat_dec_le(x_589, x_589);
if (x_594 == 0)
{
lean_dec(x_589);
lean_dec(x_587);
x_424 = x_591;
x_425 = x_588;
goto block_586;
}
else
{
size_t x_595; size_t x_596; lean_object* x_597; 
x_595 = 0;
x_596 = lean_usize_of_nat(x_589);
lean_dec(x_589);
x_597 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13(x_587, x_595, x_596, x_591);
lean_dec(x_587);
x_424 = x_597;
x_425 = x_588;
goto block_586;
}
}
}
}
}
block_399:
{
uint8_t x_376; 
x_376 = l_Array_isEmpty___rarg(x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; 
lean_dec(x_374);
x_377 = lean_array_get_size(x_375);
x_378 = lean_unsigned_to_nat(0u);
x_379 = lean_nat_dec_lt(x_378, x_377);
x_380 = lean_array_get_size(x_372);
if (x_379 == 0)
{
lean_object* x_381; lean_object* x_382; 
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_368);
if (lean_is_scalar(x_373)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_373;
 lean_ctor_set_tag(x_381, 1);
}
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_372);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_370);
return x_382;
}
else
{
uint8_t x_383; 
x_383 = lean_nat_dec_le(x_377, x_377);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_377);
lean_dec(x_375);
lean_dec(x_368);
if (lean_is_scalar(x_373)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_373;
 lean_ctor_set_tag(x_384, 1);
}
lean_ctor_set(x_384, 0, x_380);
lean_ctor_set(x_384, 1, x_372);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_370);
return x_385;
}
else
{
size_t x_386; size_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
lean_dec(x_373);
x_386 = 0;
x_387 = lean_usize_of_nat(x_377);
lean_dec(x_377);
x_388 = lean_box(0);
x_389 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1(x_368, x_375, x_386, x_387, x_388, x_372, x_370);
lean_dec(x_375);
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_392 = x_389;
} else {
 lean_dec_ref(x_389);
 x_392 = lean_box(0);
}
x_393 = lean_ctor_get(x_390, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_394 = x_390;
} else {
 lean_dec_ref(x_390);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
 lean_ctor_set_tag(x_395, 1);
}
lean_ctor_set(x_395, 0, x_380);
lean_ctor_set(x_395, 1, x_393);
if (lean_is_scalar(x_392)) {
 x_396 = lean_alloc_ctor(0, 2, 0);
} else {
 x_396 = x_392;
}
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_391);
return x_396;
}
}
}
else
{
lean_object* x_397; lean_object* x_398; 
lean_dec(x_375);
lean_dec(x_368);
if (lean_is_scalar(x_373)) {
 x_397 = lean_alloc_ctor(0, 2, 0);
} else {
 x_397 = x_373;
}
lean_ctor_set(x_397, 0, x_374);
lean_ctor_set(x_397, 1, x_372);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_370);
return x_398;
}
}
}
}
}
else
{
uint8_t x_660; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_660 = !lean_is_exclusive(x_7);
if (x_660 == 0)
{
lean_object* x_661; 
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_7);
lean_ctor_set(x_661, 1, x_8);
return x_661;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_662 = lean_ctor_get(x_7, 0);
x_663 = lean_ctor_get(x_7, 1);
lean_inc(x_663);
lean_inc(x_662);
lean_dec(x_7);
x_664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_664, 0, x_662);
lean_ctor_set(x_664, 1, x_663);
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_664);
lean_ctor_set(x_665, 1, x_8);
return x_665;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__5(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__6(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_loadTomlConfig___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forMAux___at_Lake_loadTomlConfig___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_loadTomlConfig___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentArray_forM___at_Lake_loadTomlConfig___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__9(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__8(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__11___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__11(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__15___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__15(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__14___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__14(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Load(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Decode(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Toml(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Load(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Decode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_takeNamePart___closed__1 = _init_l_Lake_takeNamePart___closed__1();
lean_mark_persistent(l_Lake_takeNamePart___closed__1);
l_Lake_takeNamePart___closed__2 = _init_l_Lake_takeNamePart___closed__2();
lean_mark_persistent(l_Lake_takeNamePart___closed__2);
l_Lake_takeNamePart___closed__3 = _init_l_Lake_takeNamePart___closed__3();
lean_mark_persistent(l_Lake_takeNamePart___closed__3);
l_Lake_takeNamePart___closed__4 = _init_l_Lake_takeNamePart___closed__4();
lean_mark_persistent(l_Lake_takeNamePart___closed__4);
l_Lake_Glob_decodeToml___closed__1 = _init_l_Lake_Glob_decodeToml___closed__1();
lean_mark_persistent(l_Lake_Glob_decodeToml___closed__1);
l_Lake_Glob_decodeToml___closed__2 = _init_l_Lake_Glob_decodeToml___closed__2();
lean_mark_persistent(l_Lake_Glob_decodeToml___closed__2);
l_Lake_LeanOptionValue_decodeToml___closed__1 = _init_l_Lake_LeanOptionValue_decodeToml___closed__1();
lean_mark_persistent(l_Lake_LeanOptionValue_decodeToml___closed__1);
l_Lake_LeanOptionValue_decodeToml___closed__2 = _init_l_Lake_LeanOptionValue_decodeToml___closed__2();
lean_mark_persistent(l_Lake_LeanOptionValue_decodeToml___closed__2);
l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__1);
l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__2___closed__2);
l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1 = _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1();
lean_mark_persistent(l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1);
l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2 = _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2();
lean_mark_persistent(l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2);
l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3 = _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3();
lean_mark_persistent(l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3);
l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4 = _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4();
lean_mark_persistent(l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__4);
l_Lake_LeanOption_decodeToml___closed__1 = _init_l_Lake_LeanOption_decodeToml___closed__1();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__1);
l_Lake_LeanOption_decodeToml___closed__2 = _init_l_Lake_LeanOption_decodeToml___closed__2();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__2);
l_Lake_LeanOption_decodeToml___closed__3 = _init_l_Lake_LeanOption_decodeToml___closed__3();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__3);
l_Lake_LeanOption_decodeToml___closed__4 = _init_l_Lake_LeanOption_decodeToml___closed__4();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__4);
l_Lake_LeanOption_decodeToml___closed__5 = _init_l_Lake_LeanOption_decodeToml___closed__5();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__5);
l_Lake_LeanOption_decodeToml___closed__6 = _init_l_Lake_LeanOption_decodeToml___closed__6();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__6);
l_Lake_LeanOption_decodeToml___closed__7 = _init_l_Lake_LeanOption_decodeToml___closed__7();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__7);
l_Lake_LeanOption_decodeToml___closed__8 = _init_l_Lake_LeanOption_decodeToml___closed__8();
l_Lake_LeanOption_decodeToml___closed__9 = _init_l_Lake_LeanOption_decodeToml___closed__9();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__9);
l_Lake_LeanOption_decodeToml___closed__10 = _init_l_Lake_LeanOption_decodeToml___closed__10();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__10);
l_Lake_LeanOption_decodeToml___closed__11 = _init_l_Lake_LeanOption_decodeToml___closed__11();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__11);
l_Lake_LeanOption_decodeToml___closed__12 = _init_l_Lake_LeanOption_decodeToml___closed__12();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__12);
l_Lake_LeanOption_decodeToml___closed__13 = _init_l_Lake_LeanOption_decodeToml___closed__13();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__13);
l_Lake_instDecodeTomlLeanOption___closed__1 = _init_l_Lake_instDecodeTomlLeanOption___closed__1();
lean_mark_persistent(l_Lake_instDecodeTomlLeanOption___closed__1);
l_Lake_instDecodeTomlLeanOption = _init_l_Lake_instDecodeTomlLeanOption();
lean_mark_persistent(l_Lake_instDecodeTomlLeanOption);
l_Lake_BuildType_decodeToml___closed__1 = _init_l_Lake_BuildType_decodeToml___closed__1();
lean_mark_persistent(l_Lake_BuildType_decodeToml___closed__1);
l_Lake_BuildType_decodeToml___closed__2 = _init_l_Lake_BuildType_decodeToml___closed__2();
lean_mark_persistent(l_Lake_BuildType_decodeToml___closed__2);
l_Lake_BuildType_decodeToml___closed__3 = _init_l_Lake_BuildType_decodeToml___closed__3();
lean_mark_persistent(l_Lake_BuildType_decodeToml___closed__3);
l_Lake_BuildType_decodeToml___closed__4 = _init_l_Lake_BuildType_decodeToml___closed__4();
lean_mark_persistent(l_Lake_BuildType_decodeToml___closed__4);
l_Lake_BuildType_decodeToml___closed__5 = _init_l_Lake_BuildType_decodeToml___closed__5();
lean_mark_persistent(l_Lake_BuildType_decodeToml___closed__5);
l_Lake_BuildType_decodeToml___closed__6 = _init_l_Lake_BuildType_decodeToml___closed__6();
lean_mark_persistent(l_Lake_BuildType_decodeToml___closed__6);
l_Lake_BuildType_decodeToml___closed__7 = _init_l_Lake_BuildType_decodeToml___closed__7();
lean_mark_persistent(l_Lake_BuildType_decodeToml___closed__7);
l_Lake_BuildType_decodeToml___closed__8 = _init_l_Lake_BuildType_decodeToml___closed__8();
lean_mark_persistent(l_Lake_BuildType_decodeToml___closed__8);
l_Lake_BuildType_decodeToml___closed__9 = _init_l_Lake_BuildType_decodeToml___closed__9();
lean_mark_persistent(l_Lake_BuildType_decodeToml___closed__9);
l_Lake_Backend_decodeToml___closed__1 = _init_l_Lake_Backend_decodeToml___closed__1();
lean_mark_persistent(l_Lake_Backend_decodeToml___closed__1);
l_Lake_Backend_decodeToml___closed__2 = _init_l_Lake_Backend_decodeToml___closed__2();
lean_mark_persistent(l_Lake_Backend_decodeToml___closed__2);
l_Lake_Backend_decodeToml___closed__3 = _init_l_Lake_Backend_decodeToml___closed__3();
lean_mark_persistent(l_Lake_Backend_decodeToml___closed__3);
l_Lake_Backend_decodeToml___closed__4 = _init_l_Lake_Backend_decodeToml___closed__4();
lean_mark_persistent(l_Lake_Backend_decodeToml___closed__4);
l_Lake_Backend_decodeToml___closed__5 = _init_l_Lake_Backend_decodeToml___closed__5();
lean_mark_persistent(l_Lake_Backend_decodeToml___closed__5);
l_Lake_Backend_decodeToml___closed__6 = _init_l_Lake_Backend_decodeToml___closed__6();
lean_mark_persistent(l_Lake_Backend_decodeToml___closed__6);
l_Lake_Backend_decodeToml___closed__7 = _init_l_Lake_Backend_decodeToml___closed__7();
lean_mark_persistent(l_Lake_Backend_decodeToml___closed__7);
l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1);
l_Lake_decodeLeanOptions___closed__1 = _init_l_Lake_decodeLeanOptions___closed__1();
lean_mark_persistent(l_Lake_decodeLeanOptions___closed__1);
l_Lake_WorkspaceConfig_decodeToml___closed__1 = _init_l_Lake_WorkspaceConfig_decodeToml___closed__1();
lean_mark_persistent(l_Lake_WorkspaceConfig_decodeToml___closed__1);
l_Lake_WorkspaceConfig_decodeToml___closed__2 = _init_l_Lake_WorkspaceConfig_decodeToml___closed__2();
lean_mark_persistent(l_Lake_WorkspaceConfig_decodeToml___closed__2);
l_Lake_instDecodeTomlWorkspaceConfig___closed__1 = _init_l_Lake_instDecodeTomlWorkspaceConfig___closed__1();
lean_mark_persistent(l_Lake_instDecodeTomlWorkspaceConfig___closed__1);
l_Lake_LeanConfig_decodeToml___closed__1 = _init_l_Lake_LeanConfig_decodeToml___closed__1();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__1);
l_Lake_LeanConfig_decodeToml___closed__2 = _init_l_Lake_LeanConfig_decodeToml___closed__2();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__2);
l_Lake_LeanConfig_decodeToml___closed__3 = _init_l_Lake_LeanConfig_decodeToml___closed__3();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__3);
l_Lake_LeanConfig_decodeToml___closed__4 = _init_l_Lake_LeanConfig_decodeToml___closed__4();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__4);
l_Lake_LeanConfig_decodeToml___closed__5 = _init_l_Lake_LeanConfig_decodeToml___closed__5();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__5);
l_Lake_LeanConfig_decodeToml___closed__6 = _init_l_Lake_LeanConfig_decodeToml___closed__6();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__6);
l_Lake_LeanConfig_decodeToml___closed__7 = _init_l_Lake_LeanConfig_decodeToml___closed__7();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__7);
l_Lake_LeanConfig_decodeToml___closed__8 = _init_l_Lake_LeanConfig_decodeToml___closed__8();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__8);
l_Lake_LeanConfig_decodeToml___closed__9 = _init_l_Lake_LeanConfig_decodeToml___closed__9();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__9);
l_Lake_LeanConfig_decodeToml___closed__10 = _init_l_Lake_LeanConfig_decodeToml___closed__10();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__10);
l_Lake_LeanConfig_decodeToml___closed__11 = _init_l_Lake_LeanConfig_decodeToml___closed__11();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__11);
l_Lake_LeanConfig_decodeToml___closed__12 = _init_l_Lake_LeanConfig_decodeToml___closed__12();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__12);
l_Lake_LeanConfig_decodeToml___closed__13 = _init_l_Lake_LeanConfig_decodeToml___closed__13();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__13);
l_Lake_LeanConfig_decodeToml___closed__14 = _init_l_Lake_LeanConfig_decodeToml___closed__14();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__14);
l_Lake_LeanConfig_decodeToml___closed__15 = _init_l_Lake_LeanConfig_decodeToml___closed__15();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__15);
l_Lake_LeanConfig_decodeToml___closed__16 = _init_l_Lake_LeanConfig_decodeToml___closed__16();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__16);
l_Lake_LeanConfig_decodeToml___closed__17 = _init_l_Lake_LeanConfig_decodeToml___closed__17();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__17);
l_Lake_LeanConfig_decodeToml___closed__18 = _init_l_Lake_LeanConfig_decodeToml___closed__18();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__18);
l_Lake_LeanConfig_decodeToml___closed__19 = _init_l_Lake_LeanConfig_decodeToml___closed__19();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__19);
l_Lake_LeanConfig_decodeToml___closed__20 = _init_l_Lake_LeanConfig_decodeToml___closed__20();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__20);
l_Lake_LeanConfig_decodeToml___closed__21 = _init_l_Lake_LeanConfig_decodeToml___closed__21();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__21);
l_Lake_LeanConfig_decodeToml___closed__22 = _init_l_Lake_LeanConfig_decodeToml___closed__22();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__22);
l_Lake_LeanConfig_decodeToml___closed__23 = _init_l_Lake_LeanConfig_decodeToml___closed__23();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__23);
l_Lake_LeanConfig_decodeToml___closed__24 = _init_l_Lake_LeanConfig_decodeToml___closed__24();
lean_mark_persistent(l_Lake_LeanConfig_decodeToml___closed__24);
l_Lake_PackageConfig_decodeToml___closed__1 = _init_l_Lake_PackageConfig_decodeToml___closed__1();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__1);
l_Lake_PackageConfig_decodeToml___closed__2 = _init_l_Lake_PackageConfig_decodeToml___closed__2();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__2);
l_Lake_PackageConfig_decodeToml___closed__3 = _init_l_Lake_PackageConfig_decodeToml___closed__3();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__3);
l_Lake_PackageConfig_decodeToml___closed__4 = _init_l_Lake_PackageConfig_decodeToml___closed__4();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__4);
l_Lake_PackageConfig_decodeToml___closed__5 = _init_l_Lake_PackageConfig_decodeToml___closed__5();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__5);
l_Lake_PackageConfig_decodeToml___closed__6 = _init_l_Lake_PackageConfig_decodeToml___closed__6();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__6);
l_Lake_PackageConfig_decodeToml___closed__7 = _init_l_Lake_PackageConfig_decodeToml___closed__7();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__7);
l_Lake_PackageConfig_decodeToml___closed__8 = _init_l_Lake_PackageConfig_decodeToml___closed__8();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__8);
l_Lake_PackageConfig_decodeToml___closed__9 = _init_l_Lake_PackageConfig_decodeToml___closed__9();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__9);
l_Lake_PackageConfig_decodeToml___closed__10 = _init_l_Lake_PackageConfig_decodeToml___closed__10();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__10);
l_Lake_PackageConfig_decodeToml___closed__11 = _init_l_Lake_PackageConfig_decodeToml___closed__11();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__11);
l_Lake_PackageConfig_decodeToml___closed__12 = _init_l_Lake_PackageConfig_decodeToml___closed__12();
l_Lake_PackageConfig_decodeToml___closed__13 = _init_l_Lake_PackageConfig_decodeToml___closed__13();
l_Lake_PackageConfig_decodeToml___closed__14 = _init_l_Lake_PackageConfig_decodeToml___closed__14();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__14);
l_Lake_PackageConfig_decodeToml___closed__15 = _init_l_Lake_PackageConfig_decodeToml___closed__15();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__15);
l_Lake_PackageConfig_decodeToml___closed__16 = _init_l_Lake_PackageConfig_decodeToml___closed__16();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__16);
l_Lake_PackageConfig_decodeToml___closed__17 = _init_l_Lake_PackageConfig_decodeToml___closed__17();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__17);
l_Lake_PackageConfig_decodeToml___closed__18 = _init_l_Lake_PackageConfig_decodeToml___closed__18();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__18);
l_Lake_PackageConfig_decodeToml___closed__19 = _init_l_Lake_PackageConfig_decodeToml___closed__19();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__19);
l_Lake_PackageConfig_decodeToml___closed__20 = _init_l_Lake_PackageConfig_decodeToml___closed__20();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__20);
l_Lake_PackageConfig_decodeToml___closed__21 = _init_l_Lake_PackageConfig_decodeToml___closed__21();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__21);
l_Lake_PackageConfig_decodeToml___closed__22 = _init_l_Lake_PackageConfig_decodeToml___closed__22();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__22);
l_Lake_PackageConfig_decodeToml___closed__23 = _init_l_Lake_PackageConfig_decodeToml___closed__23();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__23);
l_Lake_PackageConfig_decodeToml___closed__24 = _init_l_Lake_PackageConfig_decodeToml___closed__24();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__24);
l_Lake_PackageConfig_decodeToml___closed__25 = _init_l_Lake_PackageConfig_decodeToml___closed__25();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__25);
l_Lake_PackageConfig_decodeToml___closed__26 = _init_l_Lake_PackageConfig_decodeToml___closed__26();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__26);
l_Lake_PackageConfig_decodeToml___closed__27 = _init_l_Lake_PackageConfig_decodeToml___closed__27();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__27);
l_Lake_PackageConfig_decodeToml___closed__28 = _init_l_Lake_PackageConfig_decodeToml___closed__28();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__28);
l_Lake_PackageConfig_decodeToml___closed__29 = _init_l_Lake_PackageConfig_decodeToml___closed__29();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__29);
l_Lake_PackageConfig_decodeToml___closed__30 = _init_l_Lake_PackageConfig_decodeToml___closed__30();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__30);
l_Lake_PackageConfig_decodeToml___closed__31 = _init_l_Lake_PackageConfig_decodeToml___closed__31();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__31);
l_Lake_PackageConfig_decodeToml___closed__32 = _init_l_Lake_PackageConfig_decodeToml___closed__32();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__32);
l_Lake_PackageConfig_decodeToml___closed__33 = _init_l_Lake_PackageConfig_decodeToml___closed__33();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__33);
l_Lake_PackageConfig_decodeToml___closed__34 = _init_l_Lake_PackageConfig_decodeToml___closed__34();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__34);
l_Lake_PackageConfig_decodeToml___closed__35 = _init_l_Lake_PackageConfig_decodeToml___closed__35();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__35);
l_Lake_PackageConfig_decodeToml___closed__36 = _init_l_Lake_PackageConfig_decodeToml___closed__36();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__36);
l_Lake_PackageConfig_decodeToml___closed__37 = _init_l_Lake_PackageConfig_decodeToml___closed__37();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__37);
l_Lake_PackageConfig_decodeToml___closed__38 = _init_l_Lake_PackageConfig_decodeToml___closed__38();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__38);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__5 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__5();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__5);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__6 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__6();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__6);
l_Lake_LeanLibConfig_decodeToml___closed__1 = _init_l_Lake_LeanLibConfig_decodeToml___closed__1();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__1);
l_Lake_LeanLibConfig_decodeToml___closed__2 = _init_l_Lake_LeanLibConfig_decodeToml___closed__2();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__2);
l_Lake_LeanLibConfig_decodeToml___closed__3 = _init_l_Lake_LeanLibConfig_decodeToml___closed__3();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__3);
l_Lake_LeanLibConfig_decodeToml___closed__4 = _init_l_Lake_LeanLibConfig_decodeToml___closed__4();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__4);
l_Lake_LeanLibConfig_decodeToml___closed__5 = _init_l_Lake_LeanLibConfig_decodeToml___closed__5();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__5);
l_Lake_LeanLibConfig_decodeToml___closed__6 = _init_l_Lake_LeanLibConfig_decodeToml___closed__6();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__6);
l_Lake_LeanLibConfig_decodeToml___closed__7 = _init_l_Lake_LeanLibConfig_decodeToml___closed__7();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__7);
l_Lake_LeanLibConfig_decodeToml___closed__8 = _init_l_Lake_LeanLibConfig_decodeToml___closed__8();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__8);
l_Lake_LeanLibConfig_decodeToml___closed__9 = _init_l_Lake_LeanLibConfig_decodeToml___closed__9();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__9);
l_Lake_LeanLibConfig_decodeToml___closed__10 = _init_l_Lake_LeanLibConfig_decodeToml___closed__10();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__10);
l_Lake_LeanLibConfig_decodeToml___closed__11 = _init_l_Lake_LeanLibConfig_decodeToml___closed__11();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__11);
l_Lake_LeanLibConfig_decodeToml___closed__12 = _init_l_Lake_LeanLibConfig_decodeToml___closed__12();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___closed__12);
l_Lake_LeanExeConfig_decodeToml___closed__1 = _init_l_Lake_LeanExeConfig_decodeToml___closed__1();
lean_mark_persistent(l_Lake_LeanExeConfig_decodeToml___closed__1);
l_Lake_LeanExeConfig_decodeToml___closed__2 = _init_l_Lake_LeanExeConfig_decodeToml___closed__2();
lean_mark_persistent(l_Lake_LeanExeConfig_decodeToml___closed__2);
l_Lake_LeanExeConfig_decodeToml___closed__3 = _init_l_Lake_LeanExeConfig_decodeToml___closed__3();
lean_mark_persistent(l_Lake_LeanExeConfig_decodeToml___closed__3);
l_Lake_LeanExeConfig_decodeToml___closed__4 = _init_l_Lake_LeanExeConfig_decodeToml___closed__4();
lean_mark_persistent(l_Lake_LeanExeConfig_decodeToml___closed__4);
l_Lake_LeanExeConfig_decodeToml___closed__5 = _init_l_Lake_LeanExeConfig_decodeToml___closed__5();
lean_mark_persistent(l_Lake_LeanExeConfig_decodeToml___closed__5);
l_Lake_LeanExeConfig_decodeToml___closed__6 = _init_l_Lake_LeanExeConfig_decodeToml___closed__6();
lean_mark_persistent(l_Lake_LeanExeConfig_decodeToml___closed__6);
l_Lake_DependencySrc_decodeToml___closed__1 = _init_l_Lake_DependencySrc_decodeToml___closed__1();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__1);
l_Lake_DependencySrc_decodeToml___closed__2 = _init_l_Lake_DependencySrc_decodeToml___closed__2();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__2);
l_Lake_DependencySrc_decodeToml___closed__3 = _init_l_Lake_DependencySrc_decodeToml___closed__3();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__3);
l_Lake_DependencySrc_decodeToml___closed__4 = _init_l_Lake_DependencySrc_decodeToml___closed__4();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__4);
l_Lake_DependencySrc_decodeToml___closed__5 = _init_l_Lake_DependencySrc_decodeToml___closed__5();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__5);
l_Lake_DependencySrc_decodeToml___closed__6 = _init_l_Lake_DependencySrc_decodeToml___closed__6();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__6);
l_Lake_DependencySrc_decodeToml___closed__7 = _init_l_Lake_DependencySrc_decodeToml___closed__7();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__7);
l_Lake_DependencySrc_decodeToml___closed__8 = _init_l_Lake_DependencySrc_decodeToml___closed__8();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__8);
l_Lake_DependencySrc_decodeToml___closed__9 = _init_l_Lake_DependencySrc_decodeToml___closed__9();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__9);
l_Lake_DependencySrc_decodeToml___closed__10 = _init_l_Lake_DependencySrc_decodeToml___closed__10();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__10);
l_Lake_DependencySrc_decodeToml___closed__11 = _init_l_Lake_DependencySrc_decodeToml___closed__11();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__11);
l_Lake_DependencySrc_decodeToml___closed__12 = _init_l_Lake_DependencySrc_decodeToml___closed__12();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__12);
l_Lake_DependencySrc_decodeToml___closed__13 = _init_l_Lake_DependencySrc_decodeToml___closed__13();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__13);
l_Lake_DependencySrc_decodeToml___closed__14 = _init_l_Lake_DependencySrc_decodeToml___closed__14();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__14);
l_Lake_DependencySrc_decodeToml___closed__15 = _init_l_Lake_DependencySrc_decodeToml___closed__15();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__15);
l_Lake_DependencySrc_decodeToml___closed__16 = _init_l_Lake_DependencySrc_decodeToml___closed__16();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__16);
l_Lake_DependencySrc_decodeToml___closed__17 = _init_l_Lake_DependencySrc_decodeToml___closed__17();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__17);
l_Lake_DependencySrc_decodeToml___closed__18 = _init_l_Lake_DependencySrc_decodeToml___closed__18();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__18);
l_Lake_DependencySrc_decodeToml___closed__19 = _init_l_Lake_DependencySrc_decodeToml___closed__19();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__19);
l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1 = _init_l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1();
lean_mark_persistent(l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1);
l_Lake_Dependency_decodeToml___closed__1 = _init_l_Lake_Dependency_decodeToml___closed__1();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__1);
l_Lake_Dependency_decodeToml___closed__2 = _init_l_Lake_Dependency_decodeToml___closed__2();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__2);
l_Lake_Dependency_decodeToml___closed__3 = _init_l_Lake_Dependency_decodeToml___closed__3();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__3);
l_Lake_Dependency_decodeToml___closed__4 = _init_l_Lake_Dependency_decodeToml___closed__4();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__4);
l_Lake_Dependency_decodeToml___closed__5 = _init_l_Lake_Dependency_decodeToml___closed__5();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__5);
l_Lake_Dependency_decodeToml___closed__6 = _init_l_Lake_Dependency_decodeToml___closed__6();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__6);
l_Lake_Dependency_decodeToml___closed__7 = _init_l_Lake_Dependency_decodeToml___closed__7();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__7);
l_Lake_Dependency_decodeToml___closed__8 = _init_l_Lake_Dependency_decodeToml___closed__8();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__8);
l_Lake_Dependency_decodeToml___closed__9 = _init_l_Lake_Dependency_decodeToml___closed__9();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__9);
l_Lake_Dependency_decodeToml___closed__10 = _init_l_Lake_Dependency_decodeToml___closed__10();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__10);
l_Lake_Dependency_decodeToml___closed__11 = _init_l_Lake_Dependency_decodeToml___closed__11();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__11);
l_Lake_Dependency_decodeToml___closed__12 = _init_l_Lake_Dependency_decodeToml___closed__12();
lean_mark_persistent(l_Lake_Dependency_decodeToml___closed__12);
l_Lake_loadTomlConfig___closed__1 = _init_l_Lake_loadTomlConfig___closed__1();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__1);
l_Lake_loadTomlConfig___closed__2 = _init_l_Lake_loadTomlConfig___closed__2();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__2);
l_Lake_loadTomlConfig___closed__3 = _init_l_Lake_loadTomlConfig___closed__3();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__3);
l_Lake_loadTomlConfig___closed__4 = _init_l_Lake_loadTomlConfig___closed__4();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__4);
l_Lake_loadTomlConfig___closed__5 = _init_l_Lake_loadTomlConfig___closed__5();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__5);
l_Lake_loadTomlConfig___closed__6 = _init_l_Lake_loadTomlConfig___closed__6();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__6);
l_Lake_loadTomlConfig___closed__7 = _init_l_Lake_loadTomlConfig___closed__7();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__7);
l_Lake_loadTomlConfig___closed__8 = _init_l_Lake_loadTomlConfig___closed__8();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__8);
l_Lake_loadTomlConfig___closed__9 = _init_l_Lake_loadTomlConfig___closed__9();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__9);
l_Lake_loadTomlConfig___closed__10 = _init_l_Lake_loadTomlConfig___closed__10();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__10);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
