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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__11(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__4(lean_object*);
static lean_object* l_Lake_Backend_decodeToml___closed__2;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__10;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__57;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__11;
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_loadTomlConfig___closed__7;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanOption_decodeToml___closed__4;
static lean_object* l_Lake_decodeLeanOptions___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__60;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_RBArray_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__24;
static lean_object* l_Lake_Backend_decodeToml___closed__4;
static lean_object* l_Lake_Dependency_decodeToml___closed__2;
extern lean_object* l_Lake_defaultBuildDir;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__33;
static uint8_t l_Lake_PackageConfig_decodeToml___closed__37;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__17;
lean_object* l_Array_push___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__58;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_loadTomlConfig___spec__8(size_t, size_t, lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__30;
static lean_object* l_Lake_Dependency_decodeToml___closed__10;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__9;
static lean_object* l_Lake_BuildType_decodeToml___closed__7;
static lean_object* l_Lake_LeanOption_decodeToml___closed__2;
static lean_object* l_Lake_StrPat_decodeToml___closed__8;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__6;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanOptionValue(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__1;
lean_object* l_Lake_Toml_ppKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependency(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_loadTomlConfig___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__15;
LEAN_EXPORT lean_object* l_Lake_StrPat_decodeToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__11;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__62;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlStdVer(lean_object*);
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
static lean_object* l_Lake_PackageConfig_decodeToml___closed__59;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__7;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__22;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__54;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__18;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__53;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_loadTomlConfig___spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DependencySrc_decodeToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(lean_object*);
extern uint32_t l_Lean_idBeginEscape;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__35;
static lean_object* l_Lake_loadTomlConfig___closed__10;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__6(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptionsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_decodeToml___spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__16(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__9;
extern lean_object* l_Lake_versionTagPresets;
static lean_object* l_Lake_BuildType_decodeToml___closed__6;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__21;
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f(lean_object*);
static lean_object* l_Lake_LeanOptionValue_decodeToml___closed__1;
static lean_object* l_Lake_takeNamePart___closed__1;
lean_object* l_Lake_RBArray_mkEmpty___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_StdVer_decodeToml(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_StrPat_decodeToml___spec__5(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_StrPat_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__3;
static lean_object* l_Lake_LeanOptionValue_decodeToml___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__12;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__21;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__15;
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlPackageConfig(lean_object*);
static lean_object* l_Lake_LeanOption_decodeToml___closed__1;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__23;
static lean_object* l_Lake_LeanOption_decodeToml___closed__8;
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_StrPat_decodeToml___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_loadTomlConfig___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__29;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__14(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3(lean_object*, lean_object*);
lean_object* l_panic___at_String_toNat_x21___spec__1(lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__3;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__5;
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Lake_StrPat_decodeToml___closed__2;
static lean_object* l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__18;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1___boxed(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__50;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanExeConfig(lean_object*);
static lean_object* l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3___closed__1;
static lean_object* l_Lake_Dependency_decodeToml___closed__9;
static lean_object* l_Lake_takeNamePart___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__26;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__40;
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__1;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__51;
static lean_object* l_Lake_LeanOption_decodeToml___closed__12;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__8;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__5;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__1;
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__48;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__5___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_loadTomlConfig___closed__8;
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptions(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__10;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__61;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanConfig(lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__19;
LEAN_EXPORT lean_object* l_Lake_Dependency_decodeToml(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__6;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Dependency_decodeToml___closed__4;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__17;
lean_object* l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__16;
LEAN_EXPORT lean_object* l_Lake_StrPat_decodeToml___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_findEntry_x3f___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__3;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__52;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__12;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_StrPat_decodeToml___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2;
static lean_object* l_Lake_StrPat_decodeToml___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__22;
static uint8_t l_Lake_LeanOption_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_StrPat_decodeToml___closed__5;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__31;
static lean_object* l_Lake_loadTomlConfig___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1___boxed(lean_object*);
static lean_object* l_Lake_Dependency_decodeToml___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_PackageConfig_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__23;
static lean_object* l_Lake_decodeLeanOptions___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_loadTomlConfig___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__5;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__39;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlWorkspaceConfig(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__18;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__15;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__17;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__55;
static lean_object* l_Lake_loadTomlConfig___closed__6;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__42;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__14;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__47;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__19;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2;
static lean_object* l_Lake_Dependency_decodeToml___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanOption_decodeToml___closed__9;
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_decodeToml(lean_object*);
static lean_object* l_Lake_StrPat_decodeToml___closed__6;
LEAN_EXPORT lean_object* l_Lake_Backend_decodeToml(lean_object*);
static lean_object* l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__16;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlBackend(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__4;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__20;
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
uint8_t l_Lean_isLetterLike(uint32_t);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanLibConfig(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__2;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__19;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__46;
LEAN_EXPORT lean_object* l_Lake_BuildType_decodeToml(lean_object*);
static lean_object* l_Lake_Backend_decodeToml___closed__7;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__13;
static lean_object* l_Lake_LeanOption_decodeToml___closed__11;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__45;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__44;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__6;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__32;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__3(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_StdVer_parse(lean_object*);
lean_object* l_Lake_mergeErrors___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__24;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_StrPat_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_StrPat_decodeToml___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__5(lean_object*, lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__1;
static lean_object* l_Lake_BuildType_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__4___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__28;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_decodeToml(lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__9;
LEAN_EXPORT lean_object* l_Lake_takeName(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__38;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptionsAux___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__14;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlGlob(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__43;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__11;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_PackageConfig_decodeToml___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__12(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanOption;
lean_object* l_String_toName(lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__16;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__10;
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_WorkspaceConfig_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Lake_takeName_takeRest(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_defaultNativeLibDir;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__4;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_StrPat_decodeToml___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependencySrc(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_PackageConfig_decodeToml___spec__1(lean_object*);
static lean_object* l_Lake_loadTomlConfig___closed__11;
extern lean_object* l_Lake_defaultVersionTags;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__12___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_decodeToml(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__4;
static lean_object* l_Lake_BuildType_decodeToml___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__49;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__11;
static lean_object* l_Lake_Dependency_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1(lean_object*, uint8_t);
static lean_object* l_Lake_takeNamePart___closed__3;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_LeanOption_decodeToml___closed__5;
static lean_object* l_Lake_Backend_decodeToml___closed__3;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Lake_Glob_decodeToml(lean_object*);
static lean_object* l_Lake_StrPat_decodeToml___closed__1;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlStrPat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9___boxed(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__6;
static lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__12;
static lean_object* l_Lake_instDecodeTomlLeanOption___closed__1;
static lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
static lean_object* l_Lake_LeanOption_decodeToml___closed__6;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_LeanOption_decodeToml___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__5;
static lean_object* l_Lake_LeanOption_decodeToml___closed__10;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__14;
static lean_object* l_Lake_Dependency_decodeToml___closed__5;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__25;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_PackageConfig_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeNamePart(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__10;
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultBinDir;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__34;
static lean_object* l_Lake_takeNamePart___closed__2;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_decodeToml___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_PackageConfig_decodeToml___closed__36;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__41;
extern lean_object* l_Lake_defaultIrDir;
static lean_object* l_Lake_Backend_decodeToml___closed__1;
extern lean_object* l_System_Platform_target;
static lean_object* l_Lake_Backend_decodeToml___closed__5;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__56;
static lean_object* l_Lake_Dependency_decodeToml___closed__6;
LEAN_EXPORT lean_object* l_Lake_PackageConfig_decodeToml(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__15___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanOption_decodeToml(lean_object*);
extern lean_object* l_Lake_defaultLeanLibDir;
static lean_object* l_Lake_Glob_decodeToml___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_StrPat_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__12;
extern lean_object* l_Lake_defaultManifestFile;
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1___boxed(lean_object*);
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
lean_object* x_3; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 2);
lean_inc(x_29);
x_30 = lean_nat_sub(x_29, x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; uint32_t x_34; lean_object* x_35; uint32_t x_79; uint8_t x_80; 
x_33 = lean_nat_add(x_28, x_31);
x_34 = lean_string_utf8_get(x_27, x_33);
lean_dec(x_33);
x_79 = l_Lean_idBeginEscape;
x_80 = lean_uint32_dec_eq(x_34, x_79);
if (x_80 == 0)
{
uint32_t x_81; uint8_t x_82; 
x_81 = 65;
x_82 = lean_uint32_dec_le(x_81, x_34);
if (x_82 == 0)
{
uint32_t x_83; uint8_t x_84; 
x_83 = 97;
x_84 = lean_uint32_dec_le(x_83, x_34);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_box(0);
x_35 = x_85;
goto block_78;
}
else
{
uint32_t x_86; uint8_t x_87; 
x_86 = 122;
x_87 = lean_uint32_dec_le(x_34, x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_box(0);
x_35 = x_88;
goto block_78;
}
else
{
lean_object* x_89; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_89 = lean_box(0);
x_3 = x_89;
goto block_26;
}
}
}
else
{
uint32_t x_90; uint8_t x_91; 
x_90 = 90;
x_91 = lean_uint32_dec_le(x_34, x_90);
if (x_91 == 0)
{
uint32_t x_92; uint8_t x_93; 
x_92 = 97;
x_93 = lean_uint32_dec_le(x_92, x_34);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_box(0);
x_35 = x_94;
goto block_78;
}
else
{
uint32_t x_95; uint8_t x_96; 
x_95 = 122;
x_96 = lean_uint32_dec_le(x_34, x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_box(0);
x_35 = x_97;
goto block_78;
}
else
{
lean_object* x_98; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_98 = lean_box(0);
x_3 = x_98;
goto block_26;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_99 = lean_box(0);
x_3 = x_99;
goto block_26;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_unsigned_to_nat(1u);
x_101 = l_Substring_nextn(x_1, x_100, x_31);
x_102 = !lean_is_exclusive(x_1);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint32_t x_109; uint32_t x_110; uint8_t x_111; 
x_103 = lean_ctor_get(x_1, 2);
lean_dec(x_103);
x_104 = lean_ctor_get(x_1, 1);
lean_dec(x_104);
x_105 = lean_ctor_get(x_1, 0);
lean_dec(x_105);
x_106 = lean_nat_add(x_28, x_101);
lean_dec(x_101);
lean_dec(x_28);
lean_inc(x_106);
x_107 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__3(x_27, x_29, x_106);
lean_inc(x_107);
lean_inc(x_27);
lean_ctor_set(x_1, 1, x_107);
x_108 = lean_nat_add(x_107, x_31);
x_109 = lean_string_utf8_get(x_27, x_108);
lean_dec(x_108);
x_110 = l_Lean_idEndEscape;
x_111 = lean_uint32_dec_eq(x_109, x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_27);
lean_dec(x_2);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_1);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_string_utf8_extract(x_27, x_106, x_107);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_27);
x_115 = l_Lean_Name_str___override(x_2, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint32_t x_121; uint32_t x_122; uint8_t x_123; 
lean_dec(x_1);
x_117 = lean_nat_add(x_28, x_101);
lean_dec(x_101);
lean_dec(x_28);
lean_inc(x_117);
x_118 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__3(x_27, x_29, x_117);
lean_inc(x_118);
lean_inc(x_27);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_27);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_119, 2, x_29);
x_120 = lean_nat_add(x_118, x_31);
x_121 = lean_string_utf8_get(x_27, x_120);
lean_dec(x_120);
x_122 = l_Lean_idEndEscape;
x_123 = lean_uint32_dec_eq(x_121, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_27);
lean_dec(x_2);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_119);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_string_utf8_extract(x_27, x_117, x_118);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_27);
x_127 = l_Lean_Name_str___override(x_2, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_119);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
block_78:
{
uint32_t x_36; uint8_t x_37; 
lean_dec(x_35);
x_36 = 95;
x_37 = lean_uint32_dec_eq(x_34, x_36);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_Lean_isLetterLike(x_34);
if (x_38 == 0)
{
uint32_t x_39; uint8_t x_40; 
x_39 = 48;
x_40 = lean_uint32_dec_le(x_39, x_34);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
else
{
uint32_t x_43; uint8_t x_44; 
x_43 = 57;
x_44 = lean_uint32_dec_le(x_34, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = l_Substring_nextn(x_1, x_47, x_31);
x_49 = !lean_is_exclusive(x_1);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_1, 2);
lean_dec(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_dec(x_51);
x_52 = lean_ctor_get(x_1, 0);
lean_dec(x_52);
x_53 = lean_nat_add(x_28, x_48);
lean_dec(x_48);
x_54 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__2(x_27, x_29, x_53);
lean_inc(x_54);
lean_inc(x_27);
lean_ctor_set(x_1, 1, x_54);
x_55 = lean_string_utf8_extract(x_27, x_28, x_54);
lean_dec(x_54);
lean_dec(x_28);
lean_dec(x_27);
x_56 = l_Lean_Syntax_decodeNatLitVal_x3f(x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = l_Lake_takeNamePart___closed__4;
x_58 = l_panic___at_String_toNat_x21___spec__1(x_57);
x_59 = l_Lean_Name_num___override(x_2, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = l_Lean_Name_num___override(x_2, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_1);
x_64 = lean_nat_add(x_28, x_48);
lean_dec(x_48);
x_65 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__2(x_27, x_29, x_64);
lean_inc(x_65);
lean_inc(x_27);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_27);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_66, 2, x_29);
x_67 = lean_string_utf8_extract(x_27, x_28, x_65);
lean_dec(x_65);
lean_dec(x_28);
lean_dec(x_27);
x_68 = l_Lean_Syntax_decodeNatLitVal_x3f(x_67);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = l_Lake_takeNamePart___closed__4;
x_70 = l_panic___at_String_toNat_x21___spec__1(x_69);
x_71 = l_Lean_Name_num___override(x_2, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 0);
lean_inc(x_73);
lean_dec(x_68);
x_74 = l_Lean_Name_num___override(x_2, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_66);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
}
else
{
lean_object* x_76; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_76 = lean_box(0);
x_3 = x_76;
goto block_26;
}
}
else
{
lean_object* x_77; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_77 = lean_box(0);
x_3 = x_77;
goto block_26;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_1);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
block_26:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Substring_nextn(x_1, x_8, x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_1, 2);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_1, 0);
lean_dec(x_14);
x_15 = lean_nat_add(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
x_16 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__1(x_5, x_7, x_15);
lean_inc(x_16);
lean_inc(x_5);
lean_ctor_set(x_1, 1, x_16);
x_17 = lean_string_utf8_extract(x_5, x_4, x_16);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_5);
x_18 = l_Lean_Name_str___override(x_2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_20 = lean_nat_add(x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
x_21 = l_Substring_takeWhileAux___at___private_Init_Meta_0__Lean_Syntax_splitNameLitAux___spec__1(x_5, x_7, x_20);
lean_inc(x_21);
lean_inc(x_5);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_7);
x_23 = lean_string_utf8_extract(x_5, x_4, x_21);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_5);
x_24 = l_Lean_Name_str___override(x_2, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
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
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
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
x_24 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
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
static lean_object* _init_l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected name", 13, 13);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = l_String_toName(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
lean_ctor_set(x_2, 1, x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_array(x_14, x_2);
x_3 = x_15;
goto block_8;
}
else
{
lean_object* x_16; 
lean_free_object(x_2);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_19 = l_String_toName(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_mk_array(x_22, x_21);
x_3 = x_23;
goto block_8;
}
else
{
lean_object* x_24; 
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
return x_24;
}
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Lake_Glob_decodeToml___closed__2;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_mk_array(x_28, x_27);
x_3 = x_29;
goto block_8;
}
case 3:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
lean_dec(x_2);
x_31 = l_Lake_Glob_decodeToml___closed__2;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_mk_array(x_33, x_32);
x_3 = x_34;
goto block_8;
}
default: 
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_2, 1);
lean_dec(x_36);
x_37 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_37);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_mk_array(x_38, x_2);
x_3 = x_39;
goto block_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
x_41 = l_Lake_Glob_decodeToml___closed__2;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_mk_array(x_43, x_42);
x_3 = x_44;
goto block_8;
}
}
}
block_8:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3(x_1, x_4, x_5, x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_17 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2(x_2, x_16);
lean_dec(x_2);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
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
x_24 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_LeanOptionValue_decodeToml(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_mk_array(x_6, x_5);
x_8 = lean_array_size(x_7);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6(x_1, x_8, x_9, x_7);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
lean_dec(x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_array_size(x_13);
x_15 = 0;
x_16 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6(x_1, x_14, x_15, x_13);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
return x_3;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_17 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__5(x_2, x_16);
lean_dec(x_2);
return x_17;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected array of size 2", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanOption_decodeToml___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_LeanOption_decodeToml___closed__7() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__3;
x_2 = l_Array_isEmpty___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanOption_decodeToml___closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("value", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanOption_decodeToml___closed__11;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_array_mk(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lake_LeanOption_decodeToml___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_mk(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lake_LeanOption_decodeToml___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_mk(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lake_LeanOption_decodeToml___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
case 5:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_32 = x_1;
} else {
 lean_dec_ref(x_1);
 x_32 = lean_box(0);
}
x_33 = lean_array_get_size(x_31);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_31);
x_36 = l_Lake_LeanOption_decodeToml___closed__2;
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_32;
 lean_ctor_set_tag(x_37, 0);
}
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_mk(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_74; 
lean_dec(x_30);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_fget(x_31, x_42);
switch (lean_obj_tag(x_43)) {
case 0:
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_43);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_43, 0);
x_108 = lean_ctor_get(x_43, 1);
x_109 = l_String_toName(x_108);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
lean_ctor_set(x_43, 1, x_110);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_mk_array(x_111, x_43);
x_44 = x_112;
goto block_73;
}
else
{
lean_free_object(x_43);
lean_dec(x_107);
lean_dec(x_32);
x_74 = x_109;
goto block_105;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_43, 0);
x_114 = lean_ctor_get(x_43, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_43);
x_115 = l_String_toName(x_114);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_mk_array(x_118, x_117);
x_44 = x_119;
goto block_73;
}
else
{
lean_dec(x_113);
lean_dec(x_32);
x_74 = x_115;
goto block_105;
}
}
}
case 2:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_43, 0);
lean_inc(x_120);
lean_dec(x_43);
x_121 = l_Lake_Glob_decodeToml___closed__2;
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_mk_array(x_123, x_122);
x_44 = x_124;
goto block_73;
}
case 3:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_43, 0);
lean_inc(x_125);
lean_dec(x_43);
x_126 = l_Lake_Glob_decodeToml___closed__2;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_mk_array(x_128, x_127);
x_44 = x_129;
goto block_73;
}
default: 
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_43);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_43, 1);
lean_dec(x_131);
x_132 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_43, 0);
lean_ctor_set(x_43, 1, x_132);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_mk_array(x_133, x_43);
x_44 = x_134;
goto block_73;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_ctor_get(x_43, 0);
lean_inc(x_135);
lean_dec(x_43);
x_136 = l_Lake_Glob_decodeToml___closed__2;
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_mk_array(x_138, x_137);
x_44 = x_139;
goto block_73;
}
}
}
block_73:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = l_Lake_LeanOption_decodeToml___closed__3;
x_46 = l_Array_append___rarg(x_45, x_44);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_array_fget(x_31, x_47);
lean_dec(x_31);
x_49 = l_Lake_LeanOptionValue_decodeToml(x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
lean_dec(x_32);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_49, 0);
x_52 = lean_mk_array(x_47, x_51);
x_53 = l_Array_append___rarg(x_46, x_52);
lean_dec(x_52);
x_54 = l_Array_isEmpty___rarg(x_53);
if (x_54 == 0)
{
lean_ctor_set(x_49, 0, x_53);
return x_49;
}
else
{
lean_object* x_55; 
lean_dec(x_53);
lean_free_object(x_49);
x_55 = l_Lake_LeanOption_decodeToml___closed__6;
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec(x_49);
x_57 = lean_mk_array(x_47, x_56);
x_58 = l_Array_append___rarg(x_46, x_57);
lean_dec(x_57);
x_59 = l_Array_isEmpty___rarg(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
else
{
lean_object* x_61; 
lean_dec(x_58);
x_61 = l_Lake_LeanOption_decodeToml___closed__6;
return x_61;
}
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_49);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_49, 0);
x_64 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_32;
 lean_ctor_set_tag(x_65, 0);
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = l_Array_isEmpty___rarg(x_46);
if (x_66 == 0)
{
lean_dec(x_65);
lean_ctor_set_tag(x_49, 0);
lean_ctor_set(x_49, 0, x_46);
return x_49;
}
else
{
lean_dec(x_46);
lean_ctor_set(x_49, 0, x_65);
return x_49;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_49, 0);
lean_inc(x_67);
lean_dec(x_49);
x_68 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_32;
 lean_ctor_set_tag(x_69, 0);
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = l_Array_isEmpty___rarg(x_46);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_69);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_46);
return x_71;
}
else
{
lean_object* x_72; 
lean_dec(x_46);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_69);
return x_72;
}
}
}
}
block_105:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_array_fget(x_31, x_75);
lean_dec(x_31);
x_77 = l_Lake_LeanOptionValue_decodeToml(x_76);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_mk_array(x_75, x_79);
x_81 = l_Lake_LeanOption_decodeToml___closed__3;
x_82 = l_Array_append___rarg(x_81, x_80);
lean_dec(x_80);
x_83 = l_Lake_LeanOption_decodeToml___closed__4;
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Array_isEmpty___rarg(x_82);
if (x_85 == 0)
{
lean_dec(x_84);
lean_ctor_set(x_77, 0, x_82);
return x_77;
}
else
{
lean_dec(x_82);
lean_ctor_set_tag(x_77, 1);
lean_ctor_set(x_77, 0, x_84);
return x_77;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
lean_dec(x_77);
x_87 = lean_mk_array(x_75, x_86);
x_88 = l_Lake_LeanOption_decodeToml___closed__3;
x_89 = l_Array_append___rarg(x_88, x_87);
lean_dec(x_87);
x_90 = l_Lake_LeanOption_decodeToml___closed__4;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_74);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Array_isEmpty___rarg(x_89);
if (x_92 == 0)
{
lean_object* x_93; 
lean_dec(x_91);
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_89);
return x_93;
}
else
{
lean_object* x_94; 
lean_dec(x_89);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_91);
return x_94;
}
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_77);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_77, 0);
x_97 = l_Lake_LeanOption_decodeToml___closed__7;
if (x_97 == 0)
{
lean_object* x_98; 
lean_free_object(x_77);
lean_dec(x_96);
lean_dec(x_74);
x_98 = l_Lake_LeanOption_decodeToml___closed__8;
return x_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_74);
lean_ctor_set(x_99, 1, x_96);
lean_ctor_set(x_77, 0, x_99);
return x_77;
}
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_ctor_get(x_77, 0);
lean_inc(x_100);
lean_dec(x_77);
x_101 = l_Lake_LeanOption_decodeToml___closed__7;
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_100);
lean_dec(x_74);
x_102 = l_Lake_LeanOption_decodeToml___closed__8;
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_74);
lean_ctor_set(x_103, 1, x_100);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
}
}
}
case 6:
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_1);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_1, 0);
x_142 = lean_ctor_get(x_1, 1);
x_143 = l_Lake_LeanOption_decodeToml___closed__10;
lean_inc(x_141);
lean_inc(x_142);
x_144 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(x_142, x_143, x_141);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec(x_144);
x_146 = l_Lake_LeanOption_decodeToml___closed__3;
x_147 = l_Array_append___rarg(x_146, x_145);
lean_dec(x_145);
x_148 = l_Lake_LeanOption_decodeToml___closed__12;
x_149 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(x_142, x_148, x_141);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
lean_free_object(x_1);
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = l_Array_append___rarg(x_147, x_151);
lean_dec(x_151);
x_153 = l_Array_isEmpty___rarg(x_152);
if (x_153 == 0)
{
lean_ctor_set(x_149, 0, x_152);
return x_149;
}
else
{
lean_object* x_154; 
lean_dec(x_152);
lean_free_object(x_149);
x_154 = l_Lake_LeanOption_decodeToml___closed__6;
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_155 = lean_ctor_get(x_149, 0);
lean_inc(x_155);
lean_dec(x_149);
x_156 = l_Array_append___rarg(x_147, x_155);
lean_dec(x_155);
x_157 = l_Array_isEmpty___rarg(x_156);
if (x_157 == 0)
{
lean_object* x_158; 
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_156);
return x_158;
}
else
{
lean_object* x_159; 
lean_dec(x_156);
x_159 = l_Lake_LeanOption_decodeToml___closed__6;
return x_159;
}
}
}
else
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_149);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_149, 0);
x_162 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_161);
lean_ctor_set(x_1, 0, x_162);
x_163 = l_Array_isEmpty___rarg(x_147);
if (x_163 == 0)
{
lean_dec(x_1);
lean_ctor_set_tag(x_149, 0);
lean_ctor_set(x_149, 0, x_147);
return x_149;
}
else
{
lean_dec(x_147);
lean_ctor_set(x_149, 0, x_1);
return x_149;
}
}
else
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_149, 0);
lean_inc(x_164);
lean_dec(x_149);
x_165 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_164);
lean_ctor_set(x_1, 0, x_165);
x_166 = l_Array_isEmpty___rarg(x_147);
if (x_166 == 0)
{
lean_object* x_167; 
lean_dec(x_1);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_147);
return x_167;
}
else
{
lean_object* x_168; 
lean_dec(x_147);
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_1);
return x_168;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_144, 0);
lean_inc(x_169);
lean_dec(x_144);
x_170 = l_Lake_LeanOption_decodeToml___closed__12;
x_171 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(x_142, x_170, x_141);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = l_Lake_LeanOption_decodeToml___closed__3;
x_175 = l_Array_append___rarg(x_174, x_173);
lean_dec(x_173);
x_176 = l_Lake_LeanOption_decodeToml___closed__4;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_176);
lean_ctor_set(x_1, 0, x_169);
x_177 = l_Array_isEmpty___rarg(x_175);
if (x_177 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_171, 0, x_175);
return x_171;
}
else
{
lean_dec(x_175);
lean_ctor_set_tag(x_171, 1);
lean_ctor_set(x_171, 0, x_1);
return x_171;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = lean_ctor_get(x_171, 0);
lean_inc(x_178);
lean_dec(x_171);
x_179 = l_Lake_LeanOption_decodeToml___closed__3;
x_180 = l_Array_append___rarg(x_179, x_178);
lean_dec(x_178);
x_181 = l_Lake_LeanOption_decodeToml___closed__4;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_181);
lean_ctor_set(x_1, 0, x_169);
x_182 = l_Array_isEmpty___rarg(x_180);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_1);
x_183 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_183, 0, x_180);
return x_183;
}
else
{
lean_object* x_184; 
lean_dec(x_180);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_1);
return x_184;
}
}
}
else
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_171);
if (x_185 == 0)
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_171, 0);
x_187 = l_Lake_LeanOption_decodeToml___closed__7;
if (x_187 == 0)
{
lean_object* x_188; 
lean_free_object(x_171);
lean_dec(x_186);
lean_dec(x_169);
lean_free_object(x_1);
x_188 = l_Lake_LeanOption_decodeToml___closed__8;
return x_188;
}
else
{
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_186);
lean_ctor_set(x_1, 0, x_169);
lean_ctor_set(x_171, 0, x_1);
return x_171;
}
}
else
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_171, 0);
lean_inc(x_189);
lean_dec(x_171);
x_190 = l_Lake_LeanOption_decodeToml___closed__7;
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_189);
lean_dec(x_169);
lean_free_object(x_1);
x_191 = l_Lake_LeanOption_decodeToml___closed__8;
return x_191;
}
else
{
lean_object* x_192; 
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_189);
lean_ctor_set(x_1, 0, x_169);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_1);
return x_192;
}
}
}
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = lean_ctor_get(x_1, 0);
x_194 = lean_ctor_get(x_1, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_1);
x_195 = l_Lake_LeanOption_decodeToml___closed__10;
lean_inc(x_193);
lean_inc(x_194);
x_196 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(x_194, x_195, x_193);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec(x_196);
x_198 = l_Lake_LeanOption_decodeToml___closed__3;
x_199 = l_Array_append___rarg(x_198, x_197);
lean_dec(x_197);
x_200 = l_Lake_LeanOption_decodeToml___closed__12;
x_201 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(x_194, x_200, x_193);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = l_Array_append___rarg(x_199, x_202);
lean_dec(x_202);
x_205 = l_Array_isEmpty___rarg(x_204);
if (x_205 == 0)
{
lean_object* x_206; 
if (lean_is_scalar(x_203)) {
 x_206 = lean_alloc_ctor(0, 1, 0);
} else {
 x_206 = x_203;
}
lean_ctor_set(x_206, 0, x_204);
return x_206;
}
else
{
lean_object* x_207; 
lean_dec(x_204);
lean_dec(x_203);
x_207 = l_Lake_LeanOption_decodeToml___closed__6;
return x_207;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_201, 0);
lean_inc(x_208);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_209 = x_201;
} else {
 lean_dec_ref(x_201);
 x_209 = lean_box(0);
}
x_210 = lean_box(0);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_208);
x_212 = l_Array_isEmpty___rarg(x_199);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_211);
if (lean_is_scalar(x_209)) {
 x_213 = lean_alloc_ctor(0, 1, 0);
} else {
 x_213 = x_209;
 lean_ctor_set_tag(x_213, 0);
}
lean_ctor_set(x_213, 0, x_199);
return x_213;
}
else
{
lean_object* x_214; 
lean_dec(x_199);
if (lean_is_scalar(x_209)) {
 x_214 = lean_alloc_ctor(1, 1, 0);
} else {
 x_214 = x_209;
}
lean_ctor_set(x_214, 0, x_211);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_196, 0);
lean_inc(x_215);
lean_dec(x_196);
x_216 = l_Lake_LeanOption_decodeToml___closed__12;
x_217 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(x_194, x_216, x_193);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
x_220 = l_Lake_LeanOption_decodeToml___closed__3;
x_221 = l_Array_append___rarg(x_220, x_218);
lean_dec(x_218);
x_222 = l_Lake_LeanOption_decodeToml___closed__4;
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_215);
lean_ctor_set(x_223, 1, x_222);
x_224 = l_Array_isEmpty___rarg(x_221);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_223);
if (lean_is_scalar(x_219)) {
 x_225 = lean_alloc_ctor(0, 1, 0);
} else {
 x_225 = x_219;
}
lean_ctor_set(x_225, 0, x_221);
return x_225;
}
else
{
lean_object* x_226; 
lean_dec(x_221);
if (lean_is_scalar(x_219)) {
 x_226 = lean_alloc_ctor(1, 1, 0);
} else {
 x_226 = x_219;
 lean_ctor_set_tag(x_226, 1);
}
lean_ctor_set(x_226, 0, x_223);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_227 = lean_ctor_get(x_217, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 x_228 = x_217;
} else {
 lean_dec_ref(x_217);
 x_228 = lean_box(0);
}
x_229 = l_Lake_LeanOption_decodeToml___closed__7;
if (x_229 == 0)
{
lean_object* x_230; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_215);
x_230 = l_Lake_LeanOption_decodeToml___closed__8;
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; 
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_215);
lean_ctor_set(x_231, 1, x_227);
if (lean_is_scalar(x_228)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_228;
}
lean_ctor_set(x_232, 0, x_231);
return x_232;
}
}
}
}
}
default: 
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_1);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_1, 1);
lean_dec(x_234);
x_235 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_235);
x_236 = lean_box(0);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_1);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_array_mk(x_237);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_240 = lean_ctor_get(x_1, 0);
lean_inc(x_240);
lean_dec(x_1);
x_241 = l_Lake_LeanOption_decodeToml___closed__1;
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_box(0);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_245 = lean_array_mk(x_244);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_245);
return x_246;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__5(x_1, x_2);
lean_dec(x_1);
return x_3;
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
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_decodeLeanOptions___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_decodeLeanOptions___closed__1;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_dec(x_3);
x_4 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set(x_1, 1, x_4);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_array_mk(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lake_LeanOption_decodeToml___closed__1;
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_mk(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
case 2:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = l_Lake_LeanOption_decodeToml___closed__1;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_mk(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lake_LeanOption_decodeToml___closed__1;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_array_mk(x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
case 5:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_dec(x_1);
x_31 = l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1(x_30);
lean_dec(x_30);
return x_31;
}
case 6:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_array_get_size(x_33);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_lt(x_35, x_34);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_33);
x_37 = l_Lake_decodeLeanOptions___closed__2;
return x_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_34, x_34);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_34);
lean_dec(x_33);
x_39 = l_Lake_decodeLeanOptions___closed__2;
return x_39;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_42 = l_Lake_decodeLeanOptions___closed__2;
x_43 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__3(x_33, x_40, x_41, x_42);
lean_dec(x_33);
return x_43;
}
}
}
default: 
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_46);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_array_mk(x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = l_Lake_LeanOption_decodeToml___closed__1;
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_mk(x_55);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
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
LEAN_EXPORT lean_object* l_Lake_StdVer_decodeToml(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_Lake_StdVer_parse(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_box(0);
lean_ctor_set(x_1, 1, x_7);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_array_mk(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
lean_ctor_set(x_1, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_mk(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
else
{
uint8_t x_16; 
lean_free_object(x_1);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_5);
if (x_16 == 0)
{
return x_5;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_5, 0);
lean_inc(x_17);
lean_dec(x_5);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_21 = l_Lake_StdVer_parse(x_20);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_23 = x_21;
} else {
 lean_dec_ref(x_21);
 x_23 = lean_box(0);
}
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = lean_array_mk(x_26);
if (lean_is_scalar(x_23)) {
 x_28 = lean_alloc_ctor(0, 1, 0);
} else {
 x_28 = x_23;
}
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_19);
x_29 = lean_ctor_get(x_21, 0);
lean_inc(x_29);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_30 = x_21;
} else {
 lean_dec_ref(x_21);
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
}
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = l_Lake_Glob_decodeToml___closed__2;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_mk_array(x_35, x_34);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
case 3:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lake_Glob_decodeToml___closed__2;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_mk_array(x_41, x_40);
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
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_46);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_mk_array(x_47, x_1);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = l_Lake_Glob_decodeToml___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_mk_array(x_53, x_52);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlStdVer(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_StdVer_decodeToml(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_StrPat_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(lean_object* x_1) {
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
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_StrPat_decodeToml___spec__2(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_StrPat_decodeToml___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
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
x_24 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lake_Glob_decodeToml___closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_array(x_14, x_13);
x_3 = x_15;
goto block_8;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lake_Glob_decodeToml___closed__2;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_mk_array(x_19, x_18);
x_3 = x_20;
goto block_8;
}
default: 
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_mk_array(x_24, x_2);
x_3 = x_25;
goto block_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lake_Glob_decodeToml___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_mk_array(x_29, x_28);
x_3 = x_30;
goto block_8;
}
}
}
block_8:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lake_StrPat_decodeToml___spec__5(x_1, x_4, x_5, x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
lean_inc(x_2);
x_4 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_3, x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3___closed__1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4(x_2, x_8);
lean_dec(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_free_object(x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_4, 0, x_14);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
lean_ctor_set(x_4, 0, x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4(x_2, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
lean_inc(x_2);
x_4 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_3, x_2, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3___closed__1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2(x_2, x_8);
lean_dec(x_2);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_free_object(x_4);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_9, 0);
lean_ctor_set(x_4, 0, x_14);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
lean_ctor_set(x_4, 0, x_15);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_4, 0);
lean_inc(x_17);
lean_dec(x_4);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2(x_2, x_18);
lean_dec(x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_21 = x_19;
} else {
 lean_dec_ref(x_19);
 x_21 = lean_box(0);
}
if (lean_is_scalar(x_21)) {
 x_22 = lean_alloc_ctor(0, 1, 0);
} else {
 x_22 = x_21;
}
lean_ctor_set(x_22, 0, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_24 = x_19;
} else {
 lean_dec_ref(x_19);
 x_24 = lean_box(0);
}
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_StrPat_decodeToml___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_StrPat_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("startsWith", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_StrPat_decodeToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_StrPat_decodeToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_StrPat_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("preset", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_StrPat_decodeToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_StrPat_decodeToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_StrPat_decodeToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected 'startsWith' or 'preset'", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lake_StrPat_decodeToml___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_StrPat_decodeToml___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_StrPat_decodeToml___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown preset '", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_StrPat_decodeToml___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
x_5 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set(x_1, 1, x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_mk(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lake_LeanOption_decodeToml___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_mk(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lake_LeanOption_decodeToml___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_mk(x_21);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
case 3:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lake_LeanOption_decodeToml___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_mk(x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
case 5:
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
return x_32;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_32, 0, x_38);
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
case 6:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_1);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_1, 0);
x_44 = lean_ctor_get(x_1, 1);
x_45 = l_Lake_StrPat_decodeToml___closed__2;
lean_inc(x_44);
x_46 = l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3(x_44, x_45);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_free_object(x_1);
lean_dec(x_44);
lean_dec(x_43);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_46);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_46, 0);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_free_object(x_46);
x_52 = l_Lake_StrPat_decodeToml___closed__4;
x_53 = l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__6(x_44, x_52);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
lean_free_object(x_1);
lean_dec(x_43);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
return x_53;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
else
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_53);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_53, 0);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = l_Lake_StrPat_decodeToml___closed__5;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_59);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_array_mk(x_61);
lean_ctor_set_tag(x_53, 0);
lean_ctor_set(x_53, 0, x_62);
return x_53;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
lean_dec(x_58);
x_64 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_2, x_63);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = 1;
x_66 = l_Lake_StrPat_decodeToml___closed__6;
x_67 = l_Lean_Name_toString(x_63, x_65, x_66);
x_68 = l_Lake_StrPat_decodeToml___closed__7;
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_70 = l_Lake_StrPat_decodeToml___closed__8;
x_71 = lean_string_append(x_69, x_70);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_71);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_array_mk(x_73);
lean_ctor_set_tag(x_53, 0);
lean_ctor_set(x_53, 0, x_74);
return x_53;
}
else
{
lean_object* x_75; 
lean_dec(x_63);
lean_free_object(x_1);
lean_dec(x_43);
x_75 = lean_ctor_get(x_64, 0);
lean_inc(x_75);
lean_dec(x_64);
lean_ctor_set(x_53, 0, x_75);
return x_53;
}
}
}
else
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_53, 0);
lean_inc(x_76);
lean_dec(x_53);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = l_Lake_StrPat_decodeToml___closed__5;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_77);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_array_mk(x_79);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_76, 0);
lean_inc(x_82);
lean_dec(x_76);
x_83 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_2, x_82);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_84 = 1;
x_85 = l_Lake_StrPat_decodeToml___closed__6;
x_86 = l_Lean_Name_toString(x_82, x_84, x_85);
x_87 = l_Lake_StrPat_decodeToml___closed__7;
x_88 = lean_string_append(x_87, x_86);
lean_dec(x_86);
x_89 = l_Lake_StrPat_decodeToml___closed__8;
x_90 = lean_string_append(x_88, x_89);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_90);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_array_mk(x_92);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_82);
lean_free_object(x_1);
lean_dec(x_43);
x_95 = lean_ctor_get(x_83, 0);
lean_inc(x_95);
lean_dec(x_83);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
}
}
else
{
uint8_t x_97; 
lean_free_object(x_1);
lean_dec(x_44);
lean_dec(x_43);
x_97 = !lean_is_exclusive(x_51);
if (x_97 == 0)
{
lean_ctor_set_tag(x_51, 2);
return x_46;
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_51, 0);
lean_inc(x_98);
lean_dec(x_51);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_46, 0, x_99);
return x_46;
}
}
}
else
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_46, 0);
lean_inc(x_100);
lean_dec(x_46);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = l_Lake_StrPat_decodeToml___closed__4;
x_102 = l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__6(x_44, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_free_object(x_1);
lean_dec(x_43);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(0, 1, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_103);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_102, 0);
lean_inc(x_106);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_107 = x_102;
} else {
 lean_dec_ref(x_102);
 x_107 = lean_box(0);
}
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = l_Lake_StrPat_decodeToml___closed__5;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_108);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_1);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_array_mk(x_110);
if (lean_is_scalar(x_107)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_107;
 lean_ctor_set_tag(x_112, 0);
}
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_106, 0);
lean_inc(x_113);
lean_dec(x_106);
x_114 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_2, x_113);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_115 = 1;
x_116 = l_Lake_StrPat_decodeToml___closed__6;
x_117 = l_Lean_Name_toString(x_113, x_115, x_116);
x_118 = l_Lake_StrPat_decodeToml___closed__7;
x_119 = lean_string_append(x_118, x_117);
lean_dec(x_117);
x_120 = l_Lake_StrPat_decodeToml___closed__8;
x_121 = lean_string_append(x_119, x_120);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_121);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_1);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_mk(x_123);
if (lean_is_scalar(x_107)) {
 x_125 = lean_alloc_ctor(0, 1, 0);
} else {
 x_125 = x_107;
 lean_ctor_set_tag(x_125, 0);
}
lean_ctor_set(x_125, 0, x_124);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_113);
lean_free_object(x_1);
lean_dec(x_43);
x_126 = lean_ctor_get(x_114, 0);
lean_inc(x_126);
lean_dec(x_114);
if (lean_is_scalar(x_107)) {
 x_127 = lean_alloc_ctor(1, 1, 0);
} else {
 x_127 = x_107;
}
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_free_object(x_1);
lean_dec(x_44);
lean_dec(x_43);
x_128 = lean_ctor_get(x_100, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 x_129 = x_100;
} else {
 lean_dec_ref(x_100);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(2, 1, 0);
} else {
 x_130 = x_129;
 lean_ctor_set_tag(x_130, 2);
}
lean_ctor_set(x_130, 0, x_128);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_1, 0);
x_133 = lean_ctor_get(x_1, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_1);
x_134 = l_Lake_StrPat_decodeToml___closed__2;
lean_inc(x_133);
x_135 = l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3(x_133, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_133);
lean_dec(x_132);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_137 = x_135;
} else {
 lean_dec_ref(x_135);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(0, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 x_140 = x_135;
} else {
 lean_dec_ref(x_135);
 x_140 = lean_box(0);
}
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_140);
x_141 = l_Lake_StrPat_decodeToml___closed__4;
x_142 = l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__6(x_133, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_132);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_144 = x_142;
} else {
 lean_dec_ref(x_142);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(0, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_147 = x_142;
} else {
 lean_dec_ref(x_142);
 x_147 = lean_box(0);
}
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_148 = l_Lake_StrPat_decodeToml___closed__5;
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_132);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_box(0);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_array_mk(x_151);
if (lean_is_scalar(x_147)) {
 x_153 = lean_alloc_ctor(0, 1, 0);
} else {
 x_153 = x_147;
 lean_ctor_set_tag(x_153, 0);
}
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_146, 0);
lean_inc(x_154);
lean_dec(x_146);
x_155 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_2, x_154);
if (lean_obj_tag(x_155) == 0)
{
uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_156 = 1;
x_157 = l_Lake_StrPat_decodeToml___closed__6;
x_158 = l_Lean_Name_toString(x_154, x_156, x_157);
x_159 = l_Lake_StrPat_decodeToml___closed__7;
x_160 = lean_string_append(x_159, x_158);
lean_dec(x_158);
x_161 = l_Lake_StrPat_decodeToml___closed__8;
x_162 = lean_string_append(x_160, x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_132);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_array_mk(x_165);
if (lean_is_scalar(x_147)) {
 x_167 = lean_alloc_ctor(0, 1, 0);
} else {
 x_167 = x_147;
 lean_ctor_set_tag(x_167, 0);
}
lean_ctor_set(x_167, 0, x_166);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_154);
lean_dec(x_132);
x_168 = lean_ctor_get(x_155, 0);
lean_inc(x_168);
lean_dec(x_155);
if (lean_is_scalar(x_147)) {
 x_169 = lean_alloc_ctor(1, 1, 0);
} else {
 x_169 = x_147;
}
lean_ctor_set(x_169, 0, x_168);
return x_169;
}
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_133);
lean_dec(x_132);
x_170 = lean_ctor_get(x_139, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 x_171 = x_139;
} else {
 lean_dec_ref(x_139);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(2, 1, 0);
} else {
 x_172 = x_171;
 lean_ctor_set_tag(x_172, 2);
}
lean_ctor_set(x_172, 0, x_170);
if (lean_is_scalar(x_140)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_140;
}
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
}
default: 
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_1);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_175 = lean_ctor_get(x_1, 1);
lean_dec(x_175);
x_176 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_176);
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_1);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_array_mk(x_178);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_181 = lean_ctor_get(x_1, 0);
lean_inc(x_181);
lean_dec(x_1);
x_182 = l_Lake_LeanOption_decodeToml___closed__1;
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
x_186 = lean_array_mk(x_185);
x_187 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_187, 0, x_186);
return x_187;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_StrPat_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_StrPat_decodeToml___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_StrPat_decodeToml___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_StrPat_decodeToml___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_decodeToml___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_StrPat_decodeToml___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_StrPat_decodeToml___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_StrPat_decodeToml(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlStrPat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lake_StrPat_decodeToml(x_1, x_2);
return x_3;
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
x_12 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_16 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_22 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_30 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_38 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_46 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_475 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_482 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_486 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_382 = l_Lake_decodeLeanOptions___closed__1;
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
x_388 = l_Lake_decodeLeanOptions___closed__1;
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
x_370 = l_Lake_decodeLeanOptions___closed__1;
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
x_376 = l_Lake_decodeLeanOptions___closed__1;
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
x_315 = l_Lake_decodeLeanOptions___closed__1;
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
x_324 = l_Lake_decodeLeanOptions___closed__1;
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
x_331 = l_Lake_decodeLeanOptions___closed__1;
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
x_338 = l_Lake_decodeLeanOptions___closed__1;
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
x_345 = l_Lake_decodeLeanOptions___closed__1;
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
x_347 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_346);
lean_dec(x_346);
if (lean_obj_tag(x_347) == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
lean_dec(x_347);
x_349 = l_Array_append___rarg(x_17, x_348);
lean_dec(x_348);
x_350 = l_Lake_decodeLeanOptions___closed__1;
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
x_358 = l_Lake_decodeLeanOptions___closed__1;
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
x_365 = l_Lake_decodeLeanOptions___closed__1;
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
x_260 = l_Lake_decodeLeanOptions___closed__1;
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
x_269 = l_Lake_decodeLeanOptions___closed__1;
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
x_276 = l_Lake_decodeLeanOptions___closed__1;
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
x_283 = l_Lake_decodeLeanOptions___closed__1;
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
x_290 = l_Lake_decodeLeanOptions___closed__1;
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
x_292 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_291);
lean_dec(x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
lean_dec(x_292);
x_294 = l_Array_append___rarg(x_19, x_293);
lean_dec(x_293);
x_295 = l_Lake_decodeLeanOptions___closed__1;
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
x_303 = l_Lake_decodeLeanOptions___closed__1;
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
x_310 = l_Lake_decodeLeanOptions___closed__1;
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
x_205 = l_Lake_decodeLeanOptions___closed__1;
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
x_214 = l_Lake_decodeLeanOptions___closed__1;
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
x_221 = l_Lake_decodeLeanOptions___closed__1;
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
x_228 = l_Lake_decodeLeanOptions___closed__1;
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
x_235 = l_Lake_decodeLeanOptions___closed__1;
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
x_237 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_236);
lean_dec(x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
lean_dec(x_237);
x_239 = l_Array_append___rarg(x_21, x_238);
lean_dec(x_238);
x_240 = l_Lake_decodeLeanOptions___closed__1;
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
x_248 = l_Lake_decodeLeanOptions___closed__1;
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
x_255 = l_Lake_decodeLeanOptions___closed__1;
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
x_150 = l_Lake_decodeLeanOptions___closed__1;
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
x_159 = l_Lake_decodeLeanOptions___closed__1;
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
x_166 = l_Lake_decodeLeanOptions___closed__1;
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
x_173 = l_Lake_decodeLeanOptions___closed__1;
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
x_180 = l_Lake_decodeLeanOptions___closed__1;
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
x_182 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_181);
lean_dec(x_181);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Array_append___rarg(x_23, x_183);
lean_dec(x_183);
x_185 = l_Lake_decodeLeanOptions___closed__1;
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
x_193 = l_Lake_decodeLeanOptions___closed__1;
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
x_200 = l_Lake_decodeLeanOptions___closed__1;
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
x_95 = l_Lake_decodeLeanOptions___closed__1;
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
x_104 = l_Lake_decodeLeanOptions___closed__1;
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
x_111 = l_Lake_decodeLeanOptions___closed__1;
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
x_118 = l_Lake_decodeLeanOptions___closed__1;
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
x_125 = l_Lake_decodeLeanOptions___closed__1;
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
x_127 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_126);
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l_Array_append___rarg(x_25, x_128);
lean_dec(x_128);
x_130 = l_Lake_decodeLeanOptions___closed__1;
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
x_138 = l_Lake_decodeLeanOptions___closed__1;
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
x_145 = l_Lake_decodeLeanOptions___closed__1;
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
x_31 = l_Lake_decodeLeanOptions___closed__1;
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
x_41 = l_Lake_decodeLeanOptions___closed__1;
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
x_49 = l_Lake_decodeLeanOptions___closed__1;
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
x_57 = l_Lake_decodeLeanOptions___closed__1;
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
x_65 = l_Lake_decodeLeanOptions___closed__1;
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
x_68 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_67);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Array_append___rarg(x_27, x_69);
lean_dec(x_69);
x_71 = l_Lake_decodeLeanOptions___closed__1;
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
x_81 = l_Lake_decodeLeanOptions___closed__1;
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
x_89 = l_Lake_decodeLeanOptions___closed__1;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_PackageConfig_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_PackageConfig_decodeToml___spec__1(lean_object* x_1) {
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
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_PackageConfig_decodeToml___spec__2(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_17 = l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4(x_2, x_16);
lean_dec(x_2);
return x_17;
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
x_3 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_1 = lean_mk_string_unchecked("reservoir", 9, 9);
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
x_1 = lean_mk_string_unchecked("readmeFile", 10, 10);
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
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("README.md", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("licenseFiles", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LICENSE", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__15;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_PackageConfig_decodeToml___closed__16;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("license", 7, 7);
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
x_1 = lean_mk_string_unchecked("homepage", 8, 8);
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
x_1 = lean_mk_string_unchecked("keywords", 8, 8);
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
x_1 = lean_mk_string_unchecked("description", 11, 11);
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
x_1 = lean_mk_string_unchecked("versionTags", 11, 11);
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
x_1 = lean_mk_string_unchecked("version", 7, 7);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_PackageConfig_decodeToml___closed__30;
x_2 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lintDriverArgs", 14, 14);
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
x_1 = lean_mk_string_unchecked("lintDriver", 10, 10);
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
static uint8_t _init_l_Lake_PackageConfig_decodeToml___closed__36() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_PackageConfig_decodeToml___closed__37() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("testDriver", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__38;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("testRunner", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__40;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__42() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("preferReleaseBuild", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__43() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__42;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__44() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("buildArchive", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__45() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__44;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__46() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("releaseRepo", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__47() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__46;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__48() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("irDir", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__49() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__48;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__50() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__51() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__50;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__52() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nativeLibDir", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__53() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__52;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__54() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanLibDir", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__55() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__54;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__56() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("buildDir", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__57() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__56;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__58() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("srcDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__59() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__58;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__60() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__61() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("precompileModules", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__62() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__61;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_PackageConfig_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_1119; lean_object* x_1120; 
x_1119 = l_Lake_LeanOption_decodeToml___closed__10;
lean_inc(x_1);
x_1120 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__3(x_1, x_1119, x_2);
if (lean_obj_tag(x_1120) == 0)
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1121 = lean_ctor_get(x_1120, 0);
lean_inc(x_1121);
lean_dec(x_1120);
x_1122 = l_Lake_LeanOption_decodeToml___closed__3;
x_1123 = l_Array_append___rarg(x_1122, x_1121);
lean_dec(x_1121);
x_1124 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_1124;
x_10 = x_1123;
goto block_1118;
}
else
{
lean_object* x_1125; lean_object* x_1126; 
x_1125 = lean_ctor_get(x_1120, 0);
lean_inc(x_1125);
lean_dec(x_1120);
x_1126 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_1125;
x_10 = x_1126;
goto block_1118;
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
block_1118:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
x_11 = l_Lake_stringToLegalOrSimpleName(x_9);
x_1076 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_1077 = l_Lake_PackageConfig_decodeToml___closed__62;
lean_inc(x_1);
x_1078 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1076, x_1077, x_1);
if (lean_obj_tag(x_1078) == 0)
{
uint8_t x_1079; 
x_1079 = 0;
x_12 = x_1079;
x_13 = x_10;
goto block_1075;
}
else
{
lean_object* x_1080; lean_object* x_1081; 
x_1080 = lean_ctor_get(x_1078, 0);
lean_inc(x_1080);
lean_dec(x_1078);
x_1081 = lean_ctor_get(x_1080, 1);
lean_inc(x_1081);
lean_dec(x_1080);
switch (lean_obj_tag(x_1081)) {
case 0:
{
uint8_t x_1082; 
x_1082 = !lean_is_exclusive(x_1081);
if (x_1082 == 0)
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; uint8_t x_1088; 
x_1083 = lean_ctor_get(x_1081, 1);
lean_dec(x_1083);
x_1084 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_1081, 1, x_1084);
x_1085 = lean_unsigned_to_nat(1u);
x_1086 = lean_mk_array(x_1085, x_1081);
x_1087 = l_Array_append___rarg(x_10, x_1086);
lean_dec(x_1086);
x_1088 = 0;
x_12 = x_1088;
x_13 = x_1087;
goto block_1075;
}
else
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; uint8_t x_1095; 
x_1089 = lean_ctor_get(x_1081, 0);
lean_inc(x_1089);
lean_dec(x_1081);
x_1090 = l_Lake_LeanConfig_decodeToml___closed__20;
x_1091 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1091, 0, x_1089);
lean_ctor_set(x_1091, 1, x_1090);
x_1092 = lean_unsigned_to_nat(1u);
x_1093 = lean_mk_array(x_1092, x_1091);
x_1094 = l_Array_append___rarg(x_10, x_1093);
lean_dec(x_1093);
x_1095 = 0;
x_12 = x_1095;
x_13 = x_1094;
goto block_1075;
}
}
case 2:
{
lean_object* x_1096; lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; uint8_t x_1102; 
x_1096 = lean_ctor_get(x_1081, 0);
lean_inc(x_1096);
lean_dec(x_1081);
x_1097 = l_Lake_LeanConfig_decodeToml___closed__20;
x_1098 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1098, 0, x_1096);
lean_ctor_set(x_1098, 1, x_1097);
x_1099 = lean_unsigned_to_nat(1u);
x_1100 = lean_mk_array(x_1099, x_1098);
x_1101 = l_Array_append___rarg(x_10, x_1100);
lean_dec(x_1100);
x_1102 = 0;
x_12 = x_1102;
x_13 = x_1101;
goto block_1075;
}
case 3:
{
uint8_t x_1103; 
x_1103 = lean_ctor_get_uint8(x_1081, sizeof(void*)*1);
lean_dec(x_1081);
x_12 = x_1103;
x_13 = x_10;
goto block_1075;
}
default: 
{
uint8_t x_1104; 
x_1104 = !lean_is_exclusive(x_1081);
if (x_1104 == 0)
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; uint8_t x_1110; 
x_1105 = lean_ctor_get(x_1081, 1);
lean_dec(x_1105);
x_1106 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_1081, 0);
lean_ctor_set(x_1081, 1, x_1106);
x_1107 = lean_unsigned_to_nat(1u);
x_1108 = lean_mk_array(x_1107, x_1081);
x_1109 = l_Array_append___rarg(x_10, x_1108);
lean_dec(x_1108);
x_1110 = 0;
x_12 = x_1110;
x_13 = x_1109;
goto block_1075;
}
else
{
lean_object* x_1111; lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; lean_object* x_1116; uint8_t x_1117; 
x_1111 = lean_ctor_get(x_1081, 0);
lean_inc(x_1111);
lean_dec(x_1081);
x_1112 = l_Lake_LeanConfig_decodeToml___closed__20;
x_1113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1113, 0, x_1111);
lean_ctor_set(x_1113, 1, x_1112);
x_1114 = lean_unsigned_to_nat(1u);
x_1115 = lean_mk_array(x_1114, x_1113);
x_1116 = l_Array_append___rarg(x_10, x_1115);
lean_dec(x_1115);
x_1117 = 0;
x_12 = x_1117;
x_13 = x_1116;
goto block_1075;
}
}
}
}
block_1075:
{
lean_object* x_14; lean_object* x_15; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
x_1021 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_1022 = l_Lake_PackageConfig_decodeToml___closed__2;
lean_inc(x_1);
x_1023 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1021, x_1022, x_1);
if (lean_obj_tag(x_1023) == 0)
{
lean_object* x_1024; 
x_1024 = l_Lake_decodeLeanOptions___closed__1;
x_14 = x_1024;
x_15 = x_13;
goto block_1020;
}
else
{
lean_object* x_1025; lean_object* x_1026; 
x_1025 = lean_ctor_get(x_1023, 0);
lean_inc(x_1025);
lean_dec(x_1023);
x_1026 = lean_ctor_get(x_1025, 1);
lean_inc(x_1026);
lean_dec(x_1025);
switch (lean_obj_tag(x_1026)) {
case 0:
{
uint8_t x_1027; 
x_1027 = !lean_is_exclusive(x_1026);
if (x_1027 == 0)
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; 
x_1028 = lean_ctor_get(x_1026, 1);
lean_dec(x_1028);
x_1029 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_1026, 1, x_1029);
x_1030 = lean_unsigned_to_nat(1u);
x_1031 = lean_mk_array(x_1030, x_1026);
x_1032 = l_Array_append___rarg(x_13, x_1031);
lean_dec(x_1031);
x_1033 = l_Lake_decodeLeanOptions___closed__1;
x_14 = x_1033;
x_15 = x_1032;
goto block_1020;
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1034 = lean_ctor_get(x_1026, 0);
lean_inc(x_1034);
lean_dec(x_1026);
x_1035 = l_Lake_LeanConfig_decodeToml___closed__5;
x_1036 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1036, 0, x_1034);
lean_ctor_set(x_1036, 1, x_1035);
x_1037 = lean_unsigned_to_nat(1u);
x_1038 = lean_mk_array(x_1037, x_1036);
x_1039 = l_Array_append___rarg(x_13, x_1038);
lean_dec(x_1038);
x_1040 = l_Lake_decodeLeanOptions___closed__1;
x_14 = x_1040;
x_15 = x_1039;
goto block_1020;
}
}
case 2:
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1041 = lean_ctor_get(x_1026, 0);
lean_inc(x_1041);
lean_dec(x_1026);
x_1042 = l_Lake_LeanConfig_decodeToml___closed__5;
x_1043 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1043, 0, x_1041);
lean_ctor_set(x_1043, 1, x_1042);
x_1044 = lean_unsigned_to_nat(1u);
x_1045 = lean_mk_array(x_1044, x_1043);
x_1046 = l_Array_append___rarg(x_13, x_1045);
lean_dec(x_1045);
x_1047 = l_Lake_decodeLeanOptions___closed__1;
x_14 = x_1047;
x_15 = x_1046;
goto block_1020;
}
case 3:
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; 
x_1048 = lean_ctor_get(x_1026, 0);
lean_inc(x_1048);
lean_dec(x_1026);
x_1049 = l_Lake_LeanConfig_decodeToml___closed__5;
x_1050 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1050, 0, x_1048);
lean_ctor_set(x_1050, 1, x_1049);
x_1051 = lean_unsigned_to_nat(1u);
x_1052 = lean_mk_array(x_1051, x_1050);
x_1053 = l_Array_append___rarg(x_13, x_1052);
lean_dec(x_1052);
x_1054 = l_Lake_decodeLeanOptions___closed__1;
x_14 = x_1054;
x_15 = x_1053;
goto block_1020;
}
case 5:
{
lean_object* x_1055; lean_object* x_1056; 
x_1055 = lean_ctor_get(x_1026, 1);
lean_inc(x_1055);
lean_dec(x_1026);
x_1056 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_1055);
lean_dec(x_1055);
if (lean_obj_tag(x_1056) == 0)
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1057 = lean_ctor_get(x_1056, 0);
lean_inc(x_1057);
lean_dec(x_1056);
x_1058 = l_Array_append___rarg(x_13, x_1057);
lean_dec(x_1057);
x_1059 = l_Lake_decodeLeanOptions___closed__1;
x_14 = x_1059;
x_15 = x_1058;
goto block_1020;
}
else
{
lean_object* x_1060; 
x_1060 = lean_ctor_get(x_1056, 0);
lean_inc(x_1060);
lean_dec(x_1056);
x_14 = x_1060;
x_15 = x_13;
goto block_1020;
}
}
default: 
{
uint8_t x_1061; 
x_1061 = !lean_is_exclusive(x_1026);
if (x_1061 == 0)
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; 
x_1062 = lean_ctor_get(x_1026, 1);
lean_dec(x_1062);
x_1063 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_1026, 0);
lean_ctor_set(x_1026, 1, x_1063);
x_1064 = lean_unsigned_to_nat(1u);
x_1065 = lean_mk_array(x_1064, x_1026);
x_1066 = l_Array_append___rarg(x_13, x_1065);
lean_dec(x_1065);
x_1067 = l_Lake_decodeLeanOptions___closed__1;
x_14 = x_1067;
x_15 = x_1066;
goto block_1020;
}
else
{
lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1068 = lean_ctor_get(x_1026, 0);
lean_inc(x_1068);
lean_dec(x_1026);
x_1069 = l_Lake_LeanConfig_decodeToml___closed__5;
x_1070 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1070, 0, x_1068);
lean_ctor_set(x_1070, 1, x_1069);
x_1071 = lean_unsigned_to_nat(1u);
x_1072 = lean_mk_array(x_1071, x_1070);
x_1073 = l_Array_append___rarg(x_13, x_1072);
lean_dec(x_1072);
x_1074 = l_Lake_decodeLeanOptions___closed__1;
x_14 = x_1074;
x_15 = x_1073;
goto block_1020;
}
}
}
}
block_1020:
{
lean_object* x_16; lean_object* x_17; lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_986 = l_Lake_PackageConfig_decodeToml___closed__59;
lean_inc(x_1);
x_987 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_985, x_986, x_1);
if (lean_obj_tag(x_987) == 0)
{
lean_object* x_988; 
x_988 = l_Lake_PackageConfig_decodeToml___closed__60;
x_16 = x_988;
x_17 = x_15;
goto block_984;
}
else
{
lean_object* x_989; lean_object* x_990; 
x_989 = lean_ctor_get(x_987, 0);
lean_inc(x_989);
lean_dec(x_987);
x_990 = lean_ctor_get(x_989, 1);
lean_inc(x_990);
lean_dec(x_989);
switch (lean_obj_tag(x_990)) {
case 0:
{
lean_object* x_991; 
x_991 = lean_ctor_get(x_990, 1);
lean_inc(x_991);
lean_dec(x_990);
x_16 = x_991;
x_17 = x_15;
goto block_984;
}
case 2:
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_992 = lean_ctor_get(x_990, 0);
lean_inc(x_992);
lean_dec(x_990);
x_993 = l_Lake_Glob_decodeToml___closed__2;
x_994 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_994, 0, x_992);
lean_ctor_set(x_994, 1, x_993);
x_995 = lean_unsigned_to_nat(1u);
x_996 = lean_mk_array(x_995, x_994);
x_997 = l_Array_append___rarg(x_15, x_996);
lean_dec(x_996);
x_998 = l_Lake_PackageConfig_decodeToml___closed__60;
x_16 = x_998;
x_17 = x_997;
goto block_984;
}
case 3:
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
x_999 = lean_ctor_get(x_990, 0);
lean_inc(x_999);
lean_dec(x_990);
x_1000 = l_Lake_Glob_decodeToml___closed__2;
x_1001 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1001, 0, x_999);
lean_ctor_set(x_1001, 1, x_1000);
x_1002 = lean_unsigned_to_nat(1u);
x_1003 = lean_mk_array(x_1002, x_1001);
x_1004 = l_Array_append___rarg(x_15, x_1003);
lean_dec(x_1003);
x_1005 = l_Lake_PackageConfig_decodeToml___closed__60;
x_16 = x_1005;
x_17 = x_1004;
goto block_984;
}
default: 
{
uint8_t x_1006; 
x_1006 = !lean_is_exclusive(x_990);
if (x_1006 == 0)
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1007 = lean_ctor_get(x_990, 1);
lean_dec(x_1007);
x_1008 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_990, 0);
lean_ctor_set(x_990, 1, x_1008);
x_1009 = lean_unsigned_to_nat(1u);
x_1010 = lean_mk_array(x_1009, x_990);
x_1011 = l_Array_append___rarg(x_15, x_1010);
lean_dec(x_1010);
x_1012 = l_Lake_PackageConfig_decodeToml___closed__60;
x_16 = x_1012;
x_17 = x_1011;
goto block_984;
}
else
{
lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1013 = lean_ctor_get(x_990, 0);
lean_inc(x_1013);
lean_dec(x_990);
x_1014 = l_Lake_Glob_decodeToml___closed__2;
x_1015 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1015, 0, x_1013);
lean_ctor_set(x_1015, 1, x_1014);
x_1016 = lean_unsigned_to_nat(1u);
x_1017 = lean_mk_array(x_1016, x_1015);
x_1018 = l_Array_append___rarg(x_15, x_1017);
lean_dec(x_1017);
x_1019 = l_Lake_PackageConfig_decodeToml___closed__60;
x_16 = x_1019;
x_17 = x_1018;
goto block_984;
}
}
}
}
block_984:
{
lean_object* x_18; lean_object* x_19; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_949 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_950 = l_Lake_PackageConfig_decodeToml___closed__57;
lean_inc(x_1);
x_951 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_949, x_950, x_1);
if (lean_obj_tag(x_951) == 0)
{
lean_object* x_952; 
x_952 = l_Lake_defaultBuildDir;
x_18 = x_952;
x_19 = x_17;
goto block_948;
}
else
{
lean_object* x_953; lean_object* x_954; 
x_953 = lean_ctor_get(x_951, 0);
lean_inc(x_953);
lean_dec(x_951);
x_954 = lean_ctor_get(x_953, 1);
lean_inc(x_954);
lean_dec(x_953);
switch (lean_obj_tag(x_954)) {
case 0:
{
lean_object* x_955; 
x_955 = lean_ctor_get(x_954, 1);
lean_inc(x_955);
lean_dec(x_954);
x_18 = x_955;
x_19 = x_17;
goto block_948;
}
case 2:
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_956 = lean_ctor_get(x_954, 0);
lean_inc(x_956);
lean_dec(x_954);
x_957 = l_Lake_Glob_decodeToml___closed__2;
x_958 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_958, 0, x_956);
lean_ctor_set(x_958, 1, x_957);
x_959 = lean_unsigned_to_nat(1u);
x_960 = lean_mk_array(x_959, x_958);
x_961 = l_Array_append___rarg(x_17, x_960);
lean_dec(x_960);
x_962 = l_Lake_defaultBuildDir;
x_18 = x_962;
x_19 = x_961;
goto block_948;
}
case 3:
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_963 = lean_ctor_get(x_954, 0);
lean_inc(x_963);
lean_dec(x_954);
x_964 = l_Lake_Glob_decodeToml___closed__2;
x_965 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_965, 0, x_963);
lean_ctor_set(x_965, 1, x_964);
x_966 = lean_unsigned_to_nat(1u);
x_967 = lean_mk_array(x_966, x_965);
x_968 = l_Array_append___rarg(x_17, x_967);
lean_dec(x_967);
x_969 = l_Lake_defaultBuildDir;
x_18 = x_969;
x_19 = x_968;
goto block_948;
}
default: 
{
uint8_t x_970; 
x_970 = !lean_is_exclusive(x_954);
if (x_970 == 0)
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_971 = lean_ctor_get(x_954, 1);
lean_dec(x_971);
x_972 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_954, 0);
lean_ctor_set(x_954, 1, x_972);
x_973 = lean_unsigned_to_nat(1u);
x_974 = lean_mk_array(x_973, x_954);
x_975 = l_Array_append___rarg(x_17, x_974);
lean_dec(x_974);
x_976 = l_Lake_defaultBuildDir;
x_18 = x_976;
x_19 = x_975;
goto block_948;
}
else
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_977 = lean_ctor_get(x_954, 0);
lean_inc(x_977);
lean_dec(x_954);
x_978 = l_Lake_Glob_decodeToml___closed__2;
x_979 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_979, 0, x_977);
lean_ctor_set(x_979, 1, x_978);
x_980 = lean_unsigned_to_nat(1u);
x_981 = lean_mk_array(x_980, x_979);
x_982 = l_Array_append___rarg(x_17, x_981);
lean_dec(x_981);
x_983 = l_Lake_defaultBuildDir;
x_18 = x_983;
x_19 = x_982;
goto block_948;
}
}
}
}
block_948:
{
lean_object* x_20; lean_object* x_21; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_913 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_914 = l_Lake_PackageConfig_decodeToml___closed__55;
lean_inc(x_1);
x_915 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_913, x_914, x_1);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; 
x_916 = l_Lake_defaultLeanLibDir;
x_20 = x_916;
x_21 = x_19;
goto block_912;
}
else
{
lean_object* x_917; lean_object* x_918; 
x_917 = lean_ctor_get(x_915, 0);
lean_inc(x_917);
lean_dec(x_915);
x_918 = lean_ctor_get(x_917, 1);
lean_inc(x_918);
lean_dec(x_917);
switch (lean_obj_tag(x_918)) {
case 0:
{
lean_object* x_919; 
x_919 = lean_ctor_get(x_918, 1);
lean_inc(x_919);
lean_dec(x_918);
x_20 = x_919;
x_21 = x_19;
goto block_912;
}
case 2:
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_920 = lean_ctor_get(x_918, 0);
lean_inc(x_920);
lean_dec(x_918);
x_921 = l_Lake_Glob_decodeToml___closed__2;
x_922 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_922, 0, x_920);
lean_ctor_set(x_922, 1, x_921);
x_923 = lean_unsigned_to_nat(1u);
x_924 = lean_mk_array(x_923, x_922);
x_925 = l_Array_append___rarg(x_19, x_924);
lean_dec(x_924);
x_926 = l_Lake_defaultLeanLibDir;
x_20 = x_926;
x_21 = x_925;
goto block_912;
}
case 3:
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_927 = lean_ctor_get(x_918, 0);
lean_inc(x_927);
lean_dec(x_918);
x_928 = l_Lake_Glob_decodeToml___closed__2;
x_929 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_929, 0, x_927);
lean_ctor_set(x_929, 1, x_928);
x_930 = lean_unsigned_to_nat(1u);
x_931 = lean_mk_array(x_930, x_929);
x_932 = l_Array_append___rarg(x_19, x_931);
lean_dec(x_931);
x_933 = l_Lake_defaultLeanLibDir;
x_20 = x_933;
x_21 = x_932;
goto block_912;
}
default: 
{
uint8_t x_934; 
x_934 = !lean_is_exclusive(x_918);
if (x_934 == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_935 = lean_ctor_get(x_918, 1);
lean_dec(x_935);
x_936 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_918, 0);
lean_ctor_set(x_918, 1, x_936);
x_937 = lean_unsigned_to_nat(1u);
x_938 = lean_mk_array(x_937, x_918);
x_939 = l_Array_append___rarg(x_19, x_938);
lean_dec(x_938);
x_940 = l_Lake_defaultLeanLibDir;
x_20 = x_940;
x_21 = x_939;
goto block_912;
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_941 = lean_ctor_get(x_918, 0);
lean_inc(x_941);
lean_dec(x_918);
x_942 = l_Lake_Glob_decodeToml___closed__2;
x_943 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_943, 0, x_941);
lean_ctor_set(x_943, 1, x_942);
x_944 = lean_unsigned_to_nat(1u);
x_945 = lean_mk_array(x_944, x_943);
x_946 = l_Array_append___rarg(x_19, x_945);
lean_dec(x_945);
x_947 = l_Lake_defaultLeanLibDir;
x_20 = x_947;
x_21 = x_946;
goto block_912;
}
}
}
}
block_912:
{
lean_object* x_22; lean_object* x_23; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_878 = l_Lake_PackageConfig_decodeToml___closed__53;
lean_inc(x_1);
x_879 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_877, x_878, x_1);
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_880; 
x_880 = l_Lake_defaultNativeLibDir;
x_22 = x_880;
x_23 = x_21;
goto block_876;
}
else
{
lean_object* x_881; lean_object* x_882; 
x_881 = lean_ctor_get(x_879, 0);
lean_inc(x_881);
lean_dec(x_879);
x_882 = lean_ctor_get(x_881, 1);
lean_inc(x_882);
lean_dec(x_881);
switch (lean_obj_tag(x_882)) {
case 0:
{
lean_object* x_883; 
x_883 = lean_ctor_get(x_882, 1);
lean_inc(x_883);
lean_dec(x_882);
x_22 = x_883;
x_23 = x_21;
goto block_876;
}
case 2:
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; 
x_884 = lean_ctor_get(x_882, 0);
lean_inc(x_884);
lean_dec(x_882);
x_885 = l_Lake_Glob_decodeToml___closed__2;
x_886 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_886, 0, x_884);
lean_ctor_set(x_886, 1, x_885);
x_887 = lean_unsigned_to_nat(1u);
x_888 = lean_mk_array(x_887, x_886);
x_889 = l_Array_append___rarg(x_21, x_888);
lean_dec(x_888);
x_890 = l_Lake_defaultNativeLibDir;
x_22 = x_890;
x_23 = x_889;
goto block_876;
}
case 3:
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; 
x_891 = lean_ctor_get(x_882, 0);
lean_inc(x_891);
lean_dec(x_882);
x_892 = l_Lake_Glob_decodeToml___closed__2;
x_893 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_893, 0, x_891);
lean_ctor_set(x_893, 1, x_892);
x_894 = lean_unsigned_to_nat(1u);
x_895 = lean_mk_array(x_894, x_893);
x_896 = l_Array_append___rarg(x_21, x_895);
lean_dec(x_895);
x_897 = l_Lake_defaultNativeLibDir;
x_22 = x_897;
x_23 = x_896;
goto block_876;
}
default: 
{
uint8_t x_898; 
x_898 = !lean_is_exclusive(x_882);
if (x_898 == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; 
x_899 = lean_ctor_get(x_882, 1);
lean_dec(x_899);
x_900 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_882, 0);
lean_ctor_set(x_882, 1, x_900);
x_901 = lean_unsigned_to_nat(1u);
x_902 = lean_mk_array(x_901, x_882);
x_903 = l_Array_append___rarg(x_21, x_902);
lean_dec(x_902);
x_904 = l_Lake_defaultNativeLibDir;
x_22 = x_904;
x_23 = x_903;
goto block_876;
}
else
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_905 = lean_ctor_get(x_882, 0);
lean_inc(x_905);
lean_dec(x_882);
x_906 = l_Lake_Glob_decodeToml___closed__2;
x_907 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_907, 0, x_905);
lean_ctor_set(x_907, 1, x_906);
x_908 = lean_unsigned_to_nat(1u);
x_909 = lean_mk_array(x_908, x_907);
x_910 = l_Array_append___rarg(x_21, x_909);
lean_dec(x_909);
x_911 = l_Lake_defaultNativeLibDir;
x_22 = x_911;
x_23 = x_910;
goto block_876;
}
}
}
}
block_876:
{
lean_object* x_24; lean_object* x_25; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_841 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_842 = l_Lake_PackageConfig_decodeToml___closed__51;
lean_inc(x_1);
x_843 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_841, x_842, x_1);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_844; 
x_844 = l_Lake_defaultBinDir;
x_24 = x_844;
x_25 = x_23;
goto block_840;
}
else
{
lean_object* x_845; lean_object* x_846; 
x_845 = lean_ctor_get(x_843, 0);
lean_inc(x_845);
lean_dec(x_843);
x_846 = lean_ctor_get(x_845, 1);
lean_inc(x_846);
lean_dec(x_845);
switch (lean_obj_tag(x_846)) {
case 0:
{
lean_object* x_847; 
x_847 = lean_ctor_get(x_846, 1);
lean_inc(x_847);
lean_dec(x_846);
x_24 = x_847;
x_25 = x_23;
goto block_840;
}
case 2:
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
x_848 = lean_ctor_get(x_846, 0);
lean_inc(x_848);
lean_dec(x_846);
x_849 = l_Lake_Glob_decodeToml___closed__2;
x_850 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_850, 0, x_848);
lean_ctor_set(x_850, 1, x_849);
x_851 = lean_unsigned_to_nat(1u);
x_852 = lean_mk_array(x_851, x_850);
x_853 = l_Array_append___rarg(x_23, x_852);
lean_dec(x_852);
x_854 = l_Lake_defaultBinDir;
x_24 = x_854;
x_25 = x_853;
goto block_840;
}
case 3:
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; 
x_855 = lean_ctor_get(x_846, 0);
lean_inc(x_855);
lean_dec(x_846);
x_856 = l_Lake_Glob_decodeToml___closed__2;
x_857 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_857, 0, x_855);
lean_ctor_set(x_857, 1, x_856);
x_858 = lean_unsigned_to_nat(1u);
x_859 = lean_mk_array(x_858, x_857);
x_860 = l_Array_append___rarg(x_23, x_859);
lean_dec(x_859);
x_861 = l_Lake_defaultBinDir;
x_24 = x_861;
x_25 = x_860;
goto block_840;
}
default: 
{
uint8_t x_862; 
x_862 = !lean_is_exclusive(x_846);
if (x_862 == 0)
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; 
x_863 = lean_ctor_get(x_846, 1);
lean_dec(x_863);
x_864 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_846, 0);
lean_ctor_set(x_846, 1, x_864);
x_865 = lean_unsigned_to_nat(1u);
x_866 = lean_mk_array(x_865, x_846);
x_867 = l_Array_append___rarg(x_23, x_866);
lean_dec(x_866);
x_868 = l_Lake_defaultBinDir;
x_24 = x_868;
x_25 = x_867;
goto block_840;
}
else
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_869 = lean_ctor_get(x_846, 0);
lean_inc(x_869);
lean_dec(x_846);
x_870 = l_Lake_Glob_decodeToml___closed__2;
x_871 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_871, 0, x_869);
lean_ctor_set(x_871, 1, x_870);
x_872 = lean_unsigned_to_nat(1u);
x_873 = lean_mk_array(x_872, x_871);
x_874 = l_Array_append___rarg(x_23, x_873);
lean_dec(x_873);
x_875 = l_Lake_defaultBinDir;
x_24 = x_875;
x_25 = x_874;
goto block_840;
}
}
}
}
block_840:
{
lean_object* x_26; lean_object* x_27; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_805 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_806 = l_Lake_PackageConfig_decodeToml___closed__49;
lean_inc(x_1);
x_807 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_805, x_806, x_1);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; 
x_808 = l_Lake_defaultIrDir;
x_26 = x_808;
x_27 = x_25;
goto block_804;
}
else
{
lean_object* x_809; lean_object* x_810; 
x_809 = lean_ctor_get(x_807, 0);
lean_inc(x_809);
lean_dec(x_807);
x_810 = lean_ctor_get(x_809, 1);
lean_inc(x_810);
lean_dec(x_809);
switch (lean_obj_tag(x_810)) {
case 0:
{
lean_object* x_811; 
x_811 = lean_ctor_get(x_810, 1);
lean_inc(x_811);
lean_dec(x_810);
x_26 = x_811;
x_27 = x_25;
goto block_804;
}
case 2:
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_812 = lean_ctor_get(x_810, 0);
lean_inc(x_812);
lean_dec(x_810);
x_813 = l_Lake_Glob_decodeToml___closed__2;
x_814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_814, 0, x_812);
lean_ctor_set(x_814, 1, x_813);
x_815 = lean_unsigned_to_nat(1u);
x_816 = lean_mk_array(x_815, x_814);
x_817 = l_Array_append___rarg(x_25, x_816);
lean_dec(x_816);
x_818 = l_Lake_defaultIrDir;
x_26 = x_818;
x_27 = x_817;
goto block_804;
}
case 3:
{
lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_819 = lean_ctor_get(x_810, 0);
lean_inc(x_819);
lean_dec(x_810);
x_820 = l_Lake_Glob_decodeToml___closed__2;
x_821 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_821, 0, x_819);
lean_ctor_set(x_821, 1, x_820);
x_822 = lean_unsigned_to_nat(1u);
x_823 = lean_mk_array(x_822, x_821);
x_824 = l_Array_append___rarg(x_25, x_823);
lean_dec(x_823);
x_825 = l_Lake_defaultIrDir;
x_26 = x_825;
x_27 = x_824;
goto block_804;
}
default: 
{
uint8_t x_826; 
x_826 = !lean_is_exclusive(x_810);
if (x_826 == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_827 = lean_ctor_get(x_810, 1);
lean_dec(x_827);
x_828 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_810, 0);
lean_ctor_set(x_810, 1, x_828);
x_829 = lean_unsigned_to_nat(1u);
x_830 = lean_mk_array(x_829, x_810);
x_831 = l_Array_append___rarg(x_25, x_830);
lean_dec(x_830);
x_832 = l_Lake_defaultIrDir;
x_26 = x_832;
x_27 = x_831;
goto block_804;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
x_833 = lean_ctor_get(x_810, 0);
lean_inc(x_833);
lean_dec(x_810);
x_834 = l_Lake_Glob_decodeToml___closed__2;
x_835 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_835, 0, x_833);
lean_ctor_set(x_835, 1, x_834);
x_836 = lean_unsigned_to_nat(1u);
x_837 = lean_mk_array(x_836, x_835);
x_838 = l_Array_append___rarg(x_25, x_837);
lean_dec(x_837);
x_839 = l_Lake_defaultIrDir;
x_26 = x_839;
x_27 = x_838;
goto block_804;
}
}
}
}
block_804:
{
lean_object* x_28; lean_object* x_29; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_749 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_750 = l_Lake_PackageConfig_decodeToml___closed__47;
lean_inc(x_1);
x_751 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_749, x_750, x_1);
x_752 = lean_box(0);
if (lean_obj_tag(x_751) == 0)
{
x_28 = x_752;
x_29 = x_27;
goto block_748;
}
else
{
uint8_t x_753; 
x_753 = !lean_is_exclusive(x_751);
if (x_753 == 0)
{
lean_object* x_754; lean_object* x_755; 
x_754 = lean_ctor_get(x_751, 0);
x_755 = lean_ctor_get(x_754, 1);
lean_inc(x_755);
lean_dec(x_754);
switch (lean_obj_tag(x_755)) {
case 0:
{
lean_object* x_756; 
x_756 = lean_ctor_get(x_755, 1);
lean_inc(x_756);
lean_dec(x_755);
lean_ctor_set(x_751, 0, x_756);
x_28 = x_751;
x_29 = x_27;
goto block_748;
}
case 2:
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_free_object(x_751);
x_757 = lean_ctor_get(x_755, 0);
lean_inc(x_757);
lean_dec(x_755);
x_758 = l_Lake_Glob_decodeToml___closed__2;
x_759 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_759, 0, x_757);
lean_ctor_set(x_759, 1, x_758);
x_760 = lean_unsigned_to_nat(1u);
x_761 = lean_mk_array(x_760, x_759);
x_762 = l_Array_append___rarg(x_27, x_761);
lean_dec(x_761);
x_28 = x_752;
x_29 = x_762;
goto block_748;
}
case 3:
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_free_object(x_751);
x_763 = lean_ctor_get(x_755, 0);
lean_inc(x_763);
lean_dec(x_755);
x_764 = l_Lake_Glob_decodeToml___closed__2;
x_765 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_765, 0, x_763);
lean_ctor_set(x_765, 1, x_764);
x_766 = lean_unsigned_to_nat(1u);
x_767 = lean_mk_array(x_766, x_765);
x_768 = l_Array_append___rarg(x_27, x_767);
lean_dec(x_767);
x_28 = x_752;
x_29 = x_768;
goto block_748;
}
default: 
{
uint8_t x_769; 
lean_free_object(x_751);
x_769 = !lean_is_exclusive(x_755);
if (x_769 == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_770 = lean_ctor_get(x_755, 1);
lean_dec(x_770);
x_771 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_755, 0);
lean_ctor_set(x_755, 1, x_771);
x_772 = lean_unsigned_to_nat(1u);
x_773 = lean_mk_array(x_772, x_755);
x_774 = l_Array_append___rarg(x_27, x_773);
lean_dec(x_773);
x_28 = x_752;
x_29 = x_774;
goto block_748;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_775 = lean_ctor_get(x_755, 0);
lean_inc(x_775);
lean_dec(x_755);
x_776 = l_Lake_Glob_decodeToml___closed__2;
x_777 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_777, 0, x_775);
lean_ctor_set(x_777, 1, x_776);
x_778 = lean_unsigned_to_nat(1u);
x_779 = lean_mk_array(x_778, x_777);
x_780 = l_Array_append___rarg(x_27, x_779);
lean_dec(x_779);
x_28 = x_752;
x_29 = x_780;
goto block_748;
}
}
}
}
else
{
lean_object* x_781; lean_object* x_782; 
x_781 = lean_ctor_get(x_751, 0);
lean_inc(x_781);
lean_dec(x_751);
x_782 = lean_ctor_get(x_781, 1);
lean_inc(x_782);
lean_dec(x_781);
switch (lean_obj_tag(x_782)) {
case 0:
{
lean_object* x_783; lean_object* x_784; 
x_783 = lean_ctor_get(x_782, 1);
lean_inc(x_783);
lean_dec(x_782);
x_784 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_784, 0, x_783);
x_28 = x_784;
x_29 = x_27;
goto block_748;
}
case 2:
{
lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_785 = lean_ctor_get(x_782, 0);
lean_inc(x_785);
lean_dec(x_782);
x_786 = l_Lake_Glob_decodeToml___closed__2;
x_787 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_787, 0, x_785);
lean_ctor_set(x_787, 1, x_786);
x_788 = lean_unsigned_to_nat(1u);
x_789 = lean_mk_array(x_788, x_787);
x_790 = l_Array_append___rarg(x_27, x_789);
lean_dec(x_789);
x_28 = x_752;
x_29 = x_790;
goto block_748;
}
case 3:
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_791 = lean_ctor_get(x_782, 0);
lean_inc(x_791);
lean_dec(x_782);
x_792 = l_Lake_Glob_decodeToml___closed__2;
x_793 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
x_794 = lean_unsigned_to_nat(1u);
x_795 = lean_mk_array(x_794, x_793);
x_796 = l_Array_append___rarg(x_27, x_795);
lean_dec(x_795);
x_28 = x_752;
x_29 = x_796;
goto block_748;
}
default: 
{
lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_797 = lean_ctor_get(x_782, 0);
lean_inc(x_797);
if (lean_is_exclusive(x_782)) {
 lean_ctor_release(x_782, 0);
 lean_ctor_release(x_782, 1);
 x_798 = x_782;
} else {
 lean_dec_ref(x_782);
 x_798 = lean_box(0);
}
x_799 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_798)) {
 x_800 = lean_alloc_ctor(0, 2, 0);
} else {
 x_800 = x_798;
 lean_ctor_set_tag(x_800, 0);
}
lean_ctor_set(x_800, 0, x_797);
lean_ctor_set(x_800, 1, x_799);
x_801 = lean_unsigned_to_nat(1u);
x_802 = lean_mk_array(x_801, x_800);
x_803 = l_Array_append___rarg(x_27, x_802);
lean_dec(x_802);
x_28 = x_752;
x_29 = x_803;
goto block_748;
}
}
}
}
block_748:
{
lean_object* x_30; lean_object* x_31; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; 
x_693 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_694 = l_Lake_PackageConfig_decodeToml___closed__45;
lean_inc(x_1);
x_695 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_693, x_694, x_1);
x_696 = lean_box(0);
if (lean_obj_tag(x_695) == 0)
{
x_30 = x_696;
x_31 = x_29;
goto block_692;
}
else
{
uint8_t x_697; 
x_697 = !lean_is_exclusive(x_695);
if (x_697 == 0)
{
lean_object* x_698; lean_object* x_699; 
x_698 = lean_ctor_get(x_695, 0);
x_699 = lean_ctor_get(x_698, 1);
lean_inc(x_699);
lean_dec(x_698);
switch (lean_obj_tag(x_699)) {
case 0:
{
lean_object* x_700; 
x_700 = lean_ctor_get(x_699, 1);
lean_inc(x_700);
lean_dec(x_699);
lean_ctor_set(x_695, 0, x_700);
x_30 = x_695;
x_31 = x_29;
goto block_692;
}
case 2:
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_free_object(x_695);
x_701 = lean_ctor_get(x_699, 0);
lean_inc(x_701);
lean_dec(x_699);
x_702 = l_Lake_Glob_decodeToml___closed__2;
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set(x_703, 1, x_702);
x_704 = lean_unsigned_to_nat(1u);
x_705 = lean_mk_array(x_704, x_703);
x_706 = l_Array_append___rarg(x_29, x_705);
lean_dec(x_705);
x_30 = x_696;
x_31 = x_706;
goto block_692;
}
case 3:
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_free_object(x_695);
x_707 = lean_ctor_get(x_699, 0);
lean_inc(x_707);
lean_dec(x_699);
x_708 = l_Lake_Glob_decodeToml___closed__2;
x_709 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_709, 0, x_707);
lean_ctor_set(x_709, 1, x_708);
x_710 = lean_unsigned_to_nat(1u);
x_711 = lean_mk_array(x_710, x_709);
x_712 = l_Array_append___rarg(x_29, x_711);
lean_dec(x_711);
x_30 = x_696;
x_31 = x_712;
goto block_692;
}
default: 
{
uint8_t x_713; 
lean_free_object(x_695);
x_713 = !lean_is_exclusive(x_699);
if (x_713 == 0)
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_714 = lean_ctor_get(x_699, 1);
lean_dec(x_714);
x_715 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_699, 0);
lean_ctor_set(x_699, 1, x_715);
x_716 = lean_unsigned_to_nat(1u);
x_717 = lean_mk_array(x_716, x_699);
x_718 = l_Array_append___rarg(x_29, x_717);
lean_dec(x_717);
x_30 = x_696;
x_31 = x_718;
goto block_692;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_719 = lean_ctor_get(x_699, 0);
lean_inc(x_719);
lean_dec(x_699);
x_720 = l_Lake_Glob_decodeToml___closed__2;
x_721 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_721, 0, x_719);
lean_ctor_set(x_721, 1, x_720);
x_722 = lean_unsigned_to_nat(1u);
x_723 = lean_mk_array(x_722, x_721);
x_724 = l_Array_append___rarg(x_29, x_723);
lean_dec(x_723);
x_30 = x_696;
x_31 = x_724;
goto block_692;
}
}
}
}
else
{
lean_object* x_725; lean_object* x_726; 
x_725 = lean_ctor_get(x_695, 0);
lean_inc(x_725);
lean_dec(x_695);
x_726 = lean_ctor_get(x_725, 1);
lean_inc(x_726);
lean_dec(x_725);
switch (lean_obj_tag(x_726)) {
case 0:
{
lean_object* x_727; lean_object* x_728; 
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
lean_dec(x_726);
x_728 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_728, 0, x_727);
x_30 = x_728;
x_31 = x_29;
goto block_692;
}
case 2:
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_729 = lean_ctor_get(x_726, 0);
lean_inc(x_729);
lean_dec(x_726);
x_730 = l_Lake_Glob_decodeToml___closed__2;
x_731 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
x_732 = lean_unsigned_to_nat(1u);
x_733 = lean_mk_array(x_732, x_731);
x_734 = l_Array_append___rarg(x_29, x_733);
lean_dec(x_733);
x_30 = x_696;
x_31 = x_734;
goto block_692;
}
case 3:
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_735 = lean_ctor_get(x_726, 0);
lean_inc(x_735);
lean_dec(x_726);
x_736 = l_Lake_Glob_decodeToml___closed__2;
x_737 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_737, 0, x_735);
lean_ctor_set(x_737, 1, x_736);
x_738 = lean_unsigned_to_nat(1u);
x_739 = lean_mk_array(x_738, x_737);
x_740 = l_Array_append___rarg(x_29, x_739);
lean_dec(x_739);
x_30 = x_696;
x_31 = x_740;
goto block_692;
}
default: 
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; 
x_741 = lean_ctor_get(x_726, 0);
lean_inc(x_741);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_742 = x_726;
} else {
 lean_dec_ref(x_726);
 x_742 = lean_box(0);
}
x_743 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_742)) {
 x_744 = lean_alloc_ctor(0, 2, 0);
} else {
 x_744 = x_742;
 lean_ctor_set_tag(x_744, 0);
}
lean_ctor_set(x_744, 0, x_741);
lean_ctor_set(x_744, 1, x_743);
x_745 = lean_unsigned_to_nat(1u);
x_746 = lean_mk_array(x_745, x_744);
x_747 = l_Array_append___rarg(x_29, x_746);
lean_dec(x_746);
x_30 = x_696;
x_31 = x_747;
goto block_692;
}
}
}
}
block_692:
{
uint8_t x_32; lean_object* x_33; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_651 = l_Lake_PackageConfig_decodeToml___closed__43;
lean_inc(x_1);
x_652 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_650, x_651, x_1);
if (lean_obj_tag(x_652) == 0)
{
uint8_t x_653; 
x_653 = 0;
x_32 = x_653;
x_33 = x_31;
goto block_649;
}
else
{
lean_object* x_654; lean_object* x_655; 
x_654 = lean_ctor_get(x_652, 0);
lean_inc(x_654);
lean_dec(x_652);
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
lean_dec(x_654);
switch (lean_obj_tag(x_655)) {
case 0:
{
uint8_t x_656; 
x_656 = !lean_is_exclusive(x_655);
if (x_656 == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; uint8_t x_662; 
x_657 = lean_ctor_get(x_655, 1);
lean_dec(x_657);
x_658 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_655, 1, x_658);
x_659 = lean_unsigned_to_nat(1u);
x_660 = lean_mk_array(x_659, x_655);
x_661 = l_Array_append___rarg(x_31, x_660);
lean_dec(x_660);
x_662 = 0;
x_32 = x_662;
x_33 = x_661;
goto block_649;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; 
x_663 = lean_ctor_get(x_655, 0);
lean_inc(x_663);
lean_dec(x_655);
x_664 = l_Lake_LeanConfig_decodeToml___closed__20;
x_665 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
x_666 = lean_unsigned_to_nat(1u);
x_667 = lean_mk_array(x_666, x_665);
x_668 = l_Array_append___rarg(x_31, x_667);
lean_dec(x_667);
x_669 = 0;
x_32 = x_669;
x_33 = x_668;
goto block_649;
}
}
case 2:
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; uint8_t x_676; 
x_670 = lean_ctor_get(x_655, 0);
lean_inc(x_670);
lean_dec(x_655);
x_671 = l_Lake_LeanConfig_decodeToml___closed__20;
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
x_673 = lean_unsigned_to_nat(1u);
x_674 = lean_mk_array(x_673, x_672);
x_675 = l_Array_append___rarg(x_31, x_674);
lean_dec(x_674);
x_676 = 0;
x_32 = x_676;
x_33 = x_675;
goto block_649;
}
case 3:
{
uint8_t x_677; 
x_677 = lean_ctor_get_uint8(x_655, sizeof(void*)*1);
lean_dec(x_655);
x_32 = x_677;
x_33 = x_31;
goto block_649;
}
default: 
{
uint8_t x_678; 
x_678 = !lean_is_exclusive(x_655);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; uint8_t x_684; 
x_679 = lean_ctor_get(x_655, 1);
lean_dec(x_679);
x_680 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_655, 0);
lean_ctor_set(x_655, 1, x_680);
x_681 = lean_unsigned_to_nat(1u);
x_682 = lean_mk_array(x_681, x_655);
x_683 = l_Array_append___rarg(x_31, x_682);
lean_dec(x_682);
x_684 = 0;
x_32 = x_684;
x_33 = x_683;
goto block_649;
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; uint8_t x_691; 
x_685 = lean_ctor_get(x_655, 0);
lean_inc(x_685);
lean_dec(x_655);
x_686 = l_Lake_LeanConfig_decodeToml___closed__20;
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
x_688 = lean_unsigned_to_nat(1u);
x_689 = lean_mk_array(x_688, x_687);
x_690 = l_Array_append___rarg(x_31, x_689);
lean_dec(x_689);
x_691 = 0;
x_32 = x_691;
x_33 = x_690;
goto block_649;
}
}
}
}
block_649:
{
lean_object* x_34; lean_object* x_35; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_615 = l_Lake_PackageConfig_decodeToml___closed__41;
lean_inc(x_1);
x_616 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_614, x_615, x_1);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; 
x_617 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_617;
x_35 = x_33;
goto block_613;
}
else
{
lean_object* x_618; lean_object* x_619; 
x_618 = lean_ctor_get(x_616, 0);
lean_inc(x_618);
lean_dec(x_616);
x_619 = lean_ctor_get(x_618, 1);
lean_inc(x_619);
lean_dec(x_618);
switch (lean_obj_tag(x_619)) {
case 0:
{
lean_object* x_620; 
x_620 = lean_ctor_get(x_619, 1);
lean_inc(x_620);
lean_dec(x_619);
x_34 = x_620;
x_35 = x_33;
goto block_613;
}
case 2:
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
x_621 = lean_ctor_get(x_619, 0);
lean_inc(x_621);
lean_dec(x_619);
x_622 = l_Lake_Glob_decodeToml___closed__2;
x_623 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_623, 0, x_621);
lean_ctor_set(x_623, 1, x_622);
x_624 = lean_unsigned_to_nat(1u);
x_625 = lean_mk_array(x_624, x_623);
x_626 = l_Array_append___rarg(x_33, x_625);
lean_dec(x_625);
x_627 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_627;
x_35 = x_626;
goto block_613;
}
case 3:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_628 = lean_ctor_get(x_619, 0);
lean_inc(x_628);
lean_dec(x_619);
x_629 = l_Lake_Glob_decodeToml___closed__2;
x_630 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
x_631 = lean_unsigned_to_nat(1u);
x_632 = lean_mk_array(x_631, x_630);
x_633 = l_Array_append___rarg(x_33, x_632);
lean_dec(x_632);
x_634 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_634;
x_35 = x_633;
goto block_613;
}
default: 
{
uint8_t x_635; 
x_635 = !lean_is_exclusive(x_619);
if (x_635 == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_636 = lean_ctor_get(x_619, 1);
lean_dec(x_636);
x_637 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_619, 0);
lean_ctor_set(x_619, 1, x_637);
x_638 = lean_unsigned_to_nat(1u);
x_639 = lean_mk_array(x_638, x_619);
x_640 = l_Array_append___rarg(x_33, x_639);
lean_dec(x_639);
x_641 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_641;
x_35 = x_640;
goto block_613;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_642 = lean_ctor_get(x_619, 0);
lean_inc(x_642);
lean_dec(x_619);
x_643 = l_Lake_Glob_decodeToml___closed__2;
x_644 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_644, 0, x_642);
lean_ctor_set(x_644, 1, x_643);
x_645 = lean_unsigned_to_nat(1u);
x_646 = lean_mk_array(x_645, x_644);
x_647 = l_Array_append___rarg(x_33, x_646);
lean_dec(x_646);
x_648 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_648;
x_35 = x_647;
goto block_613;
}
}
}
}
block_613:
{
lean_object* x_36; lean_object* x_37; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_579 = l_Lake_PackageConfig_decodeToml___closed__39;
lean_inc(x_1);
x_580 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_578, x_579, x_1);
if (lean_obj_tag(x_580) == 0)
{
lean_object* x_581; 
x_581 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_581;
x_37 = x_35;
goto block_577;
}
else
{
lean_object* x_582; lean_object* x_583; 
x_582 = lean_ctor_get(x_580, 0);
lean_inc(x_582);
lean_dec(x_580);
x_583 = lean_ctor_get(x_582, 1);
lean_inc(x_583);
lean_dec(x_582);
switch (lean_obj_tag(x_583)) {
case 0:
{
lean_object* x_584; 
x_584 = lean_ctor_get(x_583, 1);
lean_inc(x_584);
lean_dec(x_583);
x_36 = x_584;
x_37 = x_35;
goto block_577;
}
case 2:
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_585 = lean_ctor_get(x_583, 0);
lean_inc(x_585);
lean_dec(x_583);
x_586 = l_Lake_Glob_decodeToml___closed__2;
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_585);
lean_ctor_set(x_587, 1, x_586);
x_588 = lean_unsigned_to_nat(1u);
x_589 = lean_mk_array(x_588, x_587);
x_590 = l_Array_append___rarg(x_35, x_589);
lean_dec(x_589);
x_591 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_591;
x_37 = x_590;
goto block_577;
}
case 3:
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_592 = lean_ctor_get(x_583, 0);
lean_inc(x_592);
lean_dec(x_583);
x_593 = l_Lake_Glob_decodeToml___closed__2;
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_592);
lean_ctor_set(x_594, 1, x_593);
x_595 = lean_unsigned_to_nat(1u);
x_596 = lean_mk_array(x_595, x_594);
x_597 = l_Array_append___rarg(x_35, x_596);
lean_dec(x_596);
x_598 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_598;
x_37 = x_597;
goto block_577;
}
default: 
{
uint8_t x_599; 
x_599 = !lean_is_exclusive(x_583);
if (x_599 == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_600 = lean_ctor_get(x_583, 1);
lean_dec(x_600);
x_601 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_583, 0);
lean_ctor_set(x_583, 1, x_601);
x_602 = lean_unsigned_to_nat(1u);
x_603 = lean_mk_array(x_602, x_583);
x_604 = l_Array_append___rarg(x_35, x_603);
lean_dec(x_603);
x_605 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_605;
x_37 = x_604;
goto block_577;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_606 = lean_ctor_get(x_583, 0);
lean_inc(x_606);
lean_dec(x_583);
x_607 = l_Lake_Glob_decodeToml___closed__2;
x_608 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_608, 0, x_606);
lean_ctor_set(x_608, 1, x_607);
x_609 = lean_unsigned_to_nat(1u);
x_610 = lean_mk_array(x_609, x_608);
x_611 = l_Array_append___rarg(x_35, x_610);
lean_dec(x_610);
x_612 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_36 = x_612;
x_37 = x_611;
goto block_577;
}
}
}
}
block_577:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_38 = lean_string_utf8_byte_size(x_34);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_eq(x_38, x_39);
lean_dec(x_38);
x_41 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_42 = l_Lake_PackageConfig_decodeToml___closed__4;
lean_inc(x_1);
x_43 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_42, x_1);
if (x_40 == 0)
{
uint8_t x_571; 
x_571 = l_Lake_PackageConfig_decodeToml___closed__36;
if (x_571 == 0)
{
lean_dec(x_34);
x_44 = x_36;
goto block_570;
}
else
{
lean_object* x_572; uint8_t x_573; 
x_572 = lean_string_utf8_byte_size(x_36);
x_573 = lean_nat_dec_eq(x_572, x_39);
lean_dec(x_572);
if (x_573 == 0)
{
lean_dec(x_34);
x_44 = x_36;
goto block_570;
}
else
{
lean_dec(x_36);
x_44 = x_34;
goto block_570;
}
}
}
else
{
uint8_t x_574; 
x_574 = l_Lake_PackageConfig_decodeToml___closed__37;
if (x_574 == 0)
{
lean_dec(x_34);
x_44 = x_36;
goto block_570;
}
else
{
lean_object* x_575; uint8_t x_576; 
x_575 = lean_string_utf8_byte_size(x_36);
x_576 = lean_nat_dec_eq(x_575, x_39);
lean_dec(x_575);
if (x_576 == 0)
{
lean_dec(x_34);
x_44 = x_36;
goto block_570;
}
else
{
lean_dec(x_36);
x_44 = x_34;
goto block_570;
}
}
}
block_570:
{
lean_object* x_45; lean_object* x_46; 
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_519; 
x_519 = l_Lake_decodeLeanOptions___closed__1;
x_45 = x_519;
x_46 = x_37;
goto block_518;
}
else
{
lean_object* x_520; lean_object* x_521; 
x_520 = lean_ctor_get(x_43, 0);
lean_inc(x_520);
lean_dec(x_43);
x_521 = lean_ctor_get(x_520, 1);
lean_inc(x_521);
lean_dec(x_520);
switch (lean_obj_tag(x_521)) {
case 0:
{
uint8_t x_522; 
x_522 = !lean_is_exclusive(x_521);
if (x_522 == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_523 = lean_ctor_get(x_521, 1);
lean_dec(x_523);
x_524 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_521, 1, x_524);
x_525 = lean_unsigned_to_nat(1u);
x_526 = lean_mk_array(x_525, x_521);
x_527 = l_Array_append___rarg(x_37, x_526);
lean_dec(x_526);
x_528 = l_Lake_decodeLeanOptions___closed__1;
x_45 = x_528;
x_46 = x_527;
goto block_518;
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_529 = lean_ctor_get(x_521, 0);
lean_inc(x_529);
lean_dec(x_521);
x_530 = l_Lake_LeanConfig_decodeToml___closed__5;
x_531 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
x_532 = lean_unsigned_to_nat(1u);
x_533 = lean_mk_array(x_532, x_531);
x_534 = l_Array_append___rarg(x_37, x_533);
lean_dec(x_533);
x_535 = l_Lake_decodeLeanOptions___closed__1;
x_45 = x_535;
x_46 = x_534;
goto block_518;
}
}
case 2:
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_536 = lean_ctor_get(x_521, 0);
lean_inc(x_536);
lean_dec(x_521);
x_537 = l_Lake_LeanConfig_decodeToml___closed__5;
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
x_539 = lean_unsigned_to_nat(1u);
x_540 = lean_mk_array(x_539, x_538);
x_541 = l_Array_append___rarg(x_37, x_540);
lean_dec(x_540);
x_542 = l_Lake_decodeLeanOptions___closed__1;
x_45 = x_542;
x_46 = x_541;
goto block_518;
}
case 3:
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_543 = lean_ctor_get(x_521, 0);
lean_inc(x_543);
lean_dec(x_521);
x_544 = l_Lake_LeanConfig_decodeToml___closed__5;
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
x_546 = lean_unsigned_to_nat(1u);
x_547 = lean_mk_array(x_546, x_545);
x_548 = l_Array_append___rarg(x_37, x_547);
lean_dec(x_547);
x_549 = l_Lake_decodeLeanOptions___closed__1;
x_45 = x_549;
x_46 = x_548;
goto block_518;
}
case 5:
{
lean_object* x_550; lean_object* x_551; 
x_550 = lean_ctor_get(x_521, 1);
lean_inc(x_550);
lean_dec(x_521);
x_551 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_550);
lean_dec(x_550);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
lean_dec(x_551);
x_553 = l_Array_append___rarg(x_37, x_552);
lean_dec(x_552);
x_554 = l_Lake_decodeLeanOptions___closed__1;
x_45 = x_554;
x_46 = x_553;
goto block_518;
}
else
{
lean_object* x_555; 
x_555 = lean_ctor_get(x_551, 0);
lean_inc(x_555);
lean_dec(x_551);
x_45 = x_555;
x_46 = x_37;
goto block_518;
}
}
default: 
{
uint8_t x_556; 
x_556 = !lean_is_exclusive(x_521);
if (x_556 == 0)
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_557 = lean_ctor_get(x_521, 1);
lean_dec(x_557);
x_558 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_521, 0);
lean_ctor_set(x_521, 1, x_558);
x_559 = lean_unsigned_to_nat(1u);
x_560 = lean_mk_array(x_559, x_521);
x_561 = l_Array_append___rarg(x_37, x_560);
lean_dec(x_560);
x_562 = l_Lake_decodeLeanOptions___closed__1;
x_45 = x_562;
x_46 = x_561;
goto block_518;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_563 = lean_ctor_get(x_521, 0);
lean_inc(x_563);
lean_dec(x_521);
x_564 = l_Lake_LeanConfig_decodeToml___closed__5;
x_565 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
x_566 = lean_unsigned_to_nat(1u);
x_567 = lean_mk_array(x_566, x_565);
x_568 = l_Array_append___rarg(x_37, x_567);
lean_dec(x_567);
x_569 = l_Lake_decodeLeanOptions___closed__1;
x_45 = x_569;
x_46 = x_568;
goto block_518;
}
}
}
}
block_518:
{
lean_object* x_47; lean_object* x_48; lean_object* x_484; lean_object* x_485; 
x_484 = l_Lake_PackageConfig_decodeToml___closed__35;
lean_inc(x_1);
x_485 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_484, x_1);
if (lean_obj_tag(x_485) == 0)
{
lean_object* x_486; 
x_486 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_47 = x_486;
x_48 = x_46;
goto block_483;
}
else
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_485, 0);
lean_inc(x_487);
lean_dec(x_485);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
lean_dec(x_487);
switch (lean_obj_tag(x_488)) {
case 0:
{
lean_object* x_489; 
x_489 = lean_ctor_get(x_488, 1);
lean_inc(x_489);
lean_dec(x_488);
x_47 = x_489;
x_48 = x_46;
goto block_483;
}
case 2:
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_490 = lean_ctor_get(x_488, 0);
lean_inc(x_490);
lean_dec(x_488);
x_491 = l_Lake_Glob_decodeToml___closed__2;
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_unsigned_to_nat(1u);
x_494 = lean_mk_array(x_493, x_492);
x_495 = l_Array_append___rarg(x_46, x_494);
lean_dec(x_494);
x_496 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_47 = x_496;
x_48 = x_495;
goto block_483;
}
case 3:
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_497 = lean_ctor_get(x_488, 0);
lean_inc(x_497);
lean_dec(x_488);
x_498 = l_Lake_Glob_decodeToml___closed__2;
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_497);
lean_ctor_set(x_499, 1, x_498);
x_500 = lean_unsigned_to_nat(1u);
x_501 = lean_mk_array(x_500, x_499);
x_502 = l_Array_append___rarg(x_46, x_501);
lean_dec(x_501);
x_503 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_47 = x_503;
x_48 = x_502;
goto block_483;
}
default: 
{
uint8_t x_504; 
x_504 = !lean_is_exclusive(x_488);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_505 = lean_ctor_get(x_488, 1);
lean_dec(x_505);
x_506 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_488, 0);
lean_ctor_set(x_488, 1, x_506);
x_507 = lean_unsigned_to_nat(1u);
x_508 = lean_mk_array(x_507, x_488);
x_509 = l_Array_append___rarg(x_46, x_508);
lean_dec(x_508);
x_510 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_47 = x_510;
x_48 = x_509;
goto block_483;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_511 = lean_ctor_get(x_488, 0);
lean_inc(x_511);
lean_dec(x_488);
x_512 = l_Lake_Glob_decodeToml___closed__2;
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
x_514 = lean_unsigned_to_nat(1u);
x_515 = lean_mk_array(x_514, x_513);
x_516 = l_Array_append___rarg(x_46, x_515);
lean_dec(x_515);
x_517 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_47 = x_517;
x_48 = x_516;
goto block_483;
}
}
}
}
block_483:
{
lean_object* x_49; lean_object* x_50; lean_object* x_430; lean_object* x_431; 
x_430 = l_Lake_PackageConfig_decodeToml___closed__33;
lean_inc(x_1);
x_431 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_430, x_1);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; 
x_432 = l_Lake_decodeLeanOptions___closed__1;
x_49 = x_432;
x_50 = x_48;
goto block_429;
}
else
{
lean_object* x_433; lean_object* x_434; 
x_433 = lean_ctor_get(x_431, 0);
lean_inc(x_433);
lean_dec(x_431);
x_434 = lean_ctor_get(x_433, 1);
lean_inc(x_434);
lean_dec(x_433);
switch (lean_obj_tag(x_434)) {
case 0:
{
uint8_t x_435; 
x_435 = !lean_is_exclusive(x_434);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_436 = lean_ctor_get(x_434, 1);
lean_dec(x_436);
x_437 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_434, 1, x_437);
x_438 = lean_unsigned_to_nat(1u);
x_439 = lean_mk_array(x_438, x_434);
x_440 = l_Array_append___rarg(x_48, x_439);
lean_dec(x_439);
x_441 = l_Lake_decodeLeanOptions___closed__1;
x_49 = x_441;
x_50 = x_440;
goto block_429;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_442 = lean_ctor_get(x_434, 0);
lean_inc(x_442);
lean_dec(x_434);
x_443 = l_Lake_LeanConfig_decodeToml___closed__5;
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_unsigned_to_nat(1u);
x_446 = lean_mk_array(x_445, x_444);
x_447 = l_Array_append___rarg(x_48, x_446);
lean_dec(x_446);
x_448 = l_Lake_decodeLeanOptions___closed__1;
x_49 = x_448;
x_50 = x_447;
goto block_429;
}
}
case 2:
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_449 = lean_ctor_get(x_434, 0);
lean_inc(x_449);
lean_dec(x_434);
x_450 = l_Lake_LeanConfig_decodeToml___closed__5;
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_unsigned_to_nat(1u);
x_453 = lean_mk_array(x_452, x_451);
x_454 = l_Array_append___rarg(x_48, x_453);
lean_dec(x_453);
x_455 = l_Lake_decodeLeanOptions___closed__1;
x_49 = x_455;
x_50 = x_454;
goto block_429;
}
case 3:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_456 = lean_ctor_get(x_434, 0);
lean_inc(x_456);
lean_dec(x_434);
x_457 = l_Lake_LeanConfig_decodeToml___closed__5;
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_unsigned_to_nat(1u);
x_460 = lean_mk_array(x_459, x_458);
x_461 = l_Array_append___rarg(x_48, x_460);
lean_dec(x_460);
x_462 = l_Lake_decodeLeanOptions___closed__1;
x_49 = x_462;
x_50 = x_461;
goto block_429;
}
case 5:
{
lean_object* x_463; lean_object* x_464; 
x_463 = lean_ctor_get(x_434, 1);
lean_inc(x_463);
lean_dec(x_434);
x_464 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_463);
lean_dec(x_463);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
lean_dec(x_464);
x_466 = l_Array_append___rarg(x_48, x_465);
lean_dec(x_465);
x_467 = l_Lake_decodeLeanOptions___closed__1;
x_49 = x_467;
x_50 = x_466;
goto block_429;
}
else
{
lean_object* x_468; 
x_468 = lean_ctor_get(x_464, 0);
lean_inc(x_468);
lean_dec(x_464);
x_49 = x_468;
x_50 = x_48;
goto block_429;
}
}
default: 
{
uint8_t x_469; 
x_469 = !lean_is_exclusive(x_434);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_470 = lean_ctor_get(x_434, 1);
lean_dec(x_470);
x_471 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_434, 0);
lean_ctor_set(x_434, 1, x_471);
x_472 = lean_unsigned_to_nat(1u);
x_473 = lean_mk_array(x_472, x_434);
x_474 = l_Array_append___rarg(x_48, x_473);
lean_dec(x_473);
x_475 = l_Lake_decodeLeanOptions___closed__1;
x_49 = x_475;
x_50 = x_474;
goto block_429;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_476 = lean_ctor_get(x_434, 0);
lean_inc(x_476);
lean_dec(x_434);
x_477 = l_Lake_LeanConfig_decodeToml___closed__5;
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
x_479 = lean_unsigned_to_nat(1u);
x_480 = lean_mk_array(x_479, x_478);
x_481 = l_Array_append___rarg(x_48, x_480);
lean_dec(x_480);
x_482 = l_Lake_decodeLeanOptions___closed__1;
x_49 = x_482;
x_50 = x_481;
goto block_429;
}
}
}
}
block_429:
{
lean_object* x_51; lean_object* x_52; lean_object* x_419; lean_object* x_420; 
x_419 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_420 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_419, x_1);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; 
x_421 = l_Lake_PackageConfig_decodeToml___closed__31;
x_51 = x_421;
x_52 = x_50;
goto block_418;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_420, 0);
lean_inc(x_422);
lean_dec(x_420);
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
lean_dec(x_422);
x_424 = l_Lake_StdVer_decodeToml(x_423);
if (lean_obj_tag(x_424) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
lean_dec(x_424);
x_426 = l_Array_append___rarg(x_50, x_425);
lean_dec(x_425);
x_427 = l_Lake_PackageConfig_decodeToml___closed__31;
x_51 = x_427;
x_52 = x_426;
goto block_418;
}
else
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_424, 0);
lean_inc(x_428);
lean_dec(x_424);
x_51 = x_428;
x_52 = x_50;
goto block_418;
}
}
block_418:
{
lean_object* x_53; lean_object* x_54; lean_object* x_407; lean_object* x_408; 
x_407 = l_Lake_PackageConfig_decodeToml___closed__27;
lean_inc(x_1);
x_408 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_407, x_1);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; 
x_409 = l_Lake_defaultVersionTags;
x_53 = x_409;
x_54 = x_52;
goto block_406;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_410 = lean_ctor_get(x_408, 0);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
x_412 = l_Lake_versionTagPresets;
x_413 = l_Lake_StrPat_decodeToml(x_411, x_412);
if (lean_obj_tag(x_413) == 0)
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
lean_dec(x_413);
x_415 = l_Array_append___rarg(x_52, x_414);
lean_dec(x_414);
x_416 = l_Lake_defaultVersionTags;
x_53 = x_416;
x_54 = x_415;
goto block_406;
}
else
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_413, 0);
lean_inc(x_417);
lean_dec(x_413);
x_53 = x_417;
x_54 = x_52;
goto block_406;
}
}
block_406:
{
lean_object* x_55; lean_object* x_56; lean_object* x_372; lean_object* x_373; 
x_372 = l_Lake_PackageConfig_decodeToml___closed__25;
lean_inc(x_1);
x_373 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_372, x_1);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; 
x_374 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_55 = x_374;
x_56 = x_54;
goto block_371;
}
else
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_373, 0);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
switch (lean_obj_tag(x_376)) {
case 0:
{
lean_object* x_377; 
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec(x_376);
x_55 = x_377;
x_56 = x_54;
goto block_371;
}
case 2:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_378 = lean_ctor_get(x_376, 0);
lean_inc(x_378);
lean_dec(x_376);
x_379 = l_Lake_Glob_decodeToml___closed__2;
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_mk_array(x_381, x_380);
x_383 = l_Array_append___rarg(x_54, x_382);
lean_dec(x_382);
x_384 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_55 = x_384;
x_56 = x_383;
goto block_371;
}
case 3:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_385 = lean_ctor_get(x_376, 0);
lean_inc(x_385);
lean_dec(x_376);
x_386 = l_Lake_Glob_decodeToml___closed__2;
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_388 = lean_unsigned_to_nat(1u);
x_389 = lean_mk_array(x_388, x_387);
x_390 = l_Array_append___rarg(x_54, x_389);
lean_dec(x_389);
x_391 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_55 = x_391;
x_56 = x_390;
goto block_371;
}
default: 
{
uint8_t x_392; 
x_392 = !lean_is_exclusive(x_376);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_393 = lean_ctor_get(x_376, 1);
lean_dec(x_393);
x_394 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_376, 0);
lean_ctor_set(x_376, 1, x_394);
x_395 = lean_unsigned_to_nat(1u);
x_396 = lean_mk_array(x_395, x_376);
x_397 = l_Array_append___rarg(x_54, x_396);
lean_dec(x_396);
x_398 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_55 = x_398;
x_56 = x_397;
goto block_371;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_399 = lean_ctor_get(x_376, 0);
lean_inc(x_399);
lean_dec(x_376);
x_400 = l_Lake_Glob_decodeToml___closed__2;
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_399);
lean_ctor_set(x_401, 1, x_400);
x_402 = lean_unsigned_to_nat(1u);
x_403 = lean_mk_array(x_402, x_401);
x_404 = l_Array_append___rarg(x_54, x_403);
lean_dec(x_403);
x_405 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_55 = x_405;
x_56 = x_404;
goto block_371;
}
}
}
}
block_371:
{
lean_object* x_57; lean_object* x_58; lean_object* x_318; lean_object* x_319; 
x_318 = l_Lake_PackageConfig_decodeToml___closed__23;
lean_inc(x_1);
x_319 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_318, x_1);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; 
x_320 = l_Lake_decodeLeanOptions___closed__1;
x_57 = x_320;
x_58 = x_56;
goto block_317;
}
else
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_319, 0);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
switch (lean_obj_tag(x_322)) {
case 0:
{
uint8_t x_323; 
x_323 = !lean_is_exclusive(x_322);
if (x_323 == 0)
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_324 = lean_ctor_get(x_322, 1);
lean_dec(x_324);
x_325 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_322, 1, x_325);
x_326 = lean_unsigned_to_nat(1u);
x_327 = lean_mk_array(x_326, x_322);
x_328 = l_Array_append___rarg(x_56, x_327);
lean_dec(x_327);
x_329 = l_Lake_decodeLeanOptions___closed__1;
x_57 = x_329;
x_58 = x_328;
goto block_317;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_330 = lean_ctor_get(x_322, 0);
lean_inc(x_330);
lean_dec(x_322);
x_331 = l_Lake_LeanConfig_decodeToml___closed__5;
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
x_333 = lean_unsigned_to_nat(1u);
x_334 = lean_mk_array(x_333, x_332);
x_335 = l_Array_append___rarg(x_56, x_334);
lean_dec(x_334);
x_336 = l_Lake_decodeLeanOptions___closed__1;
x_57 = x_336;
x_58 = x_335;
goto block_317;
}
}
case 2:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_337 = lean_ctor_get(x_322, 0);
lean_inc(x_337);
lean_dec(x_322);
x_338 = l_Lake_LeanConfig_decodeToml___closed__5;
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_unsigned_to_nat(1u);
x_341 = lean_mk_array(x_340, x_339);
x_342 = l_Array_append___rarg(x_56, x_341);
lean_dec(x_341);
x_343 = l_Lake_decodeLeanOptions___closed__1;
x_57 = x_343;
x_58 = x_342;
goto block_317;
}
case 3:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_344 = lean_ctor_get(x_322, 0);
lean_inc(x_344);
lean_dec(x_322);
x_345 = l_Lake_LeanConfig_decodeToml___closed__5;
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_unsigned_to_nat(1u);
x_348 = lean_mk_array(x_347, x_346);
x_349 = l_Array_append___rarg(x_56, x_348);
lean_dec(x_348);
x_350 = l_Lake_decodeLeanOptions___closed__1;
x_57 = x_350;
x_58 = x_349;
goto block_317;
}
case 5:
{
lean_object* x_351; lean_object* x_352; 
x_351 = lean_ctor_get(x_322, 1);
lean_inc(x_351);
lean_dec(x_322);
x_352 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_351);
lean_dec(x_351);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_352, 0);
lean_inc(x_353);
lean_dec(x_352);
x_354 = l_Array_append___rarg(x_56, x_353);
lean_dec(x_353);
x_355 = l_Lake_decodeLeanOptions___closed__1;
x_57 = x_355;
x_58 = x_354;
goto block_317;
}
else
{
lean_object* x_356; 
x_356 = lean_ctor_get(x_352, 0);
lean_inc(x_356);
lean_dec(x_352);
x_57 = x_356;
x_58 = x_56;
goto block_317;
}
}
default: 
{
uint8_t x_357; 
x_357 = !lean_is_exclusive(x_322);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_358 = lean_ctor_get(x_322, 1);
lean_dec(x_358);
x_359 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_322, 0);
lean_ctor_set(x_322, 1, x_359);
x_360 = lean_unsigned_to_nat(1u);
x_361 = lean_mk_array(x_360, x_322);
x_362 = l_Array_append___rarg(x_56, x_361);
lean_dec(x_361);
x_363 = l_Lake_decodeLeanOptions___closed__1;
x_57 = x_363;
x_58 = x_362;
goto block_317;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_364 = lean_ctor_get(x_322, 0);
lean_inc(x_364);
lean_dec(x_322);
x_365 = l_Lake_LeanConfig_decodeToml___closed__5;
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_unsigned_to_nat(1u);
x_368 = lean_mk_array(x_367, x_366);
x_369 = l_Array_append___rarg(x_56, x_368);
lean_dec(x_368);
x_370 = l_Lake_decodeLeanOptions___closed__1;
x_57 = x_370;
x_58 = x_369;
goto block_317;
}
}
}
}
block_317:
{
lean_object* x_59; lean_object* x_60; lean_object* x_283; lean_object* x_284; 
x_283 = l_Lake_PackageConfig_decodeToml___closed__21;
lean_inc(x_1);
x_284 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_283, x_1);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; 
x_285 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_59 = x_285;
x_60 = x_58;
goto block_282;
}
else
{
lean_object* x_286; lean_object* x_287; 
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
lean_dec(x_284);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
switch (lean_obj_tag(x_287)) {
case 0:
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
lean_dec(x_287);
x_59 = x_288;
x_60 = x_58;
goto block_282;
}
case 2:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l_Lake_Glob_decodeToml___closed__2;
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_unsigned_to_nat(1u);
x_293 = lean_mk_array(x_292, x_291);
x_294 = l_Array_append___rarg(x_58, x_293);
lean_dec(x_293);
x_295 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_59 = x_295;
x_60 = x_294;
goto block_282;
}
case 3:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_296 = lean_ctor_get(x_287, 0);
lean_inc(x_296);
lean_dec(x_287);
x_297 = l_Lake_Glob_decodeToml___closed__2;
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_299 = lean_unsigned_to_nat(1u);
x_300 = lean_mk_array(x_299, x_298);
x_301 = l_Array_append___rarg(x_58, x_300);
lean_dec(x_300);
x_302 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_59 = x_302;
x_60 = x_301;
goto block_282;
}
default: 
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_287);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_304 = lean_ctor_get(x_287, 1);
lean_dec(x_304);
x_305 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_287, 0);
lean_ctor_set(x_287, 1, x_305);
x_306 = lean_unsigned_to_nat(1u);
x_307 = lean_mk_array(x_306, x_287);
x_308 = l_Array_append___rarg(x_58, x_307);
lean_dec(x_307);
x_309 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_59 = x_309;
x_60 = x_308;
goto block_282;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_310 = lean_ctor_get(x_287, 0);
lean_inc(x_310);
lean_dec(x_287);
x_311 = l_Lake_Glob_decodeToml___closed__2;
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_mk_array(x_313, x_312);
x_315 = l_Array_append___rarg(x_58, x_314);
lean_dec(x_314);
x_316 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_59 = x_316;
x_60 = x_315;
goto block_282;
}
}
}
}
block_282:
{
lean_object* x_61; lean_object* x_62; lean_object* x_248; lean_object* x_249; 
x_248 = l_Lake_PackageConfig_decodeToml___closed__19;
lean_inc(x_1);
x_249 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_248, x_1);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; 
x_250 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_61 = x_250;
x_62 = x_60;
goto block_247;
}
else
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_249, 0);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_251, 1);
lean_inc(x_252);
lean_dec(x_251);
switch (lean_obj_tag(x_252)) {
case 0:
{
lean_object* x_253; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_61 = x_253;
x_62 = x_60;
goto block_247;
}
case 2:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_254 = lean_ctor_get(x_252, 0);
lean_inc(x_254);
lean_dec(x_252);
x_255 = l_Lake_Glob_decodeToml___closed__2;
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_unsigned_to_nat(1u);
x_258 = lean_mk_array(x_257, x_256);
x_259 = l_Array_append___rarg(x_60, x_258);
lean_dec(x_258);
x_260 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_61 = x_260;
x_62 = x_259;
goto block_247;
}
case 3:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_261 = lean_ctor_get(x_252, 0);
lean_inc(x_261);
lean_dec(x_252);
x_262 = l_Lake_Glob_decodeToml___closed__2;
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_unsigned_to_nat(1u);
x_265 = lean_mk_array(x_264, x_263);
x_266 = l_Array_append___rarg(x_60, x_265);
lean_dec(x_265);
x_267 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_61 = x_267;
x_62 = x_266;
goto block_247;
}
default: 
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_252);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_269 = lean_ctor_get(x_252, 1);
lean_dec(x_269);
x_270 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_252, 0);
lean_ctor_set(x_252, 1, x_270);
x_271 = lean_unsigned_to_nat(1u);
x_272 = lean_mk_array(x_271, x_252);
x_273 = l_Array_append___rarg(x_60, x_272);
lean_dec(x_272);
x_274 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_61 = x_274;
x_62 = x_273;
goto block_247;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_275 = lean_ctor_get(x_252, 0);
lean_inc(x_275);
lean_dec(x_252);
x_276 = l_Lake_Glob_decodeToml___closed__2;
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_unsigned_to_nat(1u);
x_279 = lean_mk_array(x_278, x_277);
x_280 = l_Array_append___rarg(x_60, x_279);
lean_dec(x_279);
x_281 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_61 = x_281;
x_62 = x_280;
goto block_247;
}
}
}
}
block_247:
{
lean_object* x_63; lean_object* x_64; lean_object* x_194; lean_object* x_195; 
x_194 = l_Lake_PackageConfig_decodeToml___closed__14;
lean_inc(x_1);
x_195 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_194, x_1);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = l_Lake_PackageConfig_decodeToml___closed__17;
x_63 = x_196;
x_64 = x_62;
goto block_193;
}
else
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_195, 0);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
switch (lean_obj_tag(x_198)) {
case 0:
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_200 = lean_ctor_get(x_198, 1);
lean_dec(x_200);
x_201 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_198, 1, x_201);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_mk_array(x_202, x_198);
x_204 = l_Array_append___rarg(x_62, x_203);
lean_dec(x_203);
x_205 = l_Lake_PackageConfig_decodeToml___closed__17;
x_63 = x_205;
x_64 = x_204;
goto block_193;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_206 = lean_ctor_get(x_198, 0);
lean_inc(x_206);
lean_dec(x_198);
x_207 = l_Lake_LeanConfig_decodeToml___closed__5;
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_unsigned_to_nat(1u);
x_210 = lean_mk_array(x_209, x_208);
x_211 = l_Array_append___rarg(x_62, x_210);
lean_dec(x_210);
x_212 = l_Lake_PackageConfig_decodeToml___closed__17;
x_63 = x_212;
x_64 = x_211;
goto block_193;
}
}
case 2:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_213 = lean_ctor_get(x_198, 0);
lean_inc(x_213);
lean_dec(x_198);
x_214 = l_Lake_LeanConfig_decodeToml___closed__5;
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_unsigned_to_nat(1u);
x_217 = lean_mk_array(x_216, x_215);
x_218 = l_Array_append___rarg(x_62, x_217);
lean_dec(x_217);
x_219 = l_Lake_PackageConfig_decodeToml___closed__17;
x_63 = x_219;
x_64 = x_218;
goto block_193;
}
case 3:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_220 = lean_ctor_get(x_198, 0);
lean_inc(x_220);
lean_dec(x_198);
x_221 = l_Lake_LeanConfig_decodeToml___closed__5;
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
x_223 = lean_unsigned_to_nat(1u);
x_224 = lean_mk_array(x_223, x_222);
x_225 = l_Array_append___rarg(x_62, x_224);
lean_dec(x_224);
x_226 = l_Lake_PackageConfig_decodeToml___closed__17;
x_63 = x_226;
x_64 = x_225;
goto block_193;
}
case 5:
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_198, 1);
lean_inc(x_227);
lean_dec(x_198);
x_228 = l_Lake_Toml_decodeArray___at_Lake_PackageConfig_decodeToml___spec__1(x_227);
lean_dec(x_227);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
lean_dec(x_228);
x_230 = l_Array_append___rarg(x_62, x_229);
lean_dec(x_229);
x_231 = l_Lake_PackageConfig_decodeToml___closed__17;
x_63 = x_231;
x_64 = x_230;
goto block_193;
}
else
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_228, 0);
lean_inc(x_232);
lean_dec(x_228);
x_63 = x_232;
x_64 = x_62;
goto block_193;
}
}
default: 
{
uint8_t x_233; 
x_233 = !lean_is_exclusive(x_198);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_234 = lean_ctor_get(x_198, 1);
lean_dec(x_234);
x_235 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_198, 0);
lean_ctor_set(x_198, 1, x_235);
x_236 = lean_unsigned_to_nat(1u);
x_237 = lean_mk_array(x_236, x_198);
x_238 = l_Array_append___rarg(x_62, x_237);
lean_dec(x_237);
x_239 = l_Lake_PackageConfig_decodeToml___closed__17;
x_63 = x_239;
x_64 = x_238;
goto block_193;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_240 = lean_ctor_get(x_198, 0);
lean_inc(x_240);
lean_dec(x_198);
x_241 = l_Lake_LeanConfig_decodeToml___closed__5;
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_unsigned_to_nat(1u);
x_244 = lean_mk_array(x_243, x_242);
x_245 = l_Array_append___rarg(x_62, x_244);
lean_dec(x_244);
x_246 = l_Lake_PackageConfig_decodeToml___closed__17;
x_63 = x_246;
x_64 = x_245;
goto block_193;
}
}
}
}
block_193:
{
lean_object* x_65; lean_object* x_66; lean_object* x_159; lean_object* x_160; 
x_159 = l_Lake_PackageConfig_decodeToml___closed__11;
lean_inc(x_1);
x_160 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_159, x_1);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = l_Lake_PackageConfig_decodeToml___closed__12;
x_65 = x_161;
x_66 = x_64;
goto block_158;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
switch (lean_obj_tag(x_163)) {
case 0:
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_65 = x_164;
x_66 = x_64;
goto block_158;
}
case 2:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lake_Glob_decodeToml___closed__2;
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_unsigned_to_nat(1u);
x_169 = lean_mk_array(x_168, x_167);
x_170 = l_Array_append___rarg(x_64, x_169);
lean_dec(x_169);
x_171 = l_Lake_PackageConfig_decodeToml___closed__12;
x_65 = x_171;
x_66 = x_170;
goto block_158;
}
case 3:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_163, 0);
lean_inc(x_172);
lean_dec(x_163);
x_173 = l_Lake_Glob_decodeToml___closed__2;
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = lean_unsigned_to_nat(1u);
x_176 = lean_mk_array(x_175, x_174);
x_177 = l_Array_append___rarg(x_64, x_176);
lean_dec(x_176);
x_178 = l_Lake_PackageConfig_decodeToml___closed__12;
x_65 = x_178;
x_66 = x_177;
goto block_158;
}
default: 
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_163);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_163, 1);
lean_dec(x_180);
x_181 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_163, 0);
lean_ctor_set(x_163, 1, x_181);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_mk_array(x_182, x_163);
x_184 = l_Array_append___rarg(x_64, x_183);
lean_dec(x_183);
x_185 = l_Lake_PackageConfig_decodeToml___closed__12;
x_65 = x_185;
x_66 = x_184;
goto block_158;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_186 = lean_ctor_get(x_163, 0);
lean_inc(x_186);
lean_dec(x_163);
x_187 = l_Lake_Glob_decodeToml___closed__2;
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_unsigned_to_nat(1u);
x_190 = lean_mk_array(x_189, x_188);
x_191 = l_Array_append___rarg(x_64, x_190);
lean_dec(x_190);
x_192 = l_Lake_PackageConfig_decodeToml___closed__12;
x_65 = x_192;
x_66 = x_191;
goto block_158;
}
}
}
}
block_158:
{
uint8_t x_67; lean_object* x_68; lean_object* x_117; lean_object* x_118; 
x_117 = l_Lake_PackageConfig_decodeToml___closed__9;
lean_inc(x_1);
x_118 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_41, x_117, x_1);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = 1;
x_67 = x_119;
x_68 = x_66;
goto block_116;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
lean_dec(x_120);
switch (lean_obj_tag(x_121)) {
case 0:
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_123 = lean_ctor_get(x_121, 1);
lean_dec(x_123);
x_124 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_121, 1, x_124);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_mk_array(x_125, x_121);
x_127 = l_Array_append___rarg(x_66, x_126);
lean_dec(x_126);
x_128 = 1;
x_67 = x_128;
x_68 = x_127;
goto block_116;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_129 = lean_ctor_get(x_121, 0);
lean_inc(x_129);
lean_dec(x_121);
x_130 = l_Lake_LeanConfig_decodeToml___closed__20;
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_unsigned_to_nat(1u);
x_133 = lean_mk_array(x_132, x_131);
x_134 = l_Array_append___rarg(x_66, x_133);
lean_dec(x_133);
x_135 = 1;
x_67 = x_135;
x_68 = x_134;
goto block_116;
}
}
case 2:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_136 = lean_ctor_get(x_121, 0);
lean_inc(x_136);
lean_dec(x_121);
x_137 = l_Lake_LeanConfig_decodeToml___closed__20;
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_mk_array(x_139, x_138);
x_141 = l_Array_append___rarg(x_66, x_140);
lean_dec(x_140);
x_142 = 1;
x_67 = x_142;
x_68 = x_141;
goto block_116;
}
case 3:
{
uint8_t x_143; 
x_143 = lean_ctor_get_uint8(x_121, sizeof(void*)*1);
lean_dec(x_121);
x_67 = x_143;
x_68 = x_66;
goto block_116;
}
default: 
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_121);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_121, 1);
lean_dec(x_145);
x_146 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_121, 0);
lean_ctor_set(x_121, 1, x_146);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_mk_array(x_147, x_121);
x_149 = l_Array_append___rarg(x_66, x_148);
lean_dec(x_148);
x_150 = 1;
x_67 = x_150;
x_68 = x_149;
goto block_116;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_151 = lean_ctor_get(x_121, 0);
lean_inc(x_151);
lean_dec(x_121);
x_152 = l_Lake_LeanConfig_decodeToml___closed__20;
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_mk_array(x_154, x_153);
x_156 = l_Array_append___rarg(x_66, x_155);
lean_dec(x_155);
x_157 = 1;
x_67 = x_157;
x_68 = x_156;
goto block_116;
}
}
}
}
block_116:
{
lean_object* x_69; lean_object* x_70; lean_object* x_111; 
lean_inc(x_1);
x_111 = l_Lake_LeanConfig_decodeToml(x_1);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l_Array_append___rarg(x_68, x_112);
lean_dec(x_112);
x_114 = l_Lake_PackageConfig_decodeToml___closed__7;
x_69 = x_114;
x_70 = x_113;
goto block_110;
}
else
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_111, 0);
lean_inc(x_115);
lean_dec(x_111);
x_69 = x_115;
x_70 = x_68;
goto block_110;
}
block_110:
{
lean_object* x_71; 
x_71 = l_Lake_WorkspaceConfig_decodeToml(x_1);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Array_append___rarg(x_70, x_72);
lean_dec(x_72);
x_74 = lean_box(0);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = 0;
x_76 = l_Lake_StrPat_decodeToml___closed__6;
lean_inc(x_11);
x_77 = l_Lean_Name_toString(x_11, x_75, x_76);
x_78 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = l_Lake_PackageConfig_decodeToml___closed__5;
x_81 = lean_string_append(x_79, x_80);
x_82 = l_System_Platform_target;
x_83 = lean_string_append(x_81, x_82);
x_84 = l_Lake_PackageConfig_decodeToml___closed__6;
x_85 = lean_string_append(x_83, x_84);
x_86 = l_Lake_decodeLeanOptions___closed__1;
x_87 = lean_alloc_ctor(0, 29, 3);
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_69);
lean_ctor_set(x_87, 2, x_11);
lean_ctor_set(x_87, 3, x_74);
lean_ctor_set(x_87, 4, x_86);
lean_ctor_set(x_87, 5, x_86);
lean_ctor_set(x_87, 6, x_14);
lean_ctor_set(x_87, 7, x_16);
lean_ctor_set(x_87, 8, x_18);
lean_ctor_set(x_87, 9, x_20);
lean_ctor_set(x_87, 10, x_22);
lean_ctor_set(x_87, 11, x_24);
lean_ctor_set(x_87, 12, x_26);
lean_ctor_set(x_87, 13, x_74);
lean_ctor_set(x_87, 14, x_28);
lean_ctor_set(x_87, 15, x_30);
lean_ctor_set(x_87, 16, x_85);
lean_ctor_set(x_87, 17, x_44);
lean_ctor_set(x_87, 18, x_45);
lean_ctor_set(x_87, 19, x_47);
lean_ctor_set(x_87, 20, x_49);
lean_ctor_set(x_87, 21, x_51);
lean_ctor_set(x_87, 22, x_53);
lean_ctor_set(x_87, 23, x_55);
lean_ctor_set(x_87, 24, x_57);
lean_ctor_set(x_87, 25, x_59);
lean_ctor_set(x_87, 26, x_61);
lean_ctor_set(x_87, 27, x_63);
lean_ctor_set(x_87, 28, x_65);
lean_ctor_set_uint8(x_87, sizeof(void*)*29, x_12);
lean_ctor_set_uint8(x_87, sizeof(void*)*29 + 1, x_32);
lean_ctor_set_uint8(x_87, sizeof(void*)*29 + 2, x_67);
x_3 = x_87;
x_4 = x_73;
goto block_8;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_30, 0);
lean_inc(x_88);
x_89 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_90 = l_Lake_decodeLeanOptions___closed__1;
x_91 = lean_alloc_ctor(0, 29, 3);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_69);
lean_ctor_set(x_91, 2, x_11);
lean_ctor_set(x_91, 3, x_74);
lean_ctor_set(x_91, 4, x_90);
lean_ctor_set(x_91, 5, x_90);
lean_ctor_set(x_91, 6, x_14);
lean_ctor_set(x_91, 7, x_16);
lean_ctor_set(x_91, 8, x_18);
lean_ctor_set(x_91, 9, x_20);
lean_ctor_set(x_91, 10, x_22);
lean_ctor_set(x_91, 11, x_24);
lean_ctor_set(x_91, 12, x_26);
lean_ctor_set(x_91, 13, x_74);
lean_ctor_set(x_91, 14, x_28);
lean_ctor_set(x_91, 15, x_30);
lean_ctor_set(x_91, 16, x_88);
lean_ctor_set(x_91, 17, x_44);
lean_ctor_set(x_91, 18, x_45);
lean_ctor_set(x_91, 19, x_47);
lean_ctor_set(x_91, 20, x_49);
lean_ctor_set(x_91, 21, x_51);
lean_ctor_set(x_91, 22, x_53);
lean_ctor_set(x_91, 23, x_55);
lean_ctor_set(x_91, 24, x_57);
lean_ctor_set(x_91, 25, x_59);
lean_ctor_set(x_91, 26, x_61);
lean_ctor_set(x_91, 27, x_63);
lean_ctor_set(x_91, 28, x_65);
lean_ctor_set_uint8(x_91, sizeof(void*)*29, x_12);
lean_ctor_set_uint8(x_91, sizeof(void*)*29 + 1, x_32);
lean_ctor_set_uint8(x_91, sizeof(void*)*29 + 2, x_67);
x_3 = x_91;
x_4 = x_73;
goto block_8;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_71, 0);
lean_inc(x_92);
lean_dec(x_71);
x_93 = lean_box(0);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_94 = 0;
x_95 = l_Lake_StrPat_decodeToml___closed__6;
lean_inc(x_11);
x_96 = l_Lean_Name_toString(x_11, x_94, x_95);
x_97 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_98 = lean_string_append(x_97, x_96);
lean_dec(x_96);
x_99 = l_Lake_PackageConfig_decodeToml___closed__5;
x_100 = lean_string_append(x_98, x_99);
x_101 = l_System_Platform_target;
x_102 = lean_string_append(x_100, x_101);
x_103 = l_Lake_PackageConfig_decodeToml___closed__6;
x_104 = lean_string_append(x_102, x_103);
x_105 = l_Lake_decodeLeanOptions___closed__1;
x_106 = lean_alloc_ctor(0, 29, 3);
lean_ctor_set(x_106, 0, x_92);
lean_ctor_set(x_106, 1, x_69);
lean_ctor_set(x_106, 2, x_11);
lean_ctor_set(x_106, 3, x_93);
lean_ctor_set(x_106, 4, x_105);
lean_ctor_set(x_106, 5, x_105);
lean_ctor_set(x_106, 6, x_14);
lean_ctor_set(x_106, 7, x_16);
lean_ctor_set(x_106, 8, x_18);
lean_ctor_set(x_106, 9, x_20);
lean_ctor_set(x_106, 10, x_22);
lean_ctor_set(x_106, 11, x_24);
lean_ctor_set(x_106, 12, x_26);
lean_ctor_set(x_106, 13, x_93);
lean_ctor_set(x_106, 14, x_28);
lean_ctor_set(x_106, 15, x_30);
lean_ctor_set(x_106, 16, x_104);
lean_ctor_set(x_106, 17, x_44);
lean_ctor_set(x_106, 18, x_45);
lean_ctor_set(x_106, 19, x_47);
lean_ctor_set(x_106, 20, x_49);
lean_ctor_set(x_106, 21, x_51);
lean_ctor_set(x_106, 22, x_53);
lean_ctor_set(x_106, 23, x_55);
lean_ctor_set(x_106, 24, x_57);
lean_ctor_set(x_106, 25, x_59);
lean_ctor_set(x_106, 26, x_61);
lean_ctor_set(x_106, 27, x_63);
lean_ctor_set(x_106, 28, x_65);
lean_ctor_set_uint8(x_106, sizeof(void*)*29, x_12);
lean_ctor_set_uint8(x_106, sizeof(void*)*29 + 1, x_32);
lean_ctor_set_uint8(x_106, sizeof(void*)*29 + 2, x_67);
x_3 = x_106;
x_4 = x_70;
goto block_8;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_30, 0);
lean_inc(x_107);
x_108 = l_Lake_decodeLeanOptions___closed__1;
x_109 = lean_alloc_ctor(0, 29, 3);
lean_ctor_set(x_109, 0, x_92);
lean_ctor_set(x_109, 1, x_69);
lean_ctor_set(x_109, 2, x_11);
lean_ctor_set(x_109, 3, x_93);
lean_ctor_set(x_109, 4, x_108);
lean_ctor_set(x_109, 5, x_108);
lean_ctor_set(x_109, 6, x_14);
lean_ctor_set(x_109, 7, x_16);
lean_ctor_set(x_109, 8, x_18);
lean_ctor_set(x_109, 9, x_20);
lean_ctor_set(x_109, 10, x_22);
lean_ctor_set(x_109, 11, x_24);
lean_ctor_set(x_109, 12, x_26);
lean_ctor_set(x_109, 13, x_93);
lean_ctor_set(x_109, 14, x_28);
lean_ctor_set(x_109, 15, x_30);
lean_ctor_set(x_109, 16, x_107);
lean_ctor_set(x_109, 17, x_44);
lean_ctor_set(x_109, 18, x_45);
lean_ctor_set(x_109, 19, x_47);
lean_ctor_set(x_109, 20, x_49);
lean_ctor_set(x_109, 21, x_51);
lean_ctor_set(x_109, 22, x_53);
lean_ctor_set(x_109, 23, x_55);
lean_ctor_set(x_109, 24, x_57);
lean_ctor_set(x_109, 25, x_59);
lean_ctor_set(x_109, 26, x_61);
lean_ctor_set(x_109, 27, x_63);
lean_ctor_set(x_109, 28, x_65);
lean_ctor_set_uint8(x_109, sizeof(void*)*29, x_12);
lean_ctor_set_uint8(x_109, sizeof(void*)*29 + 1, x_32);
lean_ctor_set_uint8(x_109, sizeof(void*)*29 + 2, x_67);
x_3 = x_109;
x_4 = x_70;
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
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_PackageConfig_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_PackageConfig_decodeToml___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_PackageConfig_decodeToml___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_PackageConfig_decodeToml___spec__1(x_1);
lean_dec(x_1);
return x_2;
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
x_13 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
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
x_27 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_decodeToml___spec__3(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__4(lean_object* x_1) {
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
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__5(x_1, x_8, x_9, x_4);
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("export", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1;
x_2 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1(lean_object* x_1, uint8_t x_2) {
_start:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2;
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
x_5 = lean_array_mk(x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4;
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = lean_array_mk(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("roots", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("defaultFacets", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("leanArts", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanLibConfig_decodeToml___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanLibConfig_decodeToml___closed__7;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanLibConfig_decodeToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("libName", 7, 7);
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
x_1 = lean_mk_string_unchecked("globs", 5, 5);
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
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_275; lean_object* x_276; 
x_275 = l_Lake_LeanOption_decodeToml___closed__10;
lean_inc(x_1);
x_276 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(x_1, x_275, x_2);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
lean_dec(x_276);
x_278 = l_Lake_LeanOption_decodeToml___closed__3;
x_279 = l_Array_append___rarg(x_278, x_277);
lean_dec(x_277);
x_280 = lean_box(0);
x_9 = x_280;
x_10 = x_279;
goto block_274;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_276, 0);
lean_inc(x_281);
lean_dec(x_276);
x_282 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_281;
x_10 = x_282;
goto block_274;
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
block_274:
{
lean_object* x_11; lean_object* x_12; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_240 = l_Lake_PackageConfig_decodeToml___closed__59;
lean_inc(x_1);
x_241 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_239, x_240, x_1);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; 
x_242 = l_Lake_PackageConfig_decodeToml___closed__60;
x_11 = x_242;
x_12 = x_10;
goto block_238;
}
else
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
switch (lean_obj_tag(x_244)) {
case 0:
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
x_11 = x_245;
x_12 = x_10;
goto block_238;
}
case 2:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_246 = lean_ctor_get(x_244, 0);
lean_inc(x_246);
lean_dec(x_244);
x_247 = l_Lake_Glob_decodeToml___closed__2;
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_unsigned_to_nat(1u);
x_250 = lean_mk_array(x_249, x_248);
x_251 = l_Array_append___rarg(x_10, x_250);
lean_dec(x_250);
x_252 = l_Lake_PackageConfig_decodeToml___closed__60;
x_11 = x_252;
x_12 = x_251;
goto block_238;
}
case 3:
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_253 = lean_ctor_get(x_244, 0);
lean_inc(x_253);
lean_dec(x_244);
x_254 = l_Lake_Glob_decodeToml___closed__2;
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_unsigned_to_nat(1u);
x_257 = lean_mk_array(x_256, x_255);
x_258 = l_Array_append___rarg(x_10, x_257);
lean_dec(x_257);
x_259 = l_Lake_PackageConfig_decodeToml___closed__60;
x_11 = x_259;
x_12 = x_258;
goto block_238;
}
default: 
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_244);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_261 = lean_ctor_get(x_244, 1);
lean_dec(x_261);
x_262 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_244, 0);
lean_ctor_set(x_244, 1, x_262);
x_263 = lean_unsigned_to_nat(1u);
x_264 = lean_mk_array(x_263, x_244);
x_265 = l_Array_append___rarg(x_10, x_264);
lean_dec(x_264);
x_266 = l_Lake_PackageConfig_decodeToml___closed__60;
x_11 = x_266;
x_12 = x_265;
goto block_238;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_267 = lean_ctor_get(x_244, 0);
lean_inc(x_267);
lean_dec(x_244);
x_268 = l_Lake_Glob_decodeToml___closed__2;
x_269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_mk_array(x_270, x_269);
x_272 = l_Array_append___rarg(x_10, x_271);
lean_dec(x_271);
x_273 = l_Lake_PackageConfig_decodeToml___closed__60;
x_11 = x_273;
x_12 = x_272;
goto block_238;
}
}
}
}
block_238:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_13 = lean_box(0);
lean_inc(x_9);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_9);
lean_ctor_set(x_190, 1, x_13);
x_191 = lean_array_mk(x_190);
x_192 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_193 = l_Lake_LeanLibConfig_decodeToml___closed__2;
lean_inc(x_1);
x_194 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_192, x_193, x_1);
if (lean_obj_tag(x_194) == 0)
{
x_14 = x_191;
x_15 = x_12;
goto block_189;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
lean_dec(x_194);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
switch (lean_obj_tag(x_196)) {
case 0:
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_196, 1);
lean_dec(x_198);
x_199 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_196, 1, x_199);
x_200 = lean_unsigned_to_nat(1u);
x_201 = lean_mk_array(x_200, x_196);
x_202 = l_Array_append___rarg(x_12, x_201);
lean_dec(x_201);
x_14 = x_191;
x_15 = x_202;
goto block_189;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_196, 0);
lean_inc(x_203);
lean_dec(x_196);
x_204 = l_Lake_LeanConfig_decodeToml___closed__5;
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_mk_array(x_206, x_205);
x_208 = l_Array_append___rarg(x_12, x_207);
lean_dec(x_207);
x_14 = x_191;
x_15 = x_208;
goto block_189;
}
}
case 2:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_196, 0);
lean_inc(x_209);
lean_dec(x_196);
x_210 = l_Lake_LeanConfig_decodeToml___closed__5;
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_mk_array(x_212, x_211);
x_214 = l_Array_append___rarg(x_12, x_213);
lean_dec(x_213);
x_14 = x_191;
x_15 = x_214;
goto block_189;
}
case 3:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_215 = lean_ctor_get(x_196, 0);
lean_inc(x_215);
lean_dec(x_196);
x_216 = l_Lake_LeanConfig_decodeToml___closed__5;
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_unsigned_to_nat(1u);
x_219 = lean_mk_array(x_218, x_217);
x_220 = l_Array_append___rarg(x_12, x_219);
lean_dec(x_219);
x_14 = x_191;
x_15 = x_220;
goto block_189;
}
case 5:
{
lean_object* x_221; lean_object* x_222; 
x_221 = lean_ctor_get(x_196, 1);
lean_inc(x_221);
lean_dec(x_196);
x_222 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(x_221);
lean_dec(x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec(x_222);
x_224 = l_Array_append___rarg(x_12, x_223);
lean_dec(x_223);
x_14 = x_191;
x_15 = x_224;
goto block_189;
}
else
{
lean_object* x_225; 
lean_dec(x_191);
x_225 = lean_ctor_get(x_222, 0);
lean_inc(x_225);
lean_dec(x_222);
x_14 = x_225;
x_15 = x_12;
goto block_189;
}
}
default: 
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_196);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_227 = lean_ctor_get(x_196, 1);
lean_dec(x_227);
x_228 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_196, 0);
lean_ctor_set(x_196, 1, x_228);
x_229 = lean_unsigned_to_nat(1u);
x_230 = lean_mk_array(x_229, x_196);
x_231 = l_Array_append___rarg(x_12, x_230);
lean_dec(x_230);
x_14 = x_191;
x_15 = x_231;
goto block_189;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_232 = lean_ctor_get(x_196, 0);
lean_inc(x_232);
lean_dec(x_196);
x_233 = l_Lake_LeanConfig_decodeToml___closed__5;
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_unsigned_to_nat(1u);
x_236 = lean_mk_array(x_235, x_234);
x_237 = l_Array_append___rarg(x_12, x_236);
lean_dec(x_236);
x_14 = x_191;
x_15 = x_237;
goto block_189;
}
}
}
}
block_189:
{
lean_object* x_16; lean_object* x_17; size_t x_168; size_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_168 = lean_array_size(x_14);
x_169 = 0;
lean_inc(x_14);
x_170 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_decodeToml___spec__3(x_168, x_169, x_14);
x_171 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_172 = l_Lake_LeanLibConfig_decodeToml___closed__12;
lean_inc(x_1);
x_173 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_171, x_172, x_1);
if (lean_obj_tag(x_173) == 0)
{
x_16 = x_170;
x_17 = x_15;
goto block_167;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
if (lean_obj_tag(x_175) == 5)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__4(x_176);
lean_dec(x_176);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_177, 0);
lean_inc(x_178);
lean_dec(x_177);
x_179 = l_Array_append___rarg(x_15, x_178);
lean_dec(x_178);
x_16 = x_170;
x_17 = x_179;
goto block_167;
}
else
{
lean_object* x_180; 
lean_dec(x_170);
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
lean_dec(x_177);
x_16 = x_180;
x_17 = x_15;
goto block_167;
}
}
else
{
lean_object* x_181; 
x_181 = l_Lake_Glob_decodeToml(x_175);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = lean_unsigned_to_nat(1u);
x_184 = lean_mk_array(x_183, x_182);
x_185 = l_Array_append___rarg(x_15, x_184);
lean_dec(x_184);
x_16 = x_170;
x_17 = x_185;
goto block_167;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_170);
x_186 = lean_ctor_get(x_181, 0);
lean_inc(x_186);
lean_dec(x_181);
x_187 = lean_unsigned_to_nat(1u);
x_188 = lean_mk_array(x_187, x_186);
x_16 = x_188;
x_17 = x_15;
goto block_167;
}
}
}
block_167:
{
lean_object* x_18; lean_object* x_19; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = 0;
x_135 = l_Lake_StrPat_decodeToml___closed__6;
lean_inc(x_9);
x_136 = l_Lean_Name_toString(x_9, x_134, x_135);
x_137 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_138 = l_Lake_LeanLibConfig_decodeToml___closed__10;
lean_inc(x_1);
x_139 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_137, x_138, x_1);
if (lean_obj_tag(x_139) == 0)
{
x_18 = x_136;
x_19 = x_17;
goto block_133;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
switch (lean_obj_tag(x_141)) {
case 0:
{
lean_object* x_142; 
lean_dec(x_136);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_18 = x_142;
x_19 = x_17;
goto block_133;
}
case 2:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_dec(x_141);
x_144 = l_Lake_Glob_decodeToml___closed__2;
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_mk_array(x_146, x_145);
x_148 = l_Array_append___rarg(x_17, x_147);
lean_dec(x_147);
x_18 = x_136;
x_19 = x_148;
goto block_133;
}
case 3:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_ctor_get(x_141, 0);
lean_inc(x_149);
lean_dec(x_141);
x_150 = l_Lake_Glob_decodeToml___closed__2;
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_mk_array(x_152, x_151);
x_154 = l_Array_append___rarg(x_17, x_153);
lean_dec(x_153);
x_18 = x_136;
x_19 = x_154;
goto block_133;
}
default: 
{
uint8_t x_155; 
x_155 = !lean_is_exclusive(x_141);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_141, 1);
lean_dec(x_156);
x_157 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_141, 0);
lean_ctor_set(x_141, 1, x_157);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_mk_array(x_158, x_141);
x_160 = l_Array_append___rarg(x_17, x_159);
lean_dec(x_159);
x_18 = x_136;
x_19 = x_160;
goto block_133;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_161 = lean_ctor_get(x_141, 0);
lean_inc(x_161);
lean_dec(x_141);
x_162 = l_Lake_Glob_decodeToml___closed__2;
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_unsigned_to_nat(1u);
x_165 = lean_mk_array(x_164, x_163);
x_166 = l_Array_append___rarg(x_17, x_165);
lean_dec(x_165);
x_18 = x_136;
x_19 = x_166;
goto block_133;
}
}
}
}
block_133:
{
uint8_t x_20; lean_object* x_21; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_92 = l_Lake_PackageConfig_decodeToml___closed__62;
lean_inc(x_1);
x_93 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_91, x_92, x_1);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = 0;
x_20 = x_94;
x_21 = x_19;
goto block_90;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
switch (lean_obj_tag(x_96)) {
case 0:
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_98 = lean_ctor_get(x_96, 1);
lean_dec(x_98);
x_99 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_96, 1, x_99);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_mk_array(x_100, x_96);
x_102 = l_Array_append___rarg(x_19, x_101);
lean_dec(x_101);
x_103 = 0;
x_20 = x_103;
x_21 = x_102;
goto block_90;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_96, 0);
lean_inc(x_104);
lean_dec(x_96);
x_105 = l_Lake_LeanConfig_decodeToml___closed__20;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_mk_array(x_107, x_106);
x_109 = l_Array_append___rarg(x_19, x_108);
lean_dec(x_108);
x_110 = 0;
x_20 = x_110;
x_21 = x_109;
goto block_90;
}
}
case 2:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_111 = lean_ctor_get(x_96, 0);
lean_inc(x_111);
lean_dec(x_96);
x_112 = l_Lake_LeanConfig_decodeToml___closed__20;
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_unsigned_to_nat(1u);
x_115 = lean_mk_array(x_114, x_113);
x_116 = l_Array_append___rarg(x_19, x_115);
lean_dec(x_115);
x_117 = 0;
x_20 = x_117;
x_21 = x_116;
goto block_90;
}
case 3:
{
uint8_t x_118; 
x_118 = lean_ctor_get_uint8(x_96, sizeof(void*)*1);
lean_dec(x_96);
x_20 = x_118;
x_21 = x_19;
goto block_90;
}
default: 
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_96);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_120 = lean_ctor_get(x_96, 1);
lean_dec(x_120);
x_121 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_96, 0);
lean_ctor_set(x_96, 1, x_121);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_mk_array(x_122, x_96);
x_124 = l_Array_append___rarg(x_19, x_123);
lean_dec(x_123);
x_125 = 0;
x_20 = x_125;
x_21 = x_124;
goto block_90;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_126 = lean_ctor_get(x_96, 0);
lean_inc(x_126);
lean_dec(x_96);
x_127 = l_Lake_LeanConfig_decodeToml___closed__20;
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_unsigned_to_nat(1u);
x_130 = lean_mk_array(x_129, x_128);
x_131 = l_Array_append___rarg(x_19, x_130);
lean_dec(x_130);
x_132 = 0;
x_20 = x_132;
x_21 = x_131;
goto block_90;
}
}
}
}
block_90:
{
lean_object* x_22; lean_object* x_23; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_37 = l_Lake_LeanLibConfig_decodeToml___closed__4;
lean_inc(x_1);
x_38 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_36, x_37, x_1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_22 = x_39;
x_23 = x_21;
goto block_35;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
switch (lean_obj_tag(x_41)) {
case 0:
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_41, 1);
lean_dec(x_43);
x_44 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_41, 1, x_44);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_mk_array(x_45, x_41);
x_47 = l_Array_append___rarg(x_21, x_46);
lean_dec(x_46);
x_48 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_22 = x_48;
x_23 = x_47;
goto block_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
x_50 = l_Lake_LeanConfig_decodeToml___closed__5;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_mk_array(x_52, x_51);
x_54 = l_Array_append___rarg(x_21, x_53);
lean_dec(x_53);
x_55 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_22 = x_55;
x_23 = x_54;
goto block_35;
}
}
case 2:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_56 = lean_ctor_get(x_41, 0);
lean_inc(x_56);
lean_dec(x_41);
x_57 = l_Lake_LeanConfig_decodeToml___closed__5;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_mk_array(x_59, x_58);
x_61 = l_Array_append___rarg(x_21, x_60);
lean_dec(x_60);
x_62 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_22 = x_62;
x_23 = x_61;
goto block_35;
}
case 3:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_41, 0);
lean_inc(x_63);
lean_dec(x_41);
x_64 = l_Lake_LeanConfig_decodeToml___closed__5;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_mk_array(x_66, x_65);
x_68 = l_Array_append___rarg(x_21, x_67);
lean_dec(x_67);
x_69 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_22 = x_69;
x_23 = x_68;
goto block_35;
}
case 5:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_41, 1);
lean_inc(x_70);
lean_dec(x_41);
x_71 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(x_70);
lean_dec(x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Array_append___rarg(x_21, x_72);
lean_dec(x_72);
x_74 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_22 = x_74;
x_23 = x_73;
goto block_35;
}
else
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_71, 0);
lean_inc(x_75);
lean_dec(x_71);
x_22 = x_75;
x_23 = x_21;
goto block_35;
}
}
default: 
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_41);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_77 = lean_ctor_get(x_41, 1);
lean_dec(x_77);
x_78 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_41, 0);
lean_ctor_set(x_41, 1, x_78);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_mk_array(x_79, x_41);
x_81 = l_Array_append___rarg(x_21, x_80);
lean_dec(x_80);
x_82 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_22 = x_82;
x_23 = x_81;
goto block_35;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_41, 0);
lean_inc(x_83);
lean_dec(x_41);
x_84 = l_Lake_LeanConfig_decodeToml___closed__5;
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_mk_array(x_86, x_85);
x_88 = l_Array_append___rarg(x_21, x_87);
lean_dec(x_87);
x_89 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_22 = x_89;
x_23 = x_88;
goto block_35;
}
}
}
}
block_35:
{
lean_object* x_24; 
x_24 = l_Lake_LeanConfig_decodeToml(x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Array_append___rarg(x_23, x_25);
lean_dec(x_25);
x_27 = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed), 2, 1);
lean_closure_set(x_27, 0, x_13);
x_28 = l_Lake_PackageConfig_decodeToml___closed__7;
x_29 = l_Lake_decodeLeanOptions___closed__1;
x_30 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_9);
lean_ctor_set(x_30, 2, x_11);
lean_ctor_set(x_30, 3, x_14);
lean_ctor_set(x_30, 4, x_16);
lean_ctor_set(x_30, 5, x_18);
lean_ctor_set(x_30, 6, x_29);
lean_ctor_set(x_30, 7, x_22);
lean_ctor_set(x_30, 8, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*9, x_20);
x_3 = x_30;
x_4 = x_26;
goto block_8;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_24, 0);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed), 2, 1);
lean_closure_set(x_32, 0, x_13);
x_33 = l_Lake_decodeLeanOptions___closed__1;
x_34 = lean_alloc_ctor(0, 9, 1);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_9);
lean_ctor_set(x_34, 2, x_11);
lean_ctor_set(x_34, 3, x_14);
lean_ctor_set(x_34, 4, x_16);
lean_ctor_set(x_34, 5, x_18);
lean_ctor_set(x_34, 6, x_33);
lean_ctor_set(x_34, 7, x_22);
lean_ctor_set(x_34, 8, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*9, x_20);
x_3 = x_34;
x_4 = x_23;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_decodeToml___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_decodeToml___spec__3(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_2);
lean_dec(x_2);
x_4 = l_Lake_LeanLibConfig_decodeToml___lambda__1(x_1, x_3);
return x_4;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("supportInterpreter", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_decodeToml___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exeName", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_decodeToml___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("root", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_LeanExeConfig_decodeToml___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_LeanExeConfig_decodeToml___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_192; lean_object* x_193; 
x_192 = l_Lake_LeanOption_decodeToml___closed__10;
lean_inc(x_1);
x_193 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__3(x_1, x_192, x_2);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec(x_193);
x_195 = l_Lake_LeanOption_decodeToml___closed__3;
x_196 = l_Array_append___rarg(x_195, x_194);
lean_dec(x_194);
x_197 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_197;
x_10 = x_196;
goto block_191;
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_193, 0);
lean_inc(x_198);
lean_dec(x_193);
x_199 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_198;
x_10 = x_199;
goto block_191;
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
block_191:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_11 = l_Lake_stringToLegalOrSimpleName(x_9);
x_156 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_157 = l_Lake_PackageConfig_decodeToml___closed__59;
lean_inc(x_1);
x_158 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_156, x_157, x_1);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; 
x_159 = l_Lake_PackageConfig_decodeToml___closed__60;
x_12 = x_159;
x_13 = x_10;
goto block_155;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_158, 0);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
switch (lean_obj_tag(x_161)) {
case 0:
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_12 = x_162;
x_13 = x_10;
goto block_155;
}
case 2:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lake_Glob_decodeToml___closed__2;
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_unsigned_to_nat(1u);
x_167 = lean_mk_array(x_166, x_165);
x_168 = l_Array_append___rarg(x_10, x_167);
lean_dec(x_167);
x_169 = l_Lake_PackageConfig_decodeToml___closed__60;
x_12 = x_169;
x_13 = x_168;
goto block_155;
}
case 3:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_170 = lean_ctor_get(x_161, 0);
lean_inc(x_170);
lean_dec(x_161);
x_171 = l_Lake_Glob_decodeToml___closed__2;
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_unsigned_to_nat(1u);
x_174 = lean_mk_array(x_173, x_172);
x_175 = l_Array_append___rarg(x_10, x_174);
lean_dec(x_174);
x_176 = l_Lake_PackageConfig_decodeToml___closed__60;
x_12 = x_176;
x_13 = x_175;
goto block_155;
}
default: 
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_161);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_178 = lean_ctor_get(x_161, 1);
lean_dec(x_178);
x_179 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_161, 0);
lean_ctor_set(x_161, 1, x_179);
x_180 = lean_unsigned_to_nat(1u);
x_181 = lean_mk_array(x_180, x_161);
x_182 = l_Array_append___rarg(x_10, x_181);
lean_dec(x_181);
x_183 = l_Lake_PackageConfig_decodeToml___closed__60;
x_12 = x_183;
x_13 = x_182;
goto block_155;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_161, 0);
lean_inc(x_184);
lean_dec(x_161);
x_185 = l_Lake_Glob_decodeToml___closed__2;
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_unsigned_to_nat(1u);
x_188 = lean_mk_array(x_187, x_186);
x_189 = l_Array_append___rarg(x_10, x_188);
lean_dec(x_188);
x_190 = l_Lake_PackageConfig_decodeToml___closed__60;
x_12 = x_190;
x_13 = x_189;
goto block_155;
}
}
}
}
block_155:
{
lean_object* x_14; lean_object* x_15; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_111 = l_Lake_LeanExeConfig_decodeToml___closed__7;
lean_inc(x_1);
x_112 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_110, x_111, x_1);
if (lean_obj_tag(x_112) == 0)
{
lean_inc(x_11);
x_14 = x_11;
x_15 = x_13;
goto block_109;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
switch (lean_obj_tag(x_114)) {
case 0:
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
x_118 = l_String_toName(x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
lean_ctor_set(x_114, 1, x_119);
x_120 = lean_unsigned_to_nat(1u);
x_121 = lean_mk_array(x_120, x_114);
x_122 = l_Array_append___rarg(x_13, x_121);
lean_dec(x_121);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_122;
goto block_109;
}
else
{
lean_free_object(x_114);
lean_dec(x_116);
x_14 = x_118;
x_15 = x_13;
goto block_109;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_114, 0);
x_124 = lean_ctor_get(x_114, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_114);
x_125 = l_String_toName(x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_mk_array(x_128, x_127);
x_130 = l_Array_append___rarg(x_13, x_129);
lean_dec(x_129);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_130;
goto block_109;
}
else
{
lean_dec(x_123);
x_14 = x_125;
x_15 = x_13;
goto block_109;
}
}
}
case 2:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_131 = lean_ctor_get(x_114, 0);
lean_inc(x_131);
lean_dec(x_114);
x_132 = l_Lake_Glob_decodeToml___closed__2;
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_mk_array(x_134, x_133);
x_136 = l_Array_append___rarg(x_13, x_135);
lean_dec(x_135);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_136;
goto block_109;
}
case 3:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_137 = lean_ctor_get(x_114, 0);
lean_inc(x_137);
lean_dec(x_114);
x_138 = l_Lake_Glob_decodeToml___closed__2;
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_mk_array(x_140, x_139);
x_142 = l_Array_append___rarg(x_13, x_141);
lean_dec(x_141);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_142;
goto block_109;
}
default: 
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_114);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_114, 1);
lean_dec(x_144);
x_145 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_114, 0);
lean_ctor_set(x_114, 1, x_145);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_mk_array(x_146, x_114);
x_148 = l_Array_append___rarg(x_13, x_147);
lean_dec(x_147);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_148;
goto block_109;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_149 = lean_ctor_get(x_114, 0);
lean_inc(x_149);
lean_dec(x_114);
x_150 = l_Lake_Glob_decodeToml___closed__2;
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_mk_array(x_152, x_151);
x_154 = l_Array_append___rarg(x_13, x_153);
lean_dec(x_153);
lean_inc(x_11);
x_14 = x_11;
x_15 = x_154;
goto block_109;
}
}
}
}
block_109:
{
lean_object* x_16; lean_object* x_17; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_75 = l_Lake_PackageConfig_decodeToml___closed__5;
x_76 = 0;
x_77 = l_Lake_StrPat_decodeToml___closed__6;
lean_inc(x_11);
x_78 = l_Lean_Name_toStringWithSep(x_75, x_76, x_11, x_77);
x_79 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_80 = l_Lake_LeanExeConfig_decodeToml___closed__5;
lean_inc(x_1);
x_81 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_79, x_80, x_1);
if (lean_obj_tag(x_81) == 0)
{
x_16 = x_78;
x_17 = x_15;
goto block_74;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
switch (lean_obj_tag(x_83)) {
case 0:
{
lean_object* x_84; 
lean_dec(x_78);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_16 = x_84;
x_17 = x_15;
goto block_74;
}
case 2:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lake_Glob_decodeToml___closed__2;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_mk_array(x_88, x_87);
x_90 = l_Array_append___rarg(x_15, x_89);
lean_dec(x_89);
x_16 = x_78;
x_17 = x_90;
goto block_74;
}
case 3:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_ctor_get(x_83, 0);
lean_inc(x_91);
lean_dec(x_83);
x_92 = l_Lake_Glob_decodeToml___closed__2;
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_mk_array(x_94, x_93);
x_96 = l_Array_append___rarg(x_15, x_95);
lean_dec(x_95);
x_16 = x_78;
x_17 = x_96;
goto block_74;
}
default: 
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_83);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_83, 1);
lean_dec(x_98);
x_99 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_83, 0);
lean_ctor_set(x_83, 1, x_99);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_mk_array(x_100, x_83);
x_102 = l_Array_append___rarg(x_15, x_101);
lean_dec(x_101);
x_16 = x_78;
x_17 = x_102;
goto block_74;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_83, 0);
lean_inc(x_103);
lean_dec(x_83);
x_104 = l_Lake_Glob_decodeToml___closed__2;
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_mk_array(x_106, x_105);
x_108 = l_Array_append___rarg(x_15, x_107);
lean_dec(x_107);
x_16 = x_78;
x_17 = x_108;
goto block_74;
}
}
}
}
block_74:
{
uint8_t x_18; lean_object* x_19; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_33 = l_Lake_LeanExeConfig_decodeToml___closed__3;
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
x_24 = l_Lake_decodeLeanOptions___closed__1;
x_25 = l_Lake_LeanExeConfig_decodeToml___closed__1;
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
x_28 = l_Lake_decodeLeanOptions___closed__1;
x_29 = l_Lake_LeanExeConfig_decodeToml___closed__1;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_12 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
x_13 = lean_string_append(x_12, x_11);
lean_dec(x_11);
x_14 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
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
x_24 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
x_25 = lean_string_append(x_24, x_23);
lean_dec(x_23);
x_26 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lake_Glob_decodeToml___closed__2;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_mk_array(x_14, x_13);
x_3 = x_15;
goto block_8;
}
case 3:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
lean_dec(x_2);
x_17 = l_Lake_Glob_decodeToml___closed__2;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_mk_array(x_19, x_18);
x_3 = x_20;
goto block_8;
}
default: 
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_2);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_2, 1);
lean_dec(x_22);
x_23 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_mk_array(x_24, x_2);
x_3 = x_25;
goto block_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lake_Glob_decodeToml___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_mk_array(x_29, x_28);
x_3 = x_30;
goto block_8;
}
}
}
block_8:
{
size_t x_4; size_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_size(x_3);
x_5 = 0;
x_6 = l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__3(x_1, x_4, x_5, x_3);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_17 = l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__2(x_2, x_16);
lean_dec(x_2);
return x_17;
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
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_box(0);
x_150 = l_Lake_DependencySrc_decodeToml___closed__15;
lean_ctor_set(x_141, 1, x_150);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_141);
lean_ctor_set(x_151, 1, x_149);
x_152 = lean_array_mk(x_151);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_152);
return x_137;
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_free_object(x_141);
lean_dec(x_143);
lean_free_object(x_137);
x_153 = l_Lake_DependencySrc_decodeToml___closed__17;
lean_inc(x_1);
x_154 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__3(x_1, x_153, x_2);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
lean_dec(x_154);
x_156 = l_Lake_LeanOption_decodeToml___closed__3;
x_157 = l_Array_append___rarg(x_156, x_155);
lean_dec(x_155);
x_158 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_158;
x_10 = x_157;
goto block_134;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
lean_dec(x_154);
x_160 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_159;
x_10 = x_160;
goto block_134;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_free_object(x_141);
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_2);
x_161 = l_Lake_DependencySrc_decodeToml___closed__19;
x_162 = lean_box(0);
x_163 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_161, x_162);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
lean_free_object(x_137);
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
return x_163;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
else
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_163);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = lean_ctor_get(x_163, 0);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_168);
lean_ctor_set(x_163, 0, x_137);
return x_163;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_163, 0);
lean_inc(x_169);
lean_dec(x_163);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_169);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_137);
return x_170;
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_171 = lean_ctor_get(x_141, 0);
x_172 = lean_ctor_get(x_141, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_141);
x_173 = l_Lake_DependencySrc_decodeToml___closed__13;
x_174 = lean_string_dec_eq(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = l_Lake_DependencySrc_decodeToml___closed__14;
x_176 = lean_string_dec_eq(x_172, x_175);
lean_dec(x_172);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_box(0);
x_178 = l_Lake_DependencySrc_decodeToml___closed__15;
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_171);
lean_ctor_set(x_179, 1, x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_177);
x_181 = lean_array_mk(x_180);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_181);
return x_137;
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_171);
lean_free_object(x_137);
x_182 = l_Lake_DependencySrc_decodeToml___closed__17;
lean_inc(x_1);
x_183 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__3(x_1, x_182, x_2);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l_Lake_LeanOption_decodeToml___closed__3;
x_186 = l_Array_append___rarg(x_185, x_184);
lean_dec(x_184);
x_187 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_187;
x_10 = x_186;
goto block_134;
}
else
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_183, 0);
lean_inc(x_188);
lean_dec(x_183);
x_189 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_188;
x_10 = x_189;
goto block_134;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_2);
x_190 = l_Lake_DependencySrc_decodeToml___closed__19;
x_191 = lean_box(0);
x_192 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_190, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_free_object(x_137);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 x_197 = x_192;
} else {
 lean_dec_ref(x_192);
 x_197 = lean_box(0);
}
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_196);
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_137);
return x_198;
}
}
}
}
case 2:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_2);
lean_dec(x_1);
x_199 = lean_ctor_get(x_141, 0);
lean_inc(x_199);
lean_dec(x_141);
x_200 = l_Lake_Glob_decodeToml___closed__2;
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_unsigned_to_nat(1u);
x_203 = lean_mk_array(x_202, x_201);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_203);
return x_137;
}
case 3:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_2);
lean_dec(x_1);
x_204 = lean_ctor_get(x_141, 0);
lean_inc(x_204);
lean_dec(x_141);
x_205 = l_Lake_Glob_decodeToml___closed__2;
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_mk_array(x_207, x_206);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_208);
return x_137;
}
default: 
{
uint8_t x_209; 
lean_dec(x_2);
lean_dec(x_1);
x_209 = !lean_is_exclusive(x_141);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_141, 1);
lean_dec(x_210);
x_211 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_141, 0);
lean_ctor_set(x_141, 1, x_211);
x_212 = lean_unsigned_to_nat(1u);
x_213 = lean_mk_array(x_212, x_141);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_213);
return x_137;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_214 = lean_ctor_get(x_141, 0);
lean_inc(x_214);
lean_dec(x_141);
x_215 = l_Lake_Glob_decodeToml___closed__2;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_unsigned_to_nat(1u);
x_218 = lean_mk_array(x_217, x_216);
lean_ctor_set_tag(x_137, 0);
lean_ctor_set(x_137, 0, x_218);
return x_137;
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_137, 0);
lean_inc(x_219);
lean_dec(x_137);
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
switch (lean_obj_tag(x_220)) {
case 0:
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = l_Lake_DependencySrc_decodeToml___closed__13;
x_225 = lean_string_dec_eq(x_222, x_224);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = l_Lake_DependencySrc_decodeToml___closed__14;
x_227 = lean_string_dec_eq(x_222, x_226);
lean_dec(x_222);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_2);
lean_dec(x_1);
x_228 = lean_box(0);
x_229 = l_Lake_DependencySrc_decodeToml___closed__15;
if (lean_is_scalar(x_223)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_223;
}
lean_ctor_set(x_230, 0, x_221);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_228);
x_232 = lean_array_mk(x_231);
x_233 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_223);
lean_dec(x_221);
x_234 = l_Lake_DependencySrc_decodeToml___closed__17;
lean_inc(x_1);
x_235 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__3(x_1, x_234, x_2);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec(x_235);
x_237 = l_Lake_LeanOption_decodeToml___closed__3;
x_238 = l_Array_append___rarg(x_237, x_236);
lean_dec(x_236);
x_239 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_239;
x_10 = x_238;
goto block_134;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_235, 0);
lean_inc(x_240);
lean_dec(x_235);
x_241 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_240;
x_10 = x_241;
goto block_134;
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_2);
x_242 = l_Lake_DependencySrc_decodeToml___closed__19;
x_243 = lean_box(0);
x_244 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_242, x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_246 = x_244;
} else {
 lean_dec_ref(x_244);
 x_246 = lean_box(0);
}
if (lean_is_scalar(x_246)) {
 x_247 = lean_alloc_ctor(0, 1, 0);
} else {
 x_247 = x_246;
}
lean_ctor_set(x_247, 0, x_245);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_244, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 x_249 = x_244;
} else {
 lean_dec_ref(x_244);
 x_249 = lean_box(0);
}
x_250 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_250, 0, x_248);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(1, 1, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
return x_251;
}
}
}
case 2:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_2);
lean_dec(x_1);
x_252 = lean_ctor_get(x_220, 0);
lean_inc(x_252);
lean_dec(x_220);
x_253 = l_Lake_Glob_decodeToml___closed__2;
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_mk_array(x_255, x_254);
x_257 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
case 3:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_2);
lean_dec(x_1);
x_258 = lean_ctor_get(x_220, 0);
lean_inc(x_258);
lean_dec(x_220);
x_259 = l_Lake_Glob_decodeToml___closed__2;
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = lean_unsigned_to_nat(1u);
x_262 = lean_mk_array(x_261, x_260);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_262);
return x_263;
}
default: 
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_2);
lean_dec(x_1);
x_264 = lean_ctor_get(x_220, 0);
lean_inc(x_264);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_265 = x_220;
} else {
 lean_dec_ref(x_220);
 x_265 = lean_box(0);
}
x_266 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_265)) {
 x_267 = lean_alloc_ctor(0, 2, 0);
} else {
 x_267 = x_265;
 lean_ctor_set_tag(x_267, 0);
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_unsigned_to_nat(1u);
x_269 = lean_mk_array(x_268, x_267);
x_270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_270, 0, x_269);
return x_270;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
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
x_1 = lean_mk_string_unchecked("scope", 5, 5);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("source", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Dependency_decodeToml___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected string or table", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_Dependency_decodeToml___closed__10() {
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
x_906 = l_Lake_LeanOption_decodeToml___closed__10;
lean_inc(x_1);
x_907 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__3(x_1, x_906, x_2);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
lean_dec(x_907);
x_909 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_913 = l_Lake_LeanOption_decodeToml___closed__3;
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
x_795 = l_Lake_Dependency_decodeToml___closed__10;
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
x_154 = l_Lake_Dependency_decodeToml___closed__5;
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
x_98 = l_Lake_PackageConfig_decodeToml___closed__29;
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
x_328 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_329 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_327, x_328, x_1);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_397; lean_object* x_398; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_416 = l_Lake_PackageConfig_decodeToml___closed__29;
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
x_272 = l_Lake_PackageConfig_decodeToml___closed__29;
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
x_517 = l_Lake_Dependency_decodeToml___closed__6;
lean_inc(x_1);
x_518 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_516, x_517, x_1);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = l_Lake_Dependency_decodeToml___closed__8;
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
x_697 = l_Lake_Dependency_decodeToml___closed__9;
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
x_702 = l_Lake_Dependency_decodeToml___closed__9;
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
x_772 = l_Lake_Toml_Table_decode___at_Lake_PackageConfig_decodeToml___spec__3(x_707, x_771, x_706);
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
x_779 = l_Lake_Dependency_decodeToml___closed__9;
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
x_783 = l_Lake_Dependency_decodeToml___closed__9;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_loadTomlConfig___spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_stringToLegalOrSimpleName(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9(lean_object* x_1) {
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
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__12(lean_object* x_1) {
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
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__13(x_1, x_8, x_9, x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__14(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__16(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__15(lean_object* x_1) {
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
x_10 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__16(x_1, x_8, x_9, x_4);
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_StrPat_decodeToml___closed__6;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_loadTomlConfig___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_3 = l_Lake_PackageConfig_decodeToml___closed__7;
x_4 = lean_box(0);
x_5 = l_Lake_LeanOption_decodeToml___closed__3;
x_6 = 0;
x_7 = l_Lake_PackageConfig_decodeToml___closed__31;
x_8 = l_Lake_loadTomlConfig___closed__10;
x_9 = lean_alloc_ctor(0, 29, 3);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_1);
lean_ctor_set(x_9, 4, x_5);
lean_ctor_set(x_9, 5, x_5);
lean_ctor_set(x_9, 6, x_5);
lean_ctor_set(x_9, 7, x_2);
lean_ctor_set(x_9, 8, x_2);
lean_ctor_set(x_9, 9, x_2);
lean_ctor_set(x_9, 10, x_2);
lean_ctor_set(x_9, 11, x_2);
lean_ctor_set(x_9, 12, x_2);
lean_ctor_set(x_9, 13, x_1);
lean_ctor_set(x_9, 14, x_1);
lean_ctor_set(x_9, 15, x_1);
lean_ctor_set(x_9, 16, x_2);
lean_ctor_set(x_9, 17, x_2);
lean_ctor_set(x_9, 18, x_5);
lean_ctor_set(x_9, 19, x_2);
lean_ctor_set(x_9, 20, x_5);
lean_ctor_set(x_9, 21, x_7);
lean_ctor_set(x_9, 22, x_8);
lean_ctor_set(x_9, 23, x_2);
lean_ctor_set(x_9, 24, x_5);
lean_ctor_set(x_9, 25, x_2);
lean_ctor_set(x_9, 26, x_2);
lean_ctor_set(x_9, 27, x_5);
lean_ctor_set(x_9, 28, x_2);
lean_ctor_set_uint8(x_9, sizeof(void*)*29, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*29 + 1, x_6);
lean_ctor_set_uint8(x_9, sizeof(void*)*29 + 2, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_680 = lean_ctor_get(x_1, 2);
lean_inc(x_680);
x_681 = lean_ctor_get(x_1, 3);
lean_inc(x_681);
x_682 = l_System_FilePath_join(x_680, x_681);
lean_dec(x_681);
x_683 = lean_ctor_get(x_1, 4);
lean_inc(x_683);
x_684 = l_System_FilePath_join(x_682, x_683);
lean_dec(x_683);
x_685 = l_IO_FS_readFile(x_684, x_3);
lean_dec(x_684);
if (lean_obj_tag(x_685) == 0)
{
uint8_t x_686; 
x_686 = !lean_is_exclusive(x_685);
if (x_686 == 0)
{
lean_object* x_687; 
x_687 = lean_ctor_get(x_685, 1);
lean_ctor_set(x_685, 1, x_2);
x_4 = x_685;
x_5 = x_687;
goto block_679;
}
else
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_688 = lean_ctor_get(x_685, 0);
x_689 = lean_ctor_get(x_685, 1);
lean_inc(x_689);
lean_inc(x_688);
lean_dec(x_685);
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_688);
lean_ctor_set(x_690, 1, x_2);
x_4 = x_690;
x_5 = x_689;
goto block_679;
}
}
else
{
uint8_t x_691; 
x_691 = !lean_is_exclusive(x_685);
if (x_691 == 0)
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; uint8_t x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_692 = lean_ctor_get(x_685, 0);
x_693 = lean_ctor_get(x_685, 1);
x_694 = lean_io_error_to_string(x_692);
x_695 = 3;
x_696 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set_uint8(x_696, sizeof(void*)*1, x_695);
x_697 = lean_array_get_size(x_2);
x_698 = lean_array_push(x_2, x_696);
lean_ctor_set(x_685, 1, x_698);
lean_ctor_set(x_685, 0, x_697);
x_4 = x_685;
x_5 = x_693;
goto block_679;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; 
x_699 = lean_ctor_get(x_685, 0);
x_700 = lean_ctor_get(x_685, 1);
lean_inc(x_700);
lean_inc(x_699);
lean_dec(x_685);
x_701 = lean_io_error_to_string(x_699);
x_702 = 3;
x_703 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set_uint8(x_703, sizeof(void*)*1, x_702);
x_704 = lean_array_get_size(x_2);
x_705 = lean_array_push(x_2, x_703);
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
x_4 = x_706;
x_5 = x_700;
goto block_679;
}
}
block_679:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_363; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Parser_mkInputContext(x_7, x_8, x_9);
lean_inc(x_10);
x_363 = l_Lake_Toml_loadToml(x_10, x_5);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 1);
lean_inc(x_365);
lean_dec(x_363);
x_366 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_4, 0, x_366);
x_11 = x_4;
x_12 = x_365;
goto block_362;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_363, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_363, 1);
lean_inc(x_368);
lean_dec(x_363);
x_369 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_4, 0, x_369);
x_11 = x_4;
x_12 = x_368;
goto block_362;
}
block_362:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_15 = x_11;
} else {
 lean_dec_ref(x_11);
 x_15 = lean_box(0);
}
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_1);
x_47 = lean_ctor_get(x_13, 0);
lean_inc(x_47);
lean_dec(x_13);
x_48 = lean_array_get_size(x_14);
x_49 = l_Lake_loadTomlConfig___closed__1;
x_50 = l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(x_47, x_49, x_14, x_12);
lean_dec(x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_50);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 0, x_48);
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_dec(x_51);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_50, 0, x_57);
return x_50;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_60 = x_51;
} else {
 lean_dec_ref(x_51);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
 lean_ctor_set_tag(x_61, 1);
}
lean_ctor_set(x_61, 0, x_48);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_50);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_50, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_51);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_51, 0);
lean_dec(x_66);
lean_ctor_set(x_51, 0, x_48);
return x_50;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
lean_dec(x_51);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_48);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_50, 0, x_68);
return x_50;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_50, 1);
lean_inc(x_69);
lean_dec(x_50);
x_70 = lean_ctor_get(x_51, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_71 = x_51;
} else {
 lean_dec_ref(x_51);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_48);
lean_ctor_set(x_72, 1, x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_48);
x_74 = !lean_is_exclusive(x_50);
if (x_74 == 0)
{
return x_50;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_50, 0);
x_76 = lean_ctor_get(x_50, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_50);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_354; lean_object* x_355; 
x_78 = lean_ctor_get(x_13, 0);
lean_inc(x_78);
lean_dec(x_13);
x_354 = lean_box(0);
lean_inc(x_78);
x_355 = l_Lake_PackageConfig_decodeToml(x_78, x_354);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
lean_dec(x_355);
x_357 = l_Lake_decodeLeanOptions___closed__1;
x_358 = l_Array_append___rarg(x_357, x_356);
lean_dec(x_356);
x_359 = l_Lake_loadTomlConfig___closed__11;
x_79 = x_359;
x_80 = x_358;
goto block_353;
}
else
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_355, 0);
lean_inc(x_360);
lean_dec(x_355);
x_361 = l_Lake_decodeLeanOptions___closed__1;
x_79 = x_360;
x_80 = x_361;
goto block_353;
}
block_353:
{
lean_object* x_81; lean_object* x_82; lean_object* x_287; lean_object* x_288; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_300 = l_Lake_loadTomlConfig___closed__9;
lean_inc(x_78);
x_301 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_299, x_300, x_78);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; 
x_302 = l_Lake_decodeLeanOptions___closed__1;
x_287 = x_302;
x_288 = x_80;
goto block_298;
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_301, 0);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
lean_dec(x_303);
switch (lean_obj_tag(x_304)) {
case 0:
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_306 = lean_ctor_get(x_304, 1);
lean_dec(x_306);
x_307 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_304, 1, x_307);
x_308 = lean_unsigned_to_nat(1u);
x_309 = lean_mk_array(x_308, x_304);
x_310 = l_Array_append___rarg(x_80, x_309);
lean_dec(x_309);
x_311 = l_Lake_decodeLeanOptions___closed__1;
x_287 = x_311;
x_288 = x_310;
goto block_298;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_312 = lean_ctor_get(x_304, 0);
lean_inc(x_312);
lean_dec(x_304);
x_313 = l_Lake_LeanConfig_decodeToml___closed__5;
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_unsigned_to_nat(1u);
x_316 = lean_mk_array(x_315, x_314);
x_317 = l_Array_append___rarg(x_80, x_316);
lean_dec(x_316);
x_318 = l_Lake_decodeLeanOptions___closed__1;
x_287 = x_318;
x_288 = x_317;
goto block_298;
}
}
case 2:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_319 = lean_ctor_get(x_304, 0);
lean_inc(x_319);
lean_dec(x_304);
x_320 = l_Lake_LeanConfig_decodeToml___closed__5;
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_319);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_unsigned_to_nat(1u);
x_323 = lean_mk_array(x_322, x_321);
x_324 = l_Array_append___rarg(x_80, x_323);
lean_dec(x_323);
x_325 = l_Lake_decodeLeanOptions___closed__1;
x_287 = x_325;
x_288 = x_324;
goto block_298;
}
case 3:
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_326 = lean_ctor_get(x_304, 0);
lean_inc(x_326);
lean_dec(x_304);
x_327 = l_Lake_LeanConfig_decodeToml___closed__5;
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_unsigned_to_nat(1u);
x_330 = lean_mk_array(x_329, x_328);
x_331 = l_Array_append___rarg(x_80, x_330);
lean_dec(x_330);
x_332 = l_Lake_decodeLeanOptions___closed__1;
x_287 = x_332;
x_288 = x_331;
goto block_298;
}
case 5:
{
lean_object* x_333; lean_object* x_334; 
x_333 = lean_ctor_get(x_304, 1);
lean_inc(x_333);
lean_dec(x_304);
x_334 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__15(x_333);
lean_dec(x_333);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
lean_dec(x_334);
x_336 = l_Array_append___rarg(x_80, x_335);
lean_dec(x_335);
x_337 = l_Lake_decodeLeanOptions___closed__1;
x_287 = x_337;
x_288 = x_336;
goto block_298;
}
else
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_334, 0);
lean_inc(x_338);
lean_dec(x_334);
x_287 = x_338;
x_288 = x_80;
goto block_298;
}
}
default: 
{
uint8_t x_339; 
x_339 = !lean_is_exclusive(x_304);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_340 = lean_ctor_get(x_304, 1);
lean_dec(x_340);
x_341 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_304, 0);
lean_ctor_set(x_304, 1, x_341);
x_342 = lean_unsigned_to_nat(1u);
x_343 = lean_mk_array(x_342, x_304);
x_344 = l_Array_append___rarg(x_80, x_343);
lean_dec(x_343);
x_345 = l_Lake_decodeLeanOptions___closed__1;
x_287 = x_345;
x_288 = x_344;
goto block_298;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_346 = lean_ctor_get(x_304, 0);
lean_inc(x_346);
lean_dec(x_304);
x_347 = l_Lake_LeanConfig_decodeToml___closed__5;
x_348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_unsigned_to_nat(1u);
x_350 = lean_mk_array(x_349, x_348);
x_351 = l_Array_append___rarg(x_80, x_350);
lean_dec(x_350);
x_352 = l_Lake_decodeLeanOptions___closed__1;
x_287 = x_352;
x_288 = x_351;
goto block_298;
}
}
}
}
block_286:
{
lean_object* x_83; lean_object* x_84; lean_object* x_220; lean_object* x_221; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_233 = l_Lake_loadTomlConfig___closed__7;
lean_inc(x_78);
x_234 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_232, x_233, x_78);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; 
x_235 = l_Lake_decodeLeanOptions___closed__1;
x_220 = x_235;
x_221 = x_82;
goto block_231;
}
else
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
lean_dec(x_234);
x_237 = lean_ctor_get(x_236, 1);
lean_inc(x_237);
lean_dec(x_236);
switch (lean_obj_tag(x_237)) {
case 0:
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_237, 1);
lean_dec(x_239);
x_240 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_237, 1, x_240);
x_241 = lean_unsigned_to_nat(1u);
x_242 = lean_mk_array(x_241, x_237);
x_243 = l_Array_append___rarg(x_82, x_242);
lean_dec(x_242);
x_244 = l_Lake_decodeLeanOptions___closed__1;
x_220 = x_244;
x_221 = x_243;
goto block_231;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_245 = lean_ctor_get(x_237, 0);
lean_inc(x_245);
lean_dec(x_237);
x_246 = l_Lake_LeanConfig_decodeToml___closed__5;
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_mk_array(x_248, x_247);
x_250 = l_Array_append___rarg(x_82, x_249);
lean_dec(x_249);
x_251 = l_Lake_decodeLeanOptions___closed__1;
x_220 = x_251;
x_221 = x_250;
goto block_231;
}
}
case 2:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_252 = lean_ctor_get(x_237, 0);
lean_inc(x_252);
lean_dec(x_237);
x_253 = l_Lake_LeanConfig_decodeToml___closed__5;
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = lean_unsigned_to_nat(1u);
x_256 = lean_mk_array(x_255, x_254);
x_257 = l_Array_append___rarg(x_82, x_256);
lean_dec(x_256);
x_258 = l_Lake_decodeLeanOptions___closed__1;
x_220 = x_258;
x_221 = x_257;
goto block_231;
}
case 3:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_259 = lean_ctor_get(x_237, 0);
lean_inc(x_259);
lean_dec(x_237);
x_260 = l_Lake_LeanConfig_decodeToml___closed__5;
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
x_262 = lean_unsigned_to_nat(1u);
x_263 = lean_mk_array(x_262, x_261);
x_264 = l_Array_append___rarg(x_82, x_263);
lean_dec(x_263);
x_265 = l_Lake_decodeLeanOptions___closed__1;
x_220 = x_265;
x_221 = x_264;
goto block_231;
}
case 5:
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_237, 1);
lean_inc(x_266);
lean_dec(x_237);
x_267 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__12(x_266);
lean_dec(x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec(x_267);
x_269 = l_Array_append___rarg(x_82, x_268);
lean_dec(x_268);
x_270 = l_Lake_decodeLeanOptions___closed__1;
x_220 = x_270;
x_221 = x_269;
goto block_231;
}
else
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_267, 0);
lean_inc(x_271);
lean_dec(x_267);
x_220 = x_271;
x_221 = x_82;
goto block_231;
}
}
default: 
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_237);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_237, 1);
lean_dec(x_273);
x_274 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_237, 0);
lean_ctor_set(x_237, 1, x_274);
x_275 = lean_unsigned_to_nat(1u);
x_276 = lean_mk_array(x_275, x_237);
x_277 = l_Array_append___rarg(x_82, x_276);
lean_dec(x_276);
x_278 = l_Lake_decodeLeanOptions___closed__1;
x_220 = x_278;
x_221 = x_277;
goto block_231;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_279 = lean_ctor_get(x_237, 0);
lean_inc(x_279);
lean_dec(x_237);
x_280 = l_Lake_LeanConfig_decodeToml___closed__5;
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_282 = lean_unsigned_to_nat(1u);
x_283 = lean_mk_array(x_282, x_281);
x_284 = l_Array_append___rarg(x_82, x_283);
lean_dec(x_283);
x_285 = l_Lake_decodeLeanOptions___closed__1;
x_220 = x_285;
x_221 = x_284;
goto block_231;
}
}
}
}
block_219:
{
lean_object* x_85; lean_object* x_86; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_166 = l_Lake_loadTomlConfig___closed__5;
lean_inc(x_78);
x_167 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_165, x_166, x_78);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; 
x_168 = l_Lake_decodeLeanOptions___closed__1;
x_85 = x_168;
x_86 = x_84;
goto block_164;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_167, 0);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
switch (lean_obj_tag(x_170)) {
case 0:
{
uint8_t x_171; 
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_172 = lean_ctor_get(x_170, 1);
lean_dec(x_172);
x_173 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_170, 1, x_173);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_mk_array(x_174, x_170);
x_176 = l_Array_append___rarg(x_84, x_175);
lean_dec(x_175);
x_177 = l_Lake_decodeLeanOptions___closed__1;
x_85 = x_177;
x_86 = x_176;
goto block_164;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_ctor_get(x_170, 0);
lean_inc(x_178);
lean_dec(x_170);
x_179 = l_Lake_LeanConfig_decodeToml___closed__5;
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_unsigned_to_nat(1u);
x_182 = lean_mk_array(x_181, x_180);
x_183 = l_Array_append___rarg(x_84, x_182);
lean_dec(x_182);
x_184 = l_Lake_decodeLeanOptions___closed__1;
x_85 = x_184;
x_86 = x_183;
goto block_164;
}
}
case 2:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_185 = lean_ctor_get(x_170, 0);
lean_inc(x_185);
lean_dec(x_170);
x_186 = l_Lake_LeanConfig_decodeToml___closed__5;
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_mk_array(x_188, x_187);
x_190 = l_Array_append___rarg(x_84, x_189);
lean_dec(x_189);
x_191 = l_Lake_decodeLeanOptions___closed__1;
x_85 = x_191;
x_86 = x_190;
goto block_164;
}
case 3:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_192 = lean_ctor_get(x_170, 0);
lean_inc(x_192);
lean_dec(x_170);
x_193 = l_Lake_LeanConfig_decodeToml___closed__5;
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_unsigned_to_nat(1u);
x_196 = lean_mk_array(x_195, x_194);
x_197 = l_Array_append___rarg(x_84, x_196);
lean_dec(x_196);
x_198 = l_Lake_decodeLeanOptions___closed__1;
x_85 = x_198;
x_86 = x_197;
goto block_164;
}
case 5:
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_170, 1);
lean_inc(x_199);
lean_dec(x_170);
x_200 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_199);
lean_dec(x_199);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_202 = l_Array_append___rarg(x_84, x_201);
lean_dec(x_201);
x_203 = l_Lake_decodeLeanOptions___closed__1;
x_85 = x_203;
x_86 = x_202;
goto block_164;
}
else
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_200, 0);
lean_inc(x_204);
lean_dec(x_200);
x_85 = x_204;
x_86 = x_84;
goto block_164;
}
}
default: 
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_170);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_206 = lean_ctor_get(x_170, 1);
lean_dec(x_206);
x_207 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_170, 0);
lean_ctor_set(x_170, 1, x_207);
x_208 = lean_unsigned_to_nat(1u);
x_209 = lean_mk_array(x_208, x_170);
x_210 = l_Array_append___rarg(x_84, x_209);
lean_dec(x_209);
x_211 = l_Lake_decodeLeanOptions___closed__1;
x_85 = x_211;
x_86 = x_210;
goto block_164;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_212 = lean_ctor_get(x_170, 0);
lean_inc(x_212);
lean_dec(x_170);
x_213 = l_Lake_LeanConfig_decodeToml___closed__5;
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
x_215 = lean_unsigned_to_nat(1u);
x_216 = lean_mk_array(x_215, x_214);
x_217 = l_Array_append___rarg(x_84, x_216);
lean_dec(x_216);
x_218 = l_Lake_decodeLeanOptions___closed__1;
x_85 = x_218;
x_86 = x_217;
goto block_164;
}
}
}
}
block_164:
{
size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_87 = lean_array_size(x_85);
x_88 = 0;
x_89 = l_Array_mapMUnsafe_map___at_Lake_loadTomlConfig___spec__8(x_87, x_88, x_85);
x_110 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_111 = l_Lake_loadTomlConfig___closed__3;
x_112 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_110, x_111, x_78);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; 
x_113 = l_Lake_decodeLeanOptions___closed__1;
x_90 = x_113;
x_91 = x_86;
goto block_109;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
switch (lean_obj_tag(x_115)) {
case 0:
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_117 = lean_ctor_get(x_115, 1);
lean_dec(x_117);
x_118 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_115, 1, x_118);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_mk_array(x_119, x_115);
x_121 = l_Array_append___rarg(x_86, x_120);
lean_dec(x_120);
x_122 = l_Lake_decodeLeanOptions___closed__1;
x_90 = x_122;
x_91 = x_121;
goto block_109;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_123 = lean_ctor_get(x_115, 0);
lean_inc(x_123);
lean_dec(x_115);
x_124 = l_Lake_LeanConfig_decodeToml___closed__5;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_mk_array(x_126, x_125);
x_128 = l_Array_append___rarg(x_86, x_127);
lean_dec(x_127);
x_129 = l_Lake_decodeLeanOptions___closed__1;
x_90 = x_129;
x_91 = x_128;
goto block_109;
}
}
case 2:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_130 = lean_ctor_get(x_115, 0);
lean_inc(x_130);
lean_dec(x_115);
x_131 = l_Lake_LeanConfig_decodeToml___closed__5;
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_mk_array(x_133, x_132);
x_135 = l_Array_append___rarg(x_86, x_134);
lean_dec(x_134);
x_136 = l_Lake_decodeLeanOptions___closed__1;
x_90 = x_136;
x_91 = x_135;
goto block_109;
}
case 3:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_137 = lean_ctor_get(x_115, 0);
lean_inc(x_137);
lean_dec(x_115);
x_138 = l_Lake_LeanConfig_decodeToml___closed__5;
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_mk_array(x_140, x_139);
x_142 = l_Array_append___rarg(x_86, x_141);
lean_dec(x_141);
x_143 = l_Lake_decodeLeanOptions___closed__1;
x_90 = x_143;
x_91 = x_142;
goto block_109;
}
case 5:
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_115, 1);
lean_inc(x_144);
lean_dec(x_115);
x_145 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9(x_144);
lean_dec(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
lean_dec(x_145);
x_147 = l_Array_append___rarg(x_86, x_146);
lean_dec(x_146);
x_148 = l_Lake_decodeLeanOptions___closed__1;
x_90 = x_148;
x_91 = x_147;
goto block_109;
}
else
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
lean_dec(x_145);
x_90 = x_149;
x_91 = x_86;
goto block_109;
}
}
default: 
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_115);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_151 = lean_ctor_get(x_115, 1);
lean_dec(x_151);
x_152 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_115, 0);
lean_ctor_set(x_115, 1, x_152);
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_mk_array(x_153, x_115);
x_155 = l_Array_append___rarg(x_86, x_154);
lean_dec(x_154);
x_156 = l_Lake_decodeLeanOptions___closed__1;
x_90 = x_156;
x_91 = x_155;
goto block_109;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_157 = lean_ctor_get(x_115, 0);
lean_inc(x_157);
lean_dec(x_115);
x_158 = l_Lake_LeanConfig_decodeToml___closed__5;
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_mk_array(x_160, x_159);
x_162 = l_Array_append___rarg(x_86, x_161);
lean_dec(x_161);
x_163 = l_Lake_decodeLeanOptions___closed__1;
x_90 = x_163;
x_91 = x_162;
goto block_109;
}
}
}
}
block_109:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_92 = lean_ctor_get(x_1, 2);
lean_inc(x_92);
x_93 = lean_ctor_get(x_1, 3);
lean_inc(x_93);
x_94 = l_System_FilePath_join(x_92, x_93);
x_95 = lean_ctor_get(x_79, 3);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 7);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 8);
lean_inc(x_97);
lean_dec(x_1);
x_98 = lean_box(0);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_79, 17);
lean_inc(x_99);
x_100 = lean_ctor_get(x_79, 19);
lean_inc(x_100);
x_101 = l_Lake_defaultManifestFile;
x_102 = l_Lake_decodeLeanOptions___closed__1;
x_103 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_103, 0, x_94);
lean_ctor_set(x_103, 1, x_93);
lean_ctor_set(x_103, 2, x_79);
lean_ctor_set(x_103, 3, x_8);
lean_ctor_set(x_103, 4, x_101);
lean_ctor_set(x_103, 5, x_96);
lean_ctor_set(x_103, 6, x_97);
lean_ctor_set(x_103, 7, x_90);
lean_ctor_set(x_103, 8, x_81);
lean_ctor_set(x_103, 9, x_83);
lean_ctor_set(x_103, 10, x_98);
lean_ctor_set(x_103, 11, x_98);
lean_ctor_set(x_103, 12, x_89);
lean_ctor_set(x_103, 13, x_98);
lean_ctor_set(x_103, 14, x_102);
lean_ctor_set(x_103, 15, x_102);
lean_ctor_set(x_103, 16, x_99);
lean_ctor_set(x_103, 17, x_100);
x_16 = x_103;
x_17 = x_91;
goto block_46;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_79, 17);
lean_inc(x_104);
x_105 = lean_ctor_get(x_79, 19);
lean_inc(x_105);
x_106 = lean_ctor_get(x_95, 0);
lean_inc(x_106);
lean_dec(x_95);
x_107 = l_Lake_decodeLeanOptions___closed__1;
x_108 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_108, 0, x_94);
lean_ctor_set(x_108, 1, x_93);
lean_ctor_set(x_108, 2, x_79);
lean_ctor_set(x_108, 3, x_8);
lean_ctor_set(x_108, 4, x_106);
lean_ctor_set(x_108, 5, x_96);
lean_ctor_set(x_108, 6, x_97);
lean_ctor_set(x_108, 7, x_90);
lean_ctor_set(x_108, 8, x_81);
lean_ctor_set(x_108, 9, x_83);
lean_ctor_set(x_108, 10, x_98);
lean_ctor_set(x_108, 11, x_98);
lean_ctor_set(x_108, 12, x_89);
lean_ctor_set(x_108, 13, x_98);
lean_ctor_set(x_108, 14, x_107);
lean_ctor_set(x_108, 15, x_107);
lean_ctor_set(x_108, 16, x_104);
lean_ctor_set(x_108, 17, x_105);
x_16 = x_108;
x_17 = x_91;
goto block_46;
}
}
}
}
block_231:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_222 = lean_array_get_size(x_220);
x_223 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_224 = l_Lake_RBArray_mkEmpty___rarg(x_223, x_222);
x_225 = lean_unsigned_to_nat(0u);
x_226 = lean_nat_dec_lt(x_225, x_222);
if (x_226 == 0)
{
lean_dec(x_222);
lean_dec(x_220);
x_83 = x_224;
x_84 = x_221;
goto block_219;
}
else
{
uint8_t x_227; 
x_227 = lean_nat_dec_le(x_222, x_222);
if (x_227 == 0)
{
lean_dec(x_222);
lean_dec(x_220);
x_83 = x_224;
x_84 = x_221;
goto block_219;
}
else
{
size_t x_228; size_t x_229; lean_object* x_230; 
x_228 = 0;
x_229 = lean_usize_of_nat(x_222);
lean_dec(x_222);
x_230 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__11(x_220, x_228, x_229, x_224);
lean_dec(x_220);
x_83 = x_230;
x_84 = x_221;
goto block_219;
}
}
}
}
block_298:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; 
x_289 = lean_array_get_size(x_287);
x_290 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_291 = l_Lake_RBArray_mkEmpty___rarg(x_290, x_289);
x_292 = lean_unsigned_to_nat(0u);
x_293 = lean_nat_dec_lt(x_292, x_289);
if (x_293 == 0)
{
lean_dec(x_289);
lean_dec(x_287);
x_81 = x_291;
x_82 = x_288;
goto block_286;
}
else
{
uint8_t x_294; 
x_294 = lean_nat_dec_le(x_289, x_289);
if (x_294 == 0)
{
lean_dec(x_289);
lean_dec(x_287);
x_81 = x_291;
x_82 = x_288;
goto block_286;
}
else
{
size_t x_295; size_t x_296; lean_object* x_297; 
x_295 = 0;
x_296 = lean_usize_of_nat(x_289);
lean_dec(x_289);
x_297 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__14(x_287, x_295, x_296, x_291);
lean_dec(x_287);
x_81 = x_297;
x_82 = x_288;
goto block_286;
}
}
}
}
}
block_46:
{
uint8_t x_18; 
x_18 = l_Array_isEmpty___rarg(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_dec(x_16);
x_19 = lean_array_get_size(x_17);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_lt(x_20, x_19);
x_22 = lean_array_get_size(x_14);
if (x_21 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_10);
if (lean_is_scalar(x_15)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_15;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_19, x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_10);
if (lean_is_scalar(x_15)) {
 x_26 = lean_alloc_ctor(1, 2, 0);
} else {
 x_26 = x_15;
 lean_ctor_set_tag(x_26, 1);
}
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_12);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_15);
x_28 = 0;
x_29 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_30 = lean_box(0);
x_31 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1(x_10, x_17, x_28, x_29, x_30, x_14, x_12);
lean_dec(x_17);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_22);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_22);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_31, 0, x_37);
return x_31;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_31, 0);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_31);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_41;
 lean_ctor_set_tag(x_42, 1);
}
lean_ctor_set(x_42, 0, x_22);
lean_ctor_set(x_42, 1, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_17);
lean_dec(x_10);
if (lean_is_scalar(x_15)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_15;
}
lean_ctor_set(x_44, 0, x_16);
lean_ctor_set(x_44, 1, x_14);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_12);
return x_45;
}
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_664; 
x_370 = lean_ctor_get(x_4, 0);
x_371 = lean_ctor_get(x_4, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_4);
x_372 = lean_ctor_get(x_1, 4);
lean_inc(x_372);
x_373 = 1;
lean_inc(x_372);
x_374 = l_Lean_Parser_mkInputContext(x_370, x_372, x_373);
lean_inc(x_374);
x_664 = l_Lake_Toml_loadToml(x_374, x_5);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_667 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_667, 0, x_665);
x_668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_371);
x_375 = x_668;
x_376 = x_666;
goto block_663;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_669 = lean_ctor_get(x_664, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_664, 1);
lean_inc(x_670);
lean_dec(x_664);
x_671 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_671, 0, x_669);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_371);
x_375 = x_672;
x_376 = x_670;
goto block_663;
}
block_663:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_377 = lean_ctor_get(x_375, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_375, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_379 = x_375;
} else {
 lean_dec_ref(x_375);
 x_379 = lean_box(0);
}
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_379);
lean_dec(x_374);
lean_dec(x_372);
lean_dec(x_1);
x_406 = lean_ctor_get(x_377, 0);
lean_inc(x_406);
lean_dec(x_377);
x_407 = lean_array_get_size(x_378);
x_408 = l_Lake_loadTomlConfig___closed__1;
x_409 = l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(x_406, x_408, x_378, x_376);
lean_dec(x_406);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_412 = x_409;
} else {
 lean_dec_ref(x_409);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_410, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_414 = x_410;
} else {
 lean_dec_ref(x_410);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_414;
 lean_ctor_set_tag(x_415, 1);
}
lean_ctor_set(x_415, 0, x_407);
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
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_417 = lean_ctor_get(x_409, 1);
lean_inc(x_417);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_418 = x_409;
} else {
 lean_dec_ref(x_409);
 x_418 = lean_box(0);
}
x_419 = lean_ctor_get(x_410, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_420 = x_410;
} else {
 lean_dec_ref(x_410);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_407);
lean_ctor_set(x_421, 1, x_419);
if (lean_is_scalar(x_418)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_418;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_417);
return x_422;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_407);
x_423 = lean_ctor_get(x_409, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_409, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_425 = x_409;
} else {
 lean_dec_ref(x_409);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_655; lean_object* x_656; 
x_427 = lean_ctor_get(x_377, 0);
lean_inc(x_427);
lean_dec(x_377);
x_655 = lean_box(0);
lean_inc(x_427);
x_656 = l_Lake_PackageConfig_decodeToml(x_427, x_655);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
lean_dec(x_656);
x_658 = l_Lake_decodeLeanOptions___closed__1;
x_659 = l_Array_append___rarg(x_658, x_657);
lean_dec(x_657);
x_660 = l_Lake_loadTomlConfig___closed__11;
x_428 = x_660;
x_429 = x_659;
goto block_654;
}
else
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_ctor_get(x_656, 0);
lean_inc(x_661);
lean_dec(x_656);
x_662 = l_Lake_decodeLeanOptions___closed__1;
x_428 = x_661;
x_429 = x_662;
goto block_654;
}
block_654:
{
lean_object* x_430; lean_object* x_431; lean_object* x_600; lean_object* x_601; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
x_612 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_613 = l_Lake_loadTomlConfig___closed__9;
lean_inc(x_427);
x_614 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_612, x_613, x_427);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; 
x_615 = l_Lake_decodeLeanOptions___closed__1;
x_600 = x_615;
x_601 = x_429;
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
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_619 = x_617;
} else {
 lean_dec_ref(x_617);
 x_619 = lean_box(0);
}
x_620 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_619)) {
 x_621 = lean_alloc_ctor(0, 2, 0);
} else {
 x_621 = x_619;
}
lean_ctor_set(x_621, 0, x_618);
lean_ctor_set(x_621, 1, x_620);
x_622 = lean_unsigned_to_nat(1u);
x_623 = lean_mk_array(x_622, x_621);
x_624 = l_Array_append___rarg(x_429, x_623);
lean_dec(x_623);
x_625 = l_Lake_decodeLeanOptions___closed__1;
x_600 = x_625;
x_601 = x_624;
goto block_611;
}
case 2:
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_626 = lean_ctor_get(x_617, 0);
lean_inc(x_626);
lean_dec(x_617);
x_627 = l_Lake_LeanConfig_decodeToml___closed__5;
x_628 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
x_629 = lean_unsigned_to_nat(1u);
x_630 = lean_mk_array(x_629, x_628);
x_631 = l_Array_append___rarg(x_429, x_630);
lean_dec(x_630);
x_632 = l_Lake_decodeLeanOptions___closed__1;
x_600 = x_632;
x_601 = x_631;
goto block_611;
}
case 3:
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_633 = lean_ctor_get(x_617, 0);
lean_inc(x_633);
lean_dec(x_617);
x_634 = l_Lake_LeanConfig_decodeToml___closed__5;
x_635 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
x_636 = lean_unsigned_to_nat(1u);
x_637 = lean_mk_array(x_636, x_635);
x_638 = l_Array_append___rarg(x_429, x_637);
lean_dec(x_637);
x_639 = l_Lake_decodeLeanOptions___closed__1;
x_600 = x_639;
x_601 = x_638;
goto block_611;
}
case 5:
{
lean_object* x_640; lean_object* x_641; 
x_640 = lean_ctor_get(x_617, 1);
lean_inc(x_640);
lean_dec(x_617);
x_641 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__15(x_640);
lean_dec(x_640);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
lean_dec(x_641);
x_643 = l_Array_append___rarg(x_429, x_642);
lean_dec(x_642);
x_644 = l_Lake_decodeLeanOptions___closed__1;
x_600 = x_644;
x_601 = x_643;
goto block_611;
}
else
{
lean_object* x_645; 
x_645 = lean_ctor_get(x_641, 0);
lean_inc(x_645);
lean_dec(x_641);
x_600 = x_645;
x_601 = x_429;
goto block_611;
}
}
default: 
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_646 = lean_ctor_get(x_617, 0);
lean_inc(x_646);
if (lean_is_exclusive(x_617)) {
 lean_ctor_release(x_617, 0);
 lean_ctor_release(x_617, 1);
 x_647 = x_617;
} else {
 lean_dec_ref(x_617);
 x_647 = lean_box(0);
}
x_648 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_647)) {
 x_649 = lean_alloc_ctor(0, 2, 0);
} else {
 x_649 = x_647;
 lean_ctor_set_tag(x_649, 0);
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_648);
x_650 = lean_unsigned_to_nat(1u);
x_651 = lean_mk_array(x_650, x_649);
x_652 = l_Array_append___rarg(x_429, x_651);
lean_dec(x_651);
x_653 = l_Lake_decodeLeanOptions___closed__1;
x_600 = x_653;
x_601 = x_652;
goto block_611;
}
}
}
block_599:
{
lean_object* x_432; lean_object* x_433; lean_object* x_545; lean_object* x_546; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_558 = l_Lake_loadTomlConfig___closed__7;
lean_inc(x_427);
x_559 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_557, x_558, x_427);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; 
x_560 = l_Lake_decodeLeanOptions___closed__1;
x_545 = x_560;
x_546 = x_431;
goto block_556;
}
else
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_559, 0);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_ctor_get(x_561, 1);
lean_inc(x_562);
lean_dec(x_561);
switch (lean_obj_tag(x_562)) {
case 0:
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_564 = x_562;
} else {
 lean_dec_ref(x_562);
 x_564 = lean_box(0);
}
x_565 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_564)) {
 x_566 = lean_alloc_ctor(0, 2, 0);
} else {
 x_566 = x_564;
}
lean_ctor_set(x_566, 0, x_563);
lean_ctor_set(x_566, 1, x_565);
x_567 = lean_unsigned_to_nat(1u);
x_568 = lean_mk_array(x_567, x_566);
x_569 = l_Array_append___rarg(x_431, x_568);
lean_dec(x_568);
x_570 = l_Lake_decodeLeanOptions___closed__1;
x_545 = x_570;
x_546 = x_569;
goto block_556;
}
case 2:
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_571 = lean_ctor_get(x_562, 0);
lean_inc(x_571);
lean_dec(x_562);
x_572 = l_Lake_LeanConfig_decodeToml___closed__5;
x_573 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_573, 0, x_571);
lean_ctor_set(x_573, 1, x_572);
x_574 = lean_unsigned_to_nat(1u);
x_575 = lean_mk_array(x_574, x_573);
x_576 = l_Array_append___rarg(x_431, x_575);
lean_dec(x_575);
x_577 = l_Lake_decodeLeanOptions___closed__1;
x_545 = x_577;
x_546 = x_576;
goto block_556;
}
case 3:
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_578 = lean_ctor_get(x_562, 0);
lean_inc(x_578);
lean_dec(x_562);
x_579 = l_Lake_LeanConfig_decodeToml___closed__5;
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_578);
lean_ctor_set(x_580, 1, x_579);
x_581 = lean_unsigned_to_nat(1u);
x_582 = lean_mk_array(x_581, x_580);
x_583 = l_Array_append___rarg(x_431, x_582);
lean_dec(x_582);
x_584 = l_Lake_decodeLeanOptions___closed__1;
x_545 = x_584;
x_546 = x_583;
goto block_556;
}
case 5:
{
lean_object* x_585; lean_object* x_586; 
x_585 = lean_ctor_get(x_562, 1);
lean_inc(x_585);
lean_dec(x_562);
x_586 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__12(x_585);
lean_dec(x_585);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
lean_dec(x_586);
x_588 = l_Array_append___rarg(x_431, x_587);
lean_dec(x_587);
x_589 = l_Lake_decodeLeanOptions___closed__1;
x_545 = x_589;
x_546 = x_588;
goto block_556;
}
else
{
lean_object* x_590; 
x_590 = lean_ctor_get(x_586, 0);
lean_inc(x_590);
lean_dec(x_586);
x_545 = x_590;
x_546 = x_431;
goto block_556;
}
}
default: 
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_591 = lean_ctor_get(x_562, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_592 = x_562;
} else {
 lean_dec_ref(x_562);
 x_592 = lean_box(0);
}
x_593 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_592)) {
 x_594 = lean_alloc_ctor(0, 2, 0);
} else {
 x_594 = x_592;
 lean_ctor_set_tag(x_594, 0);
}
lean_ctor_set(x_594, 0, x_591);
lean_ctor_set(x_594, 1, x_593);
x_595 = lean_unsigned_to_nat(1u);
x_596 = lean_mk_array(x_595, x_594);
x_597 = l_Array_append___rarg(x_431, x_596);
lean_dec(x_596);
x_598 = l_Lake_decodeLeanOptions___closed__1;
x_545 = x_598;
x_546 = x_597;
goto block_556;
}
}
}
block_544:
{
lean_object* x_434; lean_object* x_435; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_503 = l_Lake_loadTomlConfig___closed__5;
lean_inc(x_427);
x_504 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_502, x_503, x_427);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; 
x_505 = l_Lake_decodeLeanOptions___closed__1;
x_434 = x_505;
x_435 = x_433;
goto block_501;
}
else
{
lean_object* x_506; lean_object* x_507; 
x_506 = lean_ctor_get(x_504, 0);
lean_inc(x_506);
lean_dec(x_504);
x_507 = lean_ctor_get(x_506, 1);
lean_inc(x_507);
lean_dec(x_506);
switch (lean_obj_tag(x_507)) {
case 0:
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_509 = x_507;
} else {
 lean_dec_ref(x_507);
 x_509 = lean_box(0);
}
x_510 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_509)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_509;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_unsigned_to_nat(1u);
x_513 = lean_mk_array(x_512, x_511);
x_514 = l_Array_append___rarg(x_433, x_513);
lean_dec(x_513);
x_515 = l_Lake_decodeLeanOptions___closed__1;
x_434 = x_515;
x_435 = x_514;
goto block_501;
}
case 2:
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
x_516 = lean_ctor_get(x_507, 0);
lean_inc(x_516);
lean_dec(x_507);
x_517 = l_Lake_LeanConfig_decodeToml___closed__5;
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
x_519 = lean_unsigned_to_nat(1u);
x_520 = lean_mk_array(x_519, x_518);
x_521 = l_Array_append___rarg(x_433, x_520);
lean_dec(x_520);
x_522 = l_Lake_decodeLeanOptions___closed__1;
x_434 = x_522;
x_435 = x_521;
goto block_501;
}
case 3:
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_523 = lean_ctor_get(x_507, 0);
lean_inc(x_523);
lean_dec(x_507);
x_524 = l_Lake_LeanConfig_decodeToml___closed__5;
x_525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
x_526 = lean_unsigned_to_nat(1u);
x_527 = lean_mk_array(x_526, x_525);
x_528 = l_Array_append___rarg(x_433, x_527);
lean_dec(x_527);
x_529 = l_Lake_decodeLeanOptions___closed__1;
x_434 = x_529;
x_435 = x_528;
goto block_501;
}
case 5:
{
lean_object* x_530; lean_object* x_531; 
x_530 = lean_ctor_get(x_507, 1);
lean_inc(x_530);
lean_dec(x_507);
x_531 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_530);
lean_dec(x_530);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
lean_dec(x_531);
x_533 = l_Array_append___rarg(x_433, x_532);
lean_dec(x_532);
x_534 = l_Lake_decodeLeanOptions___closed__1;
x_434 = x_534;
x_435 = x_533;
goto block_501;
}
else
{
lean_object* x_535; 
x_535 = lean_ctor_get(x_531, 0);
lean_inc(x_535);
lean_dec(x_531);
x_434 = x_535;
x_435 = x_433;
goto block_501;
}
}
default: 
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
x_536 = lean_ctor_get(x_507, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_507)) {
 lean_ctor_release(x_507, 0);
 lean_ctor_release(x_507, 1);
 x_537 = x_507;
} else {
 lean_dec_ref(x_507);
 x_537 = lean_box(0);
}
x_538 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_537)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_537;
 lean_ctor_set_tag(x_539, 0);
}
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_538);
x_540 = lean_unsigned_to_nat(1u);
x_541 = lean_mk_array(x_540, x_539);
x_542 = l_Array_append___rarg(x_433, x_541);
lean_dec(x_541);
x_543 = l_Lake_decodeLeanOptions___closed__1;
x_434 = x_543;
x_435 = x_542;
goto block_501;
}
}
}
block_501:
{
size_t x_436; size_t x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_436 = lean_array_size(x_434);
x_437 = 0;
x_438 = l_Array_mapMUnsafe_map___at_Lake_loadTomlConfig___spec__8(x_436, x_437, x_434);
x_459 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_460 = l_Lake_loadTomlConfig___closed__3;
x_461 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_459, x_460, x_427);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; 
x_462 = l_Lake_decodeLeanOptions___closed__1;
x_439 = x_462;
x_440 = x_435;
goto block_458;
}
else
{
lean_object* x_463; lean_object* x_464; 
x_463 = lean_ctor_get(x_461, 0);
lean_inc(x_463);
lean_dec(x_461);
x_464 = lean_ctor_get(x_463, 1);
lean_inc(x_464);
lean_dec(x_463);
switch (lean_obj_tag(x_464)) {
case 0:
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_466 = x_464;
} else {
 lean_dec_ref(x_464);
 x_466 = lean_box(0);
}
x_467 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_466)) {
 x_468 = lean_alloc_ctor(0, 2, 0);
} else {
 x_468 = x_466;
}
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_unsigned_to_nat(1u);
x_470 = lean_mk_array(x_469, x_468);
x_471 = l_Array_append___rarg(x_435, x_470);
lean_dec(x_470);
x_472 = l_Lake_decodeLeanOptions___closed__1;
x_439 = x_472;
x_440 = x_471;
goto block_458;
}
case 2:
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_473 = lean_ctor_get(x_464, 0);
lean_inc(x_473);
lean_dec(x_464);
x_474 = l_Lake_LeanConfig_decodeToml___closed__5;
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
x_476 = lean_unsigned_to_nat(1u);
x_477 = lean_mk_array(x_476, x_475);
x_478 = l_Array_append___rarg(x_435, x_477);
lean_dec(x_477);
x_479 = l_Lake_decodeLeanOptions___closed__1;
x_439 = x_479;
x_440 = x_478;
goto block_458;
}
case 3:
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_480 = lean_ctor_get(x_464, 0);
lean_inc(x_480);
lean_dec(x_464);
x_481 = l_Lake_LeanConfig_decodeToml___closed__5;
x_482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
x_483 = lean_unsigned_to_nat(1u);
x_484 = lean_mk_array(x_483, x_482);
x_485 = l_Array_append___rarg(x_435, x_484);
lean_dec(x_484);
x_486 = l_Lake_decodeLeanOptions___closed__1;
x_439 = x_486;
x_440 = x_485;
goto block_458;
}
case 5:
{
lean_object* x_487; lean_object* x_488; 
x_487 = lean_ctor_get(x_464, 1);
lean_inc(x_487);
lean_dec(x_464);
x_488 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9(x_487);
lean_dec(x_487);
if (lean_obj_tag(x_488) == 0)
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_488, 0);
lean_inc(x_489);
lean_dec(x_488);
x_490 = l_Array_append___rarg(x_435, x_489);
lean_dec(x_489);
x_491 = l_Lake_decodeLeanOptions___closed__1;
x_439 = x_491;
x_440 = x_490;
goto block_458;
}
else
{
lean_object* x_492; 
x_492 = lean_ctor_get(x_488, 0);
lean_inc(x_492);
lean_dec(x_488);
x_439 = x_492;
x_440 = x_435;
goto block_458;
}
}
default: 
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_493 = lean_ctor_get(x_464, 0);
lean_inc(x_493);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_494 = x_464;
} else {
 lean_dec_ref(x_464);
 x_494 = lean_box(0);
}
x_495 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_494)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_494;
 lean_ctor_set_tag(x_496, 0);
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_495);
x_497 = lean_unsigned_to_nat(1u);
x_498 = lean_mk_array(x_497, x_496);
x_499 = l_Array_append___rarg(x_435, x_498);
lean_dec(x_498);
x_500 = l_Lake_decodeLeanOptions___closed__1;
x_439 = x_500;
x_440 = x_499;
goto block_458;
}
}
}
block_458:
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_441 = lean_ctor_get(x_1, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_1, 3);
lean_inc(x_442);
x_443 = l_System_FilePath_join(x_441, x_442);
x_444 = lean_ctor_get(x_428, 3);
lean_inc(x_444);
x_445 = lean_ctor_get(x_1, 7);
lean_inc(x_445);
x_446 = lean_ctor_get(x_1, 8);
lean_inc(x_446);
lean_dec(x_1);
x_447 = lean_box(0);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_448 = lean_ctor_get(x_428, 17);
lean_inc(x_448);
x_449 = lean_ctor_get(x_428, 19);
lean_inc(x_449);
x_450 = l_Lake_defaultManifestFile;
x_451 = l_Lake_decodeLeanOptions___closed__1;
x_452 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_452, 0, x_443);
lean_ctor_set(x_452, 1, x_442);
lean_ctor_set(x_452, 2, x_428);
lean_ctor_set(x_452, 3, x_372);
lean_ctor_set(x_452, 4, x_450);
lean_ctor_set(x_452, 5, x_445);
lean_ctor_set(x_452, 6, x_446);
lean_ctor_set(x_452, 7, x_439);
lean_ctor_set(x_452, 8, x_430);
lean_ctor_set(x_452, 9, x_432);
lean_ctor_set(x_452, 10, x_447);
lean_ctor_set(x_452, 11, x_447);
lean_ctor_set(x_452, 12, x_438);
lean_ctor_set(x_452, 13, x_447);
lean_ctor_set(x_452, 14, x_451);
lean_ctor_set(x_452, 15, x_451);
lean_ctor_set(x_452, 16, x_448);
lean_ctor_set(x_452, 17, x_449);
x_380 = x_452;
x_381 = x_440;
goto block_405;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_453 = lean_ctor_get(x_428, 17);
lean_inc(x_453);
x_454 = lean_ctor_get(x_428, 19);
lean_inc(x_454);
x_455 = lean_ctor_get(x_444, 0);
lean_inc(x_455);
lean_dec(x_444);
x_456 = l_Lake_decodeLeanOptions___closed__1;
x_457 = lean_alloc_ctor(0, 18, 0);
lean_ctor_set(x_457, 0, x_443);
lean_ctor_set(x_457, 1, x_442);
lean_ctor_set(x_457, 2, x_428);
lean_ctor_set(x_457, 3, x_372);
lean_ctor_set(x_457, 4, x_455);
lean_ctor_set(x_457, 5, x_445);
lean_ctor_set(x_457, 6, x_446);
lean_ctor_set(x_457, 7, x_439);
lean_ctor_set(x_457, 8, x_430);
lean_ctor_set(x_457, 9, x_432);
lean_ctor_set(x_457, 10, x_447);
lean_ctor_set(x_457, 11, x_447);
lean_ctor_set(x_457, 12, x_438);
lean_ctor_set(x_457, 13, x_447);
lean_ctor_set(x_457, 14, x_456);
lean_ctor_set(x_457, 15, x_456);
lean_ctor_set(x_457, 16, x_453);
lean_ctor_set(x_457, 17, x_454);
x_380 = x_457;
x_381 = x_440;
goto block_405;
}
}
}
}
block_556:
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_551; 
x_547 = lean_array_get_size(x_545);
x_548 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_549 = l_Lake_RBArray_mkEmpty___rarg(x_548, x_547);
x_550 = lean_unsigned_to_nat(0u);
x_551 = lean_nat_dec_lt(x_550, x_547);
if (x_551 == 0)
{
lean_dec(x_547);
lean_dec(x_545);
x_432 = x_549;
x_433 = x_546;
goto block_544;
}
else
{
uint8_t x_552; 
x_552 = lean_nat_dec_le(x_547, x_547);
if (x_552 == 0)
{
lean_dec(x_547);
lean_dec(x_545);
x_432 = x_549;
x_433 = x_546;
goto block_544;
}
else
{
size_t x_553; size_t x_554; lean_object* x_555; 
x_553 = 0;
x_554 = lean_usize_of_nat(x_547);
lean_dec(x_547);
x_555 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__11(x_545, x_553, x_554, x_549);
lean_dec(x_545);
x_432 = x_555;
x_433 = x_546;
goto block_544;
}
}
}
}
block_611:
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; uint8_t x_606; 
x_602 = lean_array_get_size(x_600);
x_603 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_604 = l_Lake_RBArray_mkEmpty___rarg(x_603, x_602);
x_605 = lean_unsigned_to_nat(0u);
x_606 = lean_nat_dec_lt(x_605, x_602);
if (x_606 == 0)
{
lean_dec(x_602);
lean_dec(x_600);
x_430 = x_604;
x_431 = x_601;
goto block_599;
}
else
{
uint8_t x_607; 
x_607 = lean_nat_dec_le(x_602, x_602);
if (x_607 == 0)
{
lean_dec(x_602);
lean_dec(x_600);
x_430 = x_604;
x_431 = x_601;
goto block_599;
}
else
{
size_t x_608; size_t x_609; lean_object* x_610; 
x_608 = 0;
x_609 = lean_usize_of_nat(x_602);
lean_dec(x_602);
x_610 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__14(x_600, x_608, x_609, x_604);
lean_dec(x_600);
x_430 = x_610;
x_431 = x_601;
goto block_599;
}
}
}
}
}
block_405:
{
uint8_t x_382; 
x_382 = l_Array_isEmpty___rarg(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; 
lean_dec(x_380);
x_383 = lean_array_get_size(x_381);
x_384 = lean_unsigned_to_nat(0u);
x_385 = lean_nat_dec_lt(x_384, x_383);
x_386 = lean_array_get_size(x_378);
if (x_385 == 0)
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_374);
if (lean_is_scalar(x_379)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_379;
 lean_ctor_set_tag(x_387, 1);
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_378);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_376);
return x_388;
}
else
{
uint8_t x_389; 
x_389 = lean_nat_dec_le(x_383, x_383);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_383);
lean_dec(x_381);
lean_dec(x_374);
if (lean_is_scalar(x_379)) {
 x_390 = lean_alloc_ctor(1, 2, 0);
} else {
 x_390 = x_379;
 lean_ctor_set_tag(x_390, 1);
}
lean_ctor_set(x_390, 0, x_386);
lean_ctor_set(x_390, 1, x_378);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_376);
return x_391;
}
else
{
size_t x_392; size_t x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_379);
x_392 = 0;
x_393 = lean_usize_of_nat(x_383);
lean_dec(x_383);
x_394 = lean_box(0);
x_395 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1(x_374, x_381, x_392, x_393, x_394, x_378, x_376);
lean_dec(x_381);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_398 = x_395;
} else {
 lean_dec_ref(x_395);
 x_398 = lean_box(0);
}
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_396)) {
 lean_ctor_release(x_396, 0);
 lean_ctor_release(x_396, 1);
 x_400 = x_396;
} else {
 lean_dec_ref(x_396);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
 lean_ctor_set_tag(x_401, 1);
}
lean_ctor_set(x_401, 0, x_386);
lean_ctor_set(x_401, 1, x_399);
if (lean_is_scalar(x_398)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_398;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_397);
return x_402;
}
}
}
else
{
lean_object* x_403; lean_object* x_404; 
lean_dec(x_381);
lean_dec(x_374);
if (lean_is_scalar(x_379)) {
 x_403 = lean_alloc_ctor(0, 2, 0);
} else {
 x_403 = x_379;
}
lean_ctor_set(x_403, 0, x_380);
lean_ctor_set(x_403, 1, x_378);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_376);
return x_404;
}
}
}
}
}
else
{
uint8_t x_673; 
lean_dec(x_1);
x_673 = !lean_is_exclusive(x_4);
if (x_673 == 0)
{
lean_object* x_674; 
x_674 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_674, 0, x_4);
lean_ctor_set(x_674, 1, x_5);
return x_674;
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_675 = lean_ctor_get(x_4, 0);
x_676 = lean_ctor_get(x_4, 1);
lean_inc(x_676);
lean_inc(x_675);
lean_dec(x_4);
x_677 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_677, 0, x_675);
lean_ctor_set(x_677, 1, x_676);
x_678 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_678, 0, x_677);
lean_ctor_set(x_678, 1, x_5);
return x_678;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_loadTomlConfig___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_loadTomlConfig___spec__8(x_4, x_5, x_3);
return x_6;
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__11(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__12___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__12(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__14(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__16___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__16(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__15___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__15(x_1);
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
l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1 = _init_l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1);
l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2 = _init_l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2();
lean_mark_persistent(l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2);
l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1 = _init_l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1();
lean_mark_persistent(l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1);
l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1 = _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1();
lean_mark_persistent(l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1);
l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2 = _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2();
lean_mark_persistent(l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__2);
l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3 = _init_l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3();
lean_mark_persistent(l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3);
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
l_Lake_LeanOption_decodeToml___closed__8 = _init_l_Lake_LeanOption_decodeToml___closed__8();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__8);
l_Lake_LeanOption_decodeToml___closed__9 = _init_l_Lake_LeanOption_decodeToml___closed__9();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__9);
l_Lake_LeanOption_decodeToml___closed__10 = _init_l_Lake_LeanOption_decodeToml___closed__10();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__10);
l_Lake_LeanOption_decodeToml___closed__11 = _init_l_Lake_LeanOption_decodeToml___closed__11();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__11);
l_Lake_LeanOption_decodeToml___closed__12 = _init_l_Lake_LeanOption_decodeToml___closed__12();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__12);
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
l_Lake_decodeLeanOptions___closed__2 = _init_l_Lake_decodeLeanOptions___closed__2();
lean_mark_persistent(l_Lake_decodeLeanOptions___closed__2);
l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3___closed__1 = _init_l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3___closed__1();
lean_mark_persistent(l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3___closed__1);
l_Lake_StrPat_decodeToml___closed__1 = _init_l_Lake_StrPat_decodeToml___closed__1();
lean_mark_persistent(l_Lake_StrPat_decodeToml___closed__1);
l_Lake_StrPat_decodeToml___closed__2 = _init_l_Lake_StrPat_decodeToml___closed__2();
lean_mark_persistent(l_Lake_StrPat_decodeToml___closed__2);
l_Lake_StrPat_decodeToml___closed__3 = _init_l_Lake_StrPat_decodeToml___closed__3();
lean_mark_persistent(l_Lake_StrPat_decodeToml___closed__3);
l_Lake_StrPat_decodeToml___closed__4 = _init_l_Lake_StrPat_decodeToml___closed__4();
lean_mark_persistent(l_Lake_StrPat_decodeToml___closed__4);
l_Lake_StrPat_decodeToml___closed__5 = _init_l_Lake_StrPat_decodeToml___closed__5();
lean_mark_persistent(l_Lake_StrPat_decodeToml___closed__5);
l_Lake_StrPat_decodeToml___closed__6 = _init_l_Lake_StrPat_decodeToml___closed__6();
lean_mark_persistent(l_Lake_StrPat_decodeToml___closed__6);
l_Lake_StrPat_decodeToml___closed__7 = _init_l_Lake_StrPat_decodeToml___closed__7();
lean_mark_persistent(l_Lake_StrPat_decodeToml___closed__7);
l_Lake_StrPat_decodeToml___closed__8 = _init_l_Lake_StrPat_decodeToml___closed__8();
lean_mark_persistent(l_Lake_StrPat_decodeToml___closed__8);
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
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__12);
l_Lake_PackageConfig_decodeToml___closed__13 = _init_l_Lake_PackageConfig_decodeToml___closed__13();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__13);
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
l_Lake_PackageConfig_decodeToml___closed__37 = _init_l_Lake_PackageConfig_decodeToml___closed__37();
l_Lake_PackageConfig_decodeToml___closed__38 = _init_l_Lake_PackageConfig_decodeToml___closed__38();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__38);
l_Lake_PackageConfig_decodeToml___closed__39 = _init_l_Lake_PackageConfig_decodeToml___closed__39();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__39);
l_Lake_PackageConfig_decodeToml___closed__40 = _init_l_Lake_PackageConfig_decodeToml___closed__40();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__40);
l_Lake_PackageConfig_decodeToml___closed__41 = _init_l_Lake_PackageConfig_decodeToml___closed__41();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__41);
l_Lake_PackageConfig_decodeToml___closed__42 = _init_l_Lake_PackageConfig_decodeToml___closed__42();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__42);
l_Lake_PackageConfig_decodeToml___closed__43 = _init_l_Lake_PackageConfig_decodeToml___closed__43();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__43);
l_Lake_PackageConfig_decodeToml___closed__44 = _init_l_Lake_PackageConfig_decodeToml___closed__44();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__44);
l_Lake_PackageConfig_decodeToml___closed__45 = _init_l_Lake_PackageConfig_decodeToml___closed__45();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__45);
l_Lake_PackageConfig_decodeToml___closed__46 = _init_l_Lake_PackageConfig_decodeToml___closed__46();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__46);
l_Lake_PackageConfig_decodeToml___closed__47 = _init_l_Lake_PackageConfig_decodeToml___closed__47();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__47);
l_Lake_PackageConfig_decodeToml___closed__48 = _init_l_Lake_PackageConfig_decodeToml___closed__48();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__48);
l_Lake_PackageConfig_decodeToml___closed__49 = _init_l_Lake_PackageConfig_decodeToml___closed__49();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__49);
l_Lake_PackageConfig_decodeToml___closed__50 = _init_l_Lake_PackageConfig_decodeToml___closed__50();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__50);
l_Lake_PackageConfig_decodeToml___closed__51 = _init_l_Lake_PackageConfig_decodeToml___closed__51();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__51);
l_Lake_PackageConfig_decodeToml___closed__52 = _init_l_Lake_PackageConfig_decodeToml___closed__52();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__52);
l_Lake_PackageConfig_decodeToml___closed__53 = _init_l_Lake_PackageConfig_decodeToml___closed__53();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__53);
l_Lake_PackageConfig_decodeToml___closed__54 = _init_l_Lake_PackageConfig_decodeToml___closed__54();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__54);
l_Lake_PackageConfig_decodeToml___closed__55 = _init_l_Lake_PackageConfig_decodeToml___closed__55();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__55);
l_Lake_PackageConfig_decodeToml___closed__56 = _init_l_Lake_PackageConfig_decodeToml___closed__56();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__56);
l_Lake_PackageConfig_decodeToml___closed__57 = _init_l_Lake_PackageConfig_decodeToml___closed__57();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__57);
l_Lake_PackageConfig_decodeToml___closed__58 = _init_l_Lake_PackageConfig_decodeToml___closed__58();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__58);
l_Lake_PackageConfig_decodeToml___closed__59 = _init_l_Lake_PackageConfig_decodeToml___closed__59();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__59);
l_Lake_PackageConfig_decodeToml___closed__60 = _init_l_Lake_PackageConfig_decodeToml___closed__60();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__60);
l_Lake_PackageConfig_decodeToml___closed__61 = _init_l_Lake_PackageConfig_decodeToml___closed__61();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__61);
l_Lake_PackageConfig_decodeToml___closed__62 = _init_l_Lake_PackageConfig_decodeToml___closed__62();
lean_mark_persistent(l_Lake_PackageConfig_decodeToml___closed__62);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3);
l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4 = _init_l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4();
lean_mark_persistent(l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4);
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
l_Lake_LeanExeConfig_decodeToml___closed__7 = _init_l_Lake_LeanExeConfig_decodeToml___closed__7();
lean_mark_persistent(l_Lake_LeanExeConfig_decodeToml___closed__7);
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
l_Lake_loadTomlConfig___closed__11 = _init_l_Lake_loadTomlConfig___closed__11();
lean_mark_persistent(l_Lake_loadTomlConfig___closed__11);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
