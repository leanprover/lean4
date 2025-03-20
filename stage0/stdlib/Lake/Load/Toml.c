// Lean compiler output
// Module: Lake.Load.Toml
// Imports: Lake.Toml.Load Lake.Toml.Decode Lake.Config.Package Lake.Util.Log
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__4(lean_object*);
static lean_object* l_Lake_Backend_decodeToml___closed__2;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__10;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__57;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__11;
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_decodeTargetDecls___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__4(lean_object*, size_t, size_t, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__2;
static lean_object* l_Lake_LeanOption_decodeToml___closed__4;
static lean_object* l_Lake_decodeLeanOptions___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__60;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml(lean_object*, lean_object*);
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__24;
static lean_object* l_Lake_Backend_decodeToml___closed__4;
static lean_object* l_Lake_Dependency_decodeToml___closed__2;
extern lean_object* l_Lake_defaultBuildDir;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__33;
static uint8_t l_Lake_PackageConfig_decodeToml___closed__37;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__17;
static lean_object* l_Lake_instDecodeTomlDependencySrc___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanConfig___lambda__1(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__1;
lean_object* l_Lake_Toml_ppKey(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependency;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forMAux___at_Lake_loadTomlConfig___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__15;
LEAN_EXPORT lean_object* l_Lake_StrPat_decodeToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__11;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__62;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlStdVer(lean_object*);
static lean_object* l_Lake_WorkspaceConfig_decodeToml___closed__3;
uint8_t l_Lean_RBNode_isRed___rarg(lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__1;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_RBNode_dFind___at_Lake_decodeTargetDecls_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___lambda__1(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_RBNode_dFind___at_Lake_decodeTargetDecls_go___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__35;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__6(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptionsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_decodeToml___spec__3(size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__9;
extern lean_object* l_Lake_versionTagPresets;
static lean_object* l_Lake_BuildType_decodeToml___closed__6;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__21;
LEAN_EXPORT lean_object* l_Lake_Glob_ofString_x3f(lean_object*);
static lean_object* l_Lake_LeanOptionValue_decodeToml___closed__1;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependency___lambda__1(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__2;
static lean_object* l_Lake_takeNamePart___closed__1;
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
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__2(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3(lean_object*, lean_object*);
lean_object* l_panic___at_String_toNat_x21___spec__1(lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__3;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__5;
uint8_t l_instDecidableNot___rarg(uint8_t);
static lean_object* l_Lake_StrPat_decodeToml___closed__2;
static lean_object* l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlWorkspaceConfig___lambda__1(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__18;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1___boxed(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__50;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanExeConfig(lean_object*);
static lean_object* l_Lake_Toml_Table_decode_x3f___at_Lake_StrPat_decodeToml___spec__3___closed__1;
static lean_object* l_Lake_Dependency_decodeToml___closed__9;
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_decodeTargetDecls_go___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_takeNamePart___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__26;
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lean_RBNode_setBlack___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlPackageConfig___lambda__1(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__40;
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__1;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__51;
static lean_object* l_Lake_LeanOption_decodeToml___closed__12;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__8;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__5;
static lean_object* l_Lake_decodeTargetDecls___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__1;
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__48;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptions(lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__10;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__61;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanConfig;
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__3;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__19;
LEAN_EXPORT lean_object* l_Lake_Dependency_decodeToml(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanLibConfig___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__6;
lean_object* l_Lean_Parser_mkInputContext(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Dependency_decodeToml___closed__4;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanExeConfig___lambda__1(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_StrPat_decodeToml___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1___closed__2;
static lean_object* l_Lake_StrPat_decodeToml___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__22;
static lean_object* l_Lake_LeanOption_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_StrPat_decodeToml___closed__5;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__31;
static lean_object* l_Lake_loadTomlConfig___closed__2;
LEAN_EXPORT lean_object* l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__4;
static lean_object* l_Lake_decodeTargetDecls___closed__7;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1___boxed(lean_object*);
static lean_object* l_Lake_Dependency_decodeToml___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_PackageConfig_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__23;
static lean_object* l_Lake_decodeLeanOptions___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forM___at_Lake_loadTomlConfig___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__5;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__39;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlWorkspaceConfig;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__18;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_decodeNatLitVal_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__15;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instDecodeTomlLeanConfig___closed__1;
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
LEAN_EXPORT lean_object* l_Lake_decodeTargetDecls_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__16;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlBackend(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
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
static lean_object* l_Lake_decodeTargetDecls___closed__1;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__45;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__44;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__6;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependencySrc___lambda__1(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__32;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
lean_object* l_Lake_StdVer_parse(lean_object*);
lean_object* l_Lake_mergeErrors___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__24;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_StrPat_decodeToml___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__20;
LEAN_EXPORT uint8_t l_Lake_StrPat_decodeToml___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__5(lean_object*, lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__1;
static lean_object* l_Lake_BuildType_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__4___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__2;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__28;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanExeConfig_decodeToml___closed__5;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_LeanConfig_decodeToml(lean_object*);
static lean_object* l_Lake_BuildType_decodeToml___closed__9;
LEAN_EXPORT lean_object* l_Lake_takeName(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__38;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__3(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_decodeLeanOptionsAux___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__14;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlGlob(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__43;
static lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__11;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_PackageConfig_decodeToml___spec__1___boxed(lean_object*);
static lean_object* l_Lake_instDecodeTomlDependency___closed__1;
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanOption;
lean_object* l_String_toName(lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__16;
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__10;
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig___lambda__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_WorkspaceConfig_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Lake_takeName_takeRest(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lake_defaultNativeLibDir;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2(lean_object*, lean_object*);
static lean_object* l_Lake_DependencySrc_decodeToml___closed__4;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_StrPat_decodeToml___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependencySrc;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_PackageConfig_decodeToml___spec__1(lean_object*);
extern lean_object* l_Lake_defaultVersionTags;
LEAN_EXPORT lean_object* l_Lake_LeanExeConfig_decodeToml(lean_object*, lean_object*);
static lean_object* l_Lake_Dependency_decodeToml___closed__8;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__4;
static lean_object* l_Lake_BuildType_decodeToml___closed__4;
static lean_object* l_Lake_PackageConfig_decodeToml___closed__49;
LEAN_EXPORT lean_object* l_Lake_decodeTargetDecls(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__11;
static lean_object* l_Lake_Dependency_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lake_LeanLibConfig_decodeToml___lambda__1(lean_object*, uint8_t);
static lean_object* l_Lake_WorkspaceConfig_decodeToml___closed__4;
static lean_object* l_Lake_takeNamePart___closed__3;
lean_object* lean_array_mk(lean_object*);
static uint8_t l_Lake_LeanOption_decodeToml___closed__5;
static lean_object* l_Lake_decodeTargetDecls___closed__4;
static lean_object* l_Lake_Backend_decodeToml___closed__3;
static lean_object* l_Lake_DependencySrc_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Lake_Glob_decodeToml(lean_object*);
static lean_object* l_Lake_StrPat_decodeToml___closed__1;
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlStrPat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9___boxed(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_decodeTargetDecls___closed__3;
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
static lean_object* l_Lake_decodeTargetDecls___closed__6;
LEAN_EXPORT lean_object* l_Lake_Toml_decodeArray___at_Lake_decodeLeanOptions___spec__1(lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__5;
static lean_object* l_Lake_LeanOption_decodeToml___closed__10;
static lean_object* l_Lake_LeanConfig_decodeToml___closed__14;
static lean_object* l_Lake_Dependency_decodeToml___closed__5;
static lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3___closed__1;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__7;
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__25;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_PackageConfig_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeNamePart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__3___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_LeanLibConfig_decodeToml___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l_Lake_PackageConfig_decodeToml___closed__10;
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_decodeTargetDecls_go___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_LeanOption_decodeToml(lean_object*);
extern lean_object* l_Lake_defaultLeanLibDir;
static lean_object* l_Lake_Glob_decodeToml___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_StrPat_decodeToml___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_LeanConfig_decodeToml___closed__12;
lean_object* l_Array_emptyWithCapacity(lean_object*, lean_object*);
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
x_3 = lean_unsigned_to_nat(19u);
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_array_mk(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_mk(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_array_mk(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_mk(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
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
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = l_String_toName(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
lean_ctor_set(x_2, 1, x_16);
x_3 = x_2;
goto block_11;
}
else
{
lean_object* x_17; 
lean_free_object(x_2);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_2);
x_20 = l_String_toName(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_3 = x_22;
goto block_11;
}
else
{
lean_object* x_23; 
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_20);
return x_23;
}
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
lean_dec(x_2);
x_25 = l_Lake_Glob_decodeToml___closed__2;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_3 = x_26;
goto block_11;
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_2, 0);
lean_inc(x_27);
lean_dec(x_2);
x_28 = l_Lake_Glob_decodeToml___closed__2;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_3 = x_29;
goto block_11;
}
default: 
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_2, 1);
lean_dec(x_31);
x_32 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_32);
x_3 = x_2;
goto block_11;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l_Lake_Glob_decodeToml___closed__2;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_3 = x_35;
goto block_11;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_mk(x_5);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__3(x_1, x_7, x_8, x_6);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_mk(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2(x_2, x_17);
lean_dec(x_2);
return x_18;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_array_mk(x_7);
x_9 = lean_array_size(x_8);
x_10 = 0;
x_11 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6(x_1, x_9, x_10, x_8);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_mk(x_14);
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l_Array_mapMUnsafe_map___at_Lake_LeanOption_decodeToml___spec__6(x_1, x_16, x_17, x_15);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_3);
if (x_20 == 0)
{
return x_3;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_mk(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__5(x_2, x_17);
lean_dec(x_2);
return x_18;
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
x_2 = l_Array_emptyWithCapacity(lean_box(0), x_1);
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
static uint8_t _init_l_Lake_LeanOption_decodeToml___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__3;
x_2 = l_Array_isEmpty___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__7() {
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
static lean_object* _init_l_Lake_LeanOption_decodeToml___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_LeanOption_decodeToml___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
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
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_80; 
lean_dec(x_30);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_array_fget(x_31, x_42);
switch (lean_obj_tag(x_43)) {
case 0:
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_43);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_43, 0);
x_117 = lean_ctor_get(x_43, 1);
x_118 = l_String_toName(x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
lean_dec(x_32);
x_119 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
lean_ctor_set(x_43, 1, x_119);
x_80 = x_43;
goto block_114;
}
else
{
lean_free_object(x_43);
lean_dec(x_116);
x_44 = x_118;
goto block_79;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_43, 0);
x_121 = lean_ctor_get(x_43, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_43);
x_122 = l_String_toName(x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_32);
x_123 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
x_80 = x_124;
goto block_114;
}
else
{
lean_dec(x_120);
x_44 = x_122;
goto block_79;
}
}
}
case 2:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_32);
x_125 = lean_ctor_get(x_43, 0);
lean_inc(x_125);
lean_dec(x_43);
x_126 = l_Lake_Glob_decodeToml___closed__2;
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_80 = x_127;
goto block_114;
}
case 3:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_32);
x_128 = lean_ctor_get(x_43, 0);
lean_inc(x_128);
lean_dec(x_43);
x_129 = l_Lake_Glob_decodeToml___closed__2;
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_80 = x_130;
goto block_114;
}
default: 
{
uint8_t x_131; 
lean_dec(x_32);
x_131 = !lean_is_exclusive(x_43);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_43, 1);
lean_dec(x_132);
x_133 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_43, 0);
lean_ctor_set(x_43, 1, x_133);
x_80 = x_43;
goto block_114;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_43, 0);
lean_inc(x_134);
lean_dec(x_43);
x_135 = l_Lake_Glob_decodeToml___closed__2;
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_80 = x_136;
goto block_114;
}
}
}
block_79:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_array_fget(x_31, x_45);
lean_dec(x_31);
x_47 = l_Lake_LeanOptionValue_decodeToml(x_46);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_32;
 lean_ctor_set_tag(x_51, 1);
}
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_array_mk(x_51);
x_53 = l_Lake_LeanOption_decodeToml___closed__3;
x_54 = l_Array_append___rarg(x_53, x_52);
lean_dec(x_52);
x_55 = l_Lake_LeanOption_decodeToml___closed__4;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_44);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_isEmpty___rarg(x_54);
if (x_57 == 0)
{
lean_dec(x_56);
lean_ctor_set(x_47, 0, x_54);
return x_47;
}
else
{
lean_dec(x_54);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_56);
return x_47;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_ctor_get(x_47, 0);
lean_inc(x_58);
lean_dec(x_47);
x_59 = lean_box(0);
if (lean_is_scalar(x_32)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_32;
 lean_ctor_set_tag(x_60, 1);
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_mk(x_60);
x_62 = l_Lake_LeanOption_decodeToml___closed__3;
x_63 = l_Array_append___rarg(x_62, x_61);
lean_dec(x_61);
x_64 = l_Lake_LeanOption_decodeToml___closed__4;
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_44);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Array_isEmpty___rarg(x_63);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_63);
return x_67;
}
else
{
lean_object* x_68; 
lean_dec(x_63);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_65);
return x_68;
}
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_47);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_47, 0);
x_71 = l_Lake_LeanOption_decodeToml___closed__5;
if (x_71 == 0)
{
lean_object* x_72; 
lean_free_object(x_47);
lean_dec(x_70);
lean_dec(x_44);
lean_dec(x_32);
x_72 = l_Lake_LeanOption_decodeToml___closed__6;
return x_72;
}
else
{
lean_object* x_73; 
if (lean_is_scalar(x_32)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_32;
 lean_ctor_set_tag(x_73, 0);
}
lean_ctor_set(x_73, 0, x_44);
lean_ctor_set(x_73, 1, x_70);
lean_ctor_set(x_47, 0, x_73);
return x_47;
}
}
else
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_47, 0);
lean_inc(x_74);
lean_dec(x_47);
x_75 = l_Lake_LeanOption_decodeToml___closed__5;
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_74);
lean_dec(x_44);
lean_dec(x_32);
x_76 = l_Lake_LeanOption_decodeToml___closed__6;
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
if (lean_is_scalar(x_32)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_32;
 lean_ctor_set_tag(x_77, 0);
}
lean_ctor_set(x_77, 0, x_44);
lean_ctor_set(x_77, 1, x_74);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
}
block_114:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_array_mk(x_82);
x_84 = l_Lake_LeanOption_decodeToml___closed__3;
x_85 = l_Array_append___rarg(x_84, x_83);
lean_dec(x_83);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_array_fget(x_31, x_86);
lean_dec(x_31);
x_88 = l_Lake_LeanOptionValue_decodeToml(x_87);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_81);
x_92 = lean_array_mk(x_91);
x_93 = l_Array_append___rarg(x_85, x_92);
lean_dec(x_92);
x_94 = l_Array_isEmpty___rarg(x_93);
if (x_94 == 0)
{
lean_ctor_set(x_88, 0, x_93);
return x_88;
}
else
{
lean_object* x_95; 
lean_dec(x_93);
lean_free_object(x_88);
x_95 = l_Lake_LeanOption_decodeToml___closed__8;
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_88, 0);
lean_inc(x_96);
lean_dec(x_88);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_81);
x_98 = lean_array_mk(x_97);
x_99 = l_Array_append___rarg(x_85, x_98);
lean_dec(x_98);
x_100 = l_Array_isEmpty___rarg(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_99);
return x_101;
}
else
{
lean_object* x_102; 
lean_dec(x_99);
x_102 = l_Lake_LeanOption_decodeToml___closed__8;
return x_102;
}
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_88);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_104 = lean_ctor_get(x_88, 0);
x_105 = lean_box(0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
x_107 = l_Array_isEmpty___rarg(x_85);
if (x_107 == 0)
{
lean_dec(x_106);
lean_ctor_set_tag(x_88, 0);
lean_ctor_set(x_88, 0, x_85);
return x_88;
}
else
{
lean_dec(x_85);
lean_ctor_set(x_88, 0, x_106);
return x_88;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_88, 0);
lean_inc(x_108);
lean_dec(x_88);
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_108);
x_111 = l_Array_isEmpty___rarg(x_85);
if (x_111 == 0)
{
lean_object* x_112; 
lean_dec(x_110);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_85);
return x_112;
}
else
{
lean_object* x_113; 
lean_dec(x_85);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_110);
return x_113;
}
}
}
}
}
}
case 6:
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_1);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_1, 0);
x_139 = lean_ctor_get(x_1, 1);
x_140 = l_Lake_LeanOption_decodeToml___closed__10;
lean_inc(x_138);
lean_inc(x_139);
x_141 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(x_139, x_140, x_138);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec(x_141);
x_143 = l_Lake_LeanOption_decodeToml___closed__3;
x_144 = l_Array_append___rarg(x_143, x_142);
lean_dec(x_142);
x_145 = l_Lake_LeanOption_decodeToml___closed__12;
x_146 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(x_139, x_145, x_138);
if (lean_obj_tag(x_146) == 0)
{
uint8_t x_147; 
lean_free_object(x_1);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = l_Array_append___rarg(x_144, x_148);
lean_dec(x_148);
x_150 = l_Array_isEmpty___rarg(x_149);
if (x_150 == 0)
{
lean_ctor_set(x_146, 0, x_149);
return x_146;
}
else
{
lean_object* x_151; 
lean_dec(x_149);
lean_free_object(x_146);
x_151 = l_Lake_LeanOption_decodeToml___closed__8;
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_146, 0);
lean_inc(x_152);
lean_dec(x_146);
x_153 = l_Array_append___rarg(x_144, x_152);
lean_dec(x_152);
x_154 = l_Array_isEmpty___rarg(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_153);
return x_155;
}
else
{
lean_object* x_156; 
lean_dec(x_153);
x_156 = l_Lake_LeanOption_decodeToml___closed__8;
return x_156;
}
}
}
else
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_146);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_158 = lean_ctor_get(x_146, 0);
x_159 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_158);
lean_ctor_set(x_1, 0, x_159);
x_160 = l_Array_isEmpty___rarg(x_144);
if (x_160 == 0)
{
lean_dec(x_1);
lean_ctor_set_tag(x_146, 0);
lean_ctor_set(x_146, 0, x_144);
return x_146;
}
else
{
lean_dec(x_144);
lean_ctor_set(x_146, 0, x_1);
return x_146;
}
}
else
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_146, 0);
lean_inc(x_161);
lean_dec(x_146);
x_162 = lean_box(0);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_161);
lean_ctor_set(x_1, 0, x_162);
x_163 = l_Array_isEmpty___rarg(x_144);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_1);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_144);
return x_164;
}
else
{
lean_object* x_165; 
lean_dec(x_144);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_1);
return x_165;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_141, 0);
lean_inc(x_166);
lean_dec(x_141);
x_167 = l_Lake_LeanOption_decodeToml___closed__12;
x_168 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(x_139, x_167, x_138);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = l_Lake_LeanOption_decodeToml___closed__3;
x_172 = l_Array_append___rarg(x_171, x_170);
lean_dec(x_170);
x_173 = l_Lake_LeanOption_decodeToml___closed__4;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_173);
lean_ctor_set(x_1, 0, x_166);
x_174 = l_Array_isEmpty___rarg(x_172);
if (x_174 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_168, 0, x_172);
return x_168;
}
else
{
lean_dec(x_172);
lean_ctor_set_tag(x_168, 1);
lean_ctor_set(x_168, 0, x_1);
return x_168;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_175 = lean_ctor_get(x_168, 0);
lean_inc(x_175);
lean_dec(x_168);
x_176 = l_Lake_LeanOption_decodeToml___closed__3;
x_177 = l_Array_append___rarg(x_176, x_175);
lean_dec(x_175);
x_178 = l_Lake_LeanOption_decodeToml___closed__4;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_178);
lean_ctor_set(x_1, 0, x_166);
x_179 = l_Array_isEmpty___rarg(x_177);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec(x_1);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_177);
return x_180;
}
else
{
lean_object* x_181; 
lean_dec(x_177);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_1);
return x_181;
}
}
}
else
{
uint8_t x_182; 
x_182 = !lean_is_exclusive(x_168);
if (x_182 == 0)
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_ctor_get(x_168, 0);
x_184 = l_Lake_LeanOption_decodeToml___closed__5;
if (x_184 == 0)
{
lean_object* x_185; 
lean_free_object(x_168);
lean_dec(x_183);
lean_dec(x_166);
lean_free_object(x_1);
x_185 = l_Lake_LeanOption_decodeToml___closed__6;
return x_185;
}
else
{
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_183);
lean_ctor_set(x_1, 0, x_166);
lean_ctor_set(x_168, 0, x_1);
return x_168;
}
}
else
{
lean_object* x_186; uint8_t x_187; 
x_186 = lean_ctor_get(x_168, 0);
lean_inc(x_186);
lean_dec(x_168);
x_187 = l_Lake_LeanOption_decodeToml___closed__5;
if (x_187 == 0)
{
lean_object* x_188; 
lean_dec(x_186);
lean_dec(x_166);
lean_free_object(x_1);
x_188 = l_Lake_LeanOption_decodeToml___closed__6;
return x_188;
}
else
{
lean_object* x_189; 
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_186);
lean_ctor_set(x_1, 0, x_166);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_1);
return x_189;
}
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = lean_ctor_get(x_1, 0);
x_191 = lean_ctor_get(x_1, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_1);
x_192 = l_Lake_LeanOption_decodeToml___closed__10;
lean_inc(x_190);
lean_inc(x_191);
x_193 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1(x_191, x_192, x_190);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec(x_193);
x_195 = l_Lake_LeanOption_decodeToml___closed__3;
x_196 = l_Array_append___rarg(x_195, x_194);
lean_dec(x_194);
x_197 = l_Lake_LeanOption_decodeToml___closed__12;
x_198 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(x_191, x_197, x_190);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_200 = x_198;
} else {
 lean_dec_ref(x_198);
 x_200 = lean_box(0);
}
x_201 = l_Array_append___rarg(x_196, x_199);
lean_dec(x_199);
x_202 = l_Array_isEmpty___rarg(x_201);
if (x_202 == 0)
{
lean_object* x_203; 
if (lean_is_scalar(x_200)) {
 x_203 = lean_alloc_ctor(0, 1, 0);
} else {
 x_203 = x_200;
}
lean_ctor_set(x_203, 0, x_201);
return x_203;
}
else
{
lean_object* x_204; 
lean_dec(x_201);
lean_dec(x_200);
x_204 = l_Lake_LeanOption_decodeToml___closed__8;
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_198, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_206 = x_198;
} else {
 lean_dec_ref(x_198);
 x_206 = lean_box(0);
}
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_205);
x_209 = l_Array_isEmpty___rarg(x_196);
if (x_209 == 0)
{
lean_object* x_210; 
lean_dec(x_208);
if (lean_is_scalar(x_206)) {
 x_210 = lean_alloc_ctor(0, 1, 0);
} else {
 x_210 = x_206;
 lean_ctor_set_tag(x_210, 0);
}
lean_ctor_set(x_210, 0, x_196);
return x_210;
}
else
{
lean_object* x_211; 
lean_dec(x_196);
if (lean_is_scalar(x_206)) {
 x_211 = lean_alloc_ctor(1, 1, 0);
} else {
 x_211 = x_206;
}
lean_ctor_set(x_211, 0, x_208);
return x_211;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_193, 0);
lean_inc(x_212);
lean_dec(x_193);
x_213 = l_Lake_LeanOption_decodeToml___closed__12;
x_214 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__4(x_191, x_213, x_190);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
x_217 = l_Lake_LeanOption_decodeToml___closed__3;
x_218 = l_Array_append___rarg(x_217, x_215);
lean_dec(x_215);
x_219 = l_Lake_LeanOption_decodeToml___closed__4;
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_212);
lean_ctor_set(x_220, 1, x_219);
x_221 = l_Array_isEmpty___rarg(x_218);
if (x_221 == 0)
{
lean_object* x_222; 
lean_dec(x_220);
if (lean_is_scalar(x_216)) {
 x_222 = lean_alloc_ctor(0, 1, 0);
} else {
 x_222 = x_216;
}
lean_ctor_set(x_222, 0, x_218);
return x_222;
}
else
{
lean_object* x_223; 
lean_dec(x_218);
if (lean_is_scalar(x_216)) {
 x_223 = lean_alloc_ctor(1, 1, 0);
} else {
 x_223 = x_216;
 lean_ctor_set_tag(x_223, 1);
}
lean_ctor_set(x_223, 0, x_220);
return x_223;
}
}
else
{
lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_224 = lean_ctor_get(x_214, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 x_225 = x_214;
} else {
 lean_dec_ref(x_214);
 x_225 = lean_box(0);
}
x_226 = l_Lake_LeanOption_decodeToml___closed__5;
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_212);
x_227 = l_Lake_LeanOption_decodeToml___closed__6;
return x_227;
}
else
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_228, 0, x_212);
lean_ctor_set(x_228, 1, x_224);
if (lean_is_scalar(x_225)) {
 x_229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_229 = x_225;
}
lean_ctor_set(x_229, 0, x_228);
return x_229;
}
}
}
}
}
default: 
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_1);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_231 = lean_ctor_get(x_1, 1);
lean_dec(x_231);
x_232 = l_Lake_LeanOption_decodeToml___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_232);
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_1);
lean_ctor_set(x_234, 1, x_233);
x_235 = lean_array_mk(x_234);
x_236 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_236, 0, x_235);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_237 = lean_ctor_get(x_1, 0);
lean_inc(x_237);
lean_dec(x_1);
x_238 = l_Lake_LeanOption_decodeToml___closed__1;
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_box(0);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_array_mk(x_241);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_242);
return x_243;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_array_mk(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_mk(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_array_mk(x_6);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_array_mk(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
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
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_1);
x_4 = l_Lake_LeanOptionValue_decodeToml(x_1);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_dec(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_dec(x_7);
x_8 = lean_alloc_closure((void*)(l_Lake_decodeLeanOptionsAux___lambda__1), 3, 1);
lean_closure_set(x_8, 0, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_box(0);
lean_ctor_set(x_1, 1, x_11);
lean_ctor_set(x_1, 0, x_10);
x_12 = lean_array_mk(x_1);
lean_ctor_set(x_4, 0, x_12);
x_13 = l_Lake_mergeErrors___rarg(x_3, x_4, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_box(0);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_14);
x_16 = lean_array_mk(x_1);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lake_mergeErrors___rarg(x_3, x_17, x_8);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_free_object(x_1);
x_19 = !lean_is_exclusive(x_4);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lake_mergeErrors___rarg(x_3, x_4, x_8);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lake_mergeErrors___rarg(x_3, x_22, x_8);
return x_23;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_alloc_closure((void*)(l_Lake_decodeLeanOptionsAux___lambda__1), 3, 1);
lean_closure_set(x_24, 0, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_26 = x_4;
} else {
 lean_dec_ref(x_4);
 x_26 = lean_box(0);
}
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_array_mk(x_28);
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(0, 1, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_29);
x_31 = l_Lake_mergeErrors___rarg(x_3, x_30, x_24);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_4, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 x_33 = x_4;
} else {
 lean_dec_ref(x_4);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_Lake_mergeErrors___rarg(x_3, x_34, x_24);
return x_35;
}
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lake_LeanOptionValue_decodeToml(x_1);
x_37 = lean_alloc_closure((void*)(l_Lake_decodeLeanOptionsAux___lambda__1), 3, 1);
lean_closure_set(x_37, 0, x_2);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_36, 0);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_array_mk(x_41);
lean_ctor_set(x_36, 0, x_42);
x_43 = l_Lake_mergeErrors___rarg(x_3, x_36, x_37);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_dec(x_36);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_array_mk(x_46);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = l_Lake_mergeErrors___rarg(x_3, x_48, x_37);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_36);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Lake_mergeErrors___rarg(x_3, x_36, x_37);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_36, 0);
lean_inc(x_52);
lean_dec(x_36);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lake_mergeErrors___rarg(x_3, x_53, x_37);
return x_54;
}
}
}
case 3:
{
lean_object* x_55; lean_object* x_56; 
x_55 = l_Lake_LeanOptionValue_decodeToml(x_1);
x_56 = lean_alloc_closure((void*)(l_Lake_decodeLeanOptionsAux___lambda__1), 3, 1);
lean_closure_set(x_56, 0, x_2);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_55, 0);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_array_mk(x_60);
lean_ctor_set(x_55, 0, x_61);
x_62 = l_Lake_mergeErrors___rarg(x_3, x_55, x_56);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_55, 0);
lean_inc(x_63);
lean_dec(x_55);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_mk(x_65);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lake_mergeErrors___rarg(x_3, x_67, x_56);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_55);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = l_Lake_mergeErrors___rarg(x_3, x_55, x_56);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_55, 0);
lean_inc(x_71);
lean_dec(x_55);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = l_Lake_mergeErrors___rarg(x_3, x_72, x_56);
return x_73;
}
}
}
case 6:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_array_get_size(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_lt(x_77, x_76);
if (x_78 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_2);
return x_3;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_76, x_76);
if (x_79 == 0)
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_2);
return x_3;
}
else
{
size_t x_80; size_t x_81; lean_object* x_82; 
x_80 = 0;
x_81 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_82 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptionsAux___spec__1(x_2, x_75, x_80, x_81, x_3);
lean_dec(x_75);
return x_82;
}
}
}
default: 
{
lean_object* x_83; uint8_t x_84; 
lean_inc(x_1);
x_83 = l_Lake_LeanOptionValue_decodeToml(x_1);
x_84 = !lean_is_exclusive(x_1);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_1, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_1, 0);
lean_dec(x_86);
x_87 = lean_alloc_closure((void*)(l_Lake_decodeLeanOptionsAux___lambda__1), 3, 1);
lean_closure_set(x_87, 0, x_2);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_83, 0);
x_90 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_89);
x_91 = lean_array_mk(x_1);
lean_ctor_set(x_83, 0, x_91);
x_92 = l_Lake_mergeErrors___rarg(x_3, x_83, x_87);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_83, 0);
lean_inc(x_93);
lean_dec(x_83);
x_94 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_94);
lean_ctor_set(x_1, 0, x_93);
x_95 = lean_array_mk(x_1);
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_97 = l_Lake_mergeErrors___rarg(x_3, x_96, x_87);
return x_97;
}
}
else
{
uint8_t x_98; 
lean_free_object(x_1);
x_98 = !lean_is_exclusive(x_83);
if (x_98 == 0)
{
lean_object* x_99; 
x_99 = l_Lake_mergeErrors___rarg(x_3, x_83, x_87);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_83, 0);
lean_inc(x_100);
lean_dec(x_83);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = l_Lake_mergeErrors___rarg(x_3, x_101, x_87);
return x_102;
}
}
}
else
{
lean_object* x_103; 
lean_dec(x_1);
x_103 = lean_alloc_closure((void*)(l_Lake_decodeLeanOptionsAux___lambda__1), 3, 1);
lean_closure_set(x_103, 0, x_2);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_83, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_105 = x_83;
} else {
 lean_dec_ref(x_83);
 x_105 = lean_box(0);
}
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_array_mk(x_107);
if (lean_is_scalar(x_105)) {
 x_109 = lean_alloc_ctor(0, 1, 0);
} else {
 x_109 = x_105;
}
lean_ctor_set(x_109, 0, x_108);
x_110 = l_Lake_mergeErrors___rarg(x_3, x_109, x_103);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_111 = lean_ctor_get(x_83, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_112 = x_83;
} else {
 lean_dec_ref(x_83);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
x_114 = l_Lake_mergeErrors___rarg(x_3, x_113, x_103);
return x_114;
}
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
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lake_StdVer_parse(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
lean_ctor_set(x_1, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_mk(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
lean_ctor_set(x_1, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_mk(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_free_object(x_1);
lean_dec(x_9);
x_22 = !lean_is_exclusive(x_11);
if (x_22 == 0)
{
return x_11;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_11, 0);
lean_inc(x_23);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_1);
x_27 = l_Lake_StdVer_parse(x_26);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_29 = x_27;
} else {
 lean_dec_ref(x_27);
 x_29 = lean_box(0);
}
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_28);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_array_mk(x_32);
if (lean_is_scalar(x_29)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_29;
}
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_25);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_36 = x_27;
} else {
 lean_dec_ref(x_27);
 x_36 = lean_box(0);
}
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
}
}
case 2:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
lean_dec(x_1);
x_39 = l_Lake_Glob_decodeToml___closed__2;
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_2 = x_40;
goto block_7;
}
case 3:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_1, 0);
lean_inc(x_41);
lean_dec(x_1);
x_42 = l_Lake_Glob_decodeToml___closed__2;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_2 = x_43;
goto block_7;
}
default: 
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_1);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_1, 1);
lean_dec(x_45);
x_46 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_46);
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Lake_Glob_decodeToml___closed__2;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_2 = x_49;
goto block_7;
}
}
}
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_mk(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
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
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_21 = l_Lake_mergeErrors___rarg(x_4, x_19, x_20);
x_2 = x_8;
x_4 = x_21;
goto _start;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
x_24 = l_Lake_Glob_decodeToml___closed__2;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_9 = x_25;
goto block_17;
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
x_27 = l_Lake_Glob_decodeToml___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_9 = x_28;
goto block_17;
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_6, 1);
lean_dec(x_30);
x_31 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_31);
x_9 = x_6;
goto block_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = l_Lake_Glob_decodeToml___closed__2;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_9 = x_34;
goto block_17;
}
}
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_mk(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_15 = l_Lake_mergeErrors___rarg(x_4, x_13, x_14);
x_2 = x_8;
x_4 = x_15;
goto _start;
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
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lake_Glob_decodeToml___closed__2;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_3 = x_16;
goto block_11;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lake_Glob_decodeToml___closed__2;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_3 = x_19;
goto block_11;
}
default: 
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_dec(x_21);
x_22 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_22);
x_3 = x_2;
goto block_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lake_Glob_decodeToml___closed__2;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_3 = x_25;
goto block_11;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_mk(x_5);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lake_StrPat_decodeToml___spec__5(x_1, x_7, x_8, x_6);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
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
static lean_object* _init_l_Lake_WorkspaceConfig_decodeToml___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_defaultPackagesDir;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_WorkspaceConfig_decodeToml___closed__4() {
_start:
{
uint8_t x_1; 
x_1 = l_Lake_LeanOption_decodeToml___closed__5;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = l_Lake_LeanOption_decodeToml___closed__6;
return x_2;
}
else
{
lean_object* x_3; 
x_3 = l_Lake_WorkspaceConfig_decodeToml___closed__3;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_WorkspaceConfig_decodeToml(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_13 = l_Lake_WorkspaceConfig_decodeToml___closed__2;
x_14 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_12, x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = l_Lake_WorkspaceConfig_decodeToml___closed__4;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
switch (lean_obj_tag(x_18)) {
case 0:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lake_LeanOption_decodeToml___closed__5;
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_free_object(x_14);
x_21 = l_Lake_LeanOption_decodeToml___closed__6;
return x_21;
}
else
{
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_14);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lake_Glob_decodeToml___closed__2;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_2 = x_24;
goto block_11;
}
case 3:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_14);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lake_Glob_decodeToml___closed__2;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_2 = x_27;
goto block_11;
}
default: 
{
uint8_t x_28; 
lean_free_object(x_14);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_18, 1);
lean_dec(x_29);
x_30 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_30);
x_2 = x_18;
goto block_11;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_18, 0);
lean_inc(x_31);
lean_dec(x_18);
x_32 = l_Lake_Glob_decodeToml___closed__2;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_2 = x_33;
goto block_11;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
switch (lean_obj_tag(x_35)) {
case 0:
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lake_LeanOption_decodeToml___closed__5;
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec(x_36);
x_38 = l_Lake_LeanOption_decodeToml___closed__6;
return x_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
return x_39;
}
}
case 2:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
lean_inc(x_40);
lean_dec(x_35);
x_41 = l_Lake_Glob_decodeToml___closed__2;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_2 = x_42;
goto block_11;
}
case 3:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_35, 0);
lean_inc(x_43);
lean_dec(x_35);
x_44 = l_Lake_Glob_decodeToml___closed__2;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_2 = x_45;
goto block_11;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_35, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_47 = x_35;
} else {
 lean_dec_ref(x_35);
 x_47 = lean_box(0);
}
x_48 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
 lean_ctor_set_tag(x_49, 0);
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_2 = x_49;
goto block_11;
}
}
}
}
block_11:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_mk(x_4);
x_6 = l_Lake_LeanOption_decodeToml___closed__3;
x_7 = l_Array_append___rarg(x_6, x_5);
lean_dec(x_5);
x_8 = l_Array_isEmpty___rarg(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_7);
x_10 = l_Lake_WorkspaceConfig_decodeToml___closed__3;
return x_10;
}
}
}
}
static lean_object* _init_l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected table", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlWorkspaceConfig___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_1, 1, x_10);
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_2 = x_13;
goto block_7;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
goto block_7;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_19;
goto block_7;
}
case 6:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_WorkspaceConfig_decodeToml(x_20);
return x_21;
}
default: 
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_24);
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_2 = x_27;
goto block_7;
}
}
}
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_mk(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lake_instDecodeTomlWorkspaceConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instDecodeTomlWorkspaceConfig___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instDecodeTomlWorkspaceConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instDecodeTomlWorkspaceConfig___closed__1;
return x_1;
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
lean_object* x_2; lean_object* x_3; uint8_t x_8; lean_object* x_9; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_344 = l_Lake_LeanConfig_decodeToml___closed__24;
lean_inc(x_1);
x_345 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_343, x_344, x_1);
if (lean_obj_tag(x_345) == 0)
{
uint8_t x_346; lean_object* x_347; 
x_346 = 3;
x_347 = l_Lake_LeanOption_decodeToml___closed__3;
x_8 = x_346;
x_9 = x_347;
goto block_342;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_348 = lean_ctor_get(x_345, 0);
lean_inc(x_348);
lean_dec(x_345);
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
lean_dec(x_348);
x_350 = l_Lake_BuildType_decodeToml(x_349);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec(x_350);
x_352 = lean_box(0);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
x_354 = lean_array_mk(x_353);
x_355 = l_Lake_LeanOption_decodeToml___closed__3;
x_356 = l_Array_append___rarg(x_355, x_354);
lean_dec(x_354);
x_357 = 3;
x_8 = x_357;
x_9 = x_356;
goto block_342;
}
else
{
lean_object* x_358; lean_object* x_359; uint8_t x_360; 
x_358 = lean_ctor_get(x_350, 0);
lean_inc(x_358);
lean_dec(x_350);
x_359 = l_Lake_LeanOption_decodeToml___closed__3;
x_360 = lean_unbox(x_358);
lean_dec(x_358);
x_8 = x_360;
x_9 = x_359;
goto block_342;
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
block_342:
{
uint8_t x_10; lean_object* x_11; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_328 = l_Lake_LeanConfig_decodeToml___closed__22;
lean_inc(x_1);
x_329 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_327, x_328, x_1);
if (lean_obj_tag(x_329) == 0)
{
uint8_t x_330; 
x_330 = 2;
x_10 = x_330;
x_11 = x_9;
goto block_326;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_329, 0);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
lean_dec(x_331);
x_333 = l_Lake_Backend_decodeToml(x_332);
if (lean_obj_tag(x_333) == 0)
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
lean_dec(x_333);
x_335 = lean_box(0);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
x_337 = lean_array_mk(x_336);
x_338 = l_Array_append___rarg(x_9, x_337);
lean_dec(x_337);
x_339 = 2;
x_10 = x_339;
x_11 = x_338;
goto block_326;
}
else
{
lean_object* x_340; uint8_t x_341; 
x_340 = lean_ctor_get(x_333, 0);
lean_inc(x_340);
lean_dec(x_333);
x_341 = lean_unbox(x_340);
lean_dec(x_340);
x_10 = x_341;
x_11 = x_9;
goto block_326;
}
}
block_326:
{
lean_object* x_12; lean_object* x_13; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_280 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_281 = l_Lake_LeanConfig_decodeToml___closed__19;
lean_inc(x_1);
x_282 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_280, x_281, x_1);
x_283 = lean_box(0);
if (lean_obj_tag(x_282) == 0)
{
x_12 = x_283;
x_13 = x_11;
goto block_279;
}
else
{
uint8_t x_290; 
x_290 = !lean_is_exclusive(x_282);
if (x_290 == 0)
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_282, 0);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec(x_291);
switch (lean_obj_tag(x_292)) {
case 0:
{
uint8_t x_293; 
lean_free_object(x_282);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_292, 1);
lean_dec(x_294);
x_295 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_292, 1, x_295);
x_284 = x_292;
goto block_289;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_292, 0);
lean_inc(x_296);
lean_dec(x_292);
x_297 = l_Lake_LeanConfig_decodeToml___closed__20;
x_298 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
x_284 = x_298;
goto block_289;
}
}
case 2:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
lean_free_object(x_282);
x_299 = lean_ctor_get(x_292, 0);
lean_inc(x_299);
lean_dec(x_292);
x_300 = l_Lake_LeanConfig_decodeToml___closed__20;
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_284 = x_301;
goto block_289;
}
case 3:
{
uint8_t x_302; lean_object* x_303; 
x_302 = lean_ctor_get_uint8(x_292, sizeof(void*)*1);
lean_dec(x_292);
x_303 = lean_box(x_302);
lean_ctor_set(x_282, 0, x_303);
x_12 = x_282;
x_13 = x_11;
goto block_279;
}
default: 
{
uint8_t x_304; 
lean_free_object(x_282);
x_304 = !lean_is_exclusive(x_292);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_292, 1);
lean_dec(x_305);
x_306 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_292, 0);
lean_ctor_set(x_292, 1, x_306);
x_284 = x_292;
goto block_289;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_292, 0);
lean_inc(x_307);
lean_dec(x_292);
x_308 = l_Lake_LeanConfig_decodeToml___closed__20;
x_309 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_284 = x_309;
goto block_289;
}
}
}
}
else
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_282, 0);
lean_inc(x_310);
lean_dec(x_282);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
switch (lean_obj_tag(x_311)) {
case 0:
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_313 = x_311;
} else {
 lean_dec_ref(x_311);
 x_313 = lean_box(0);
}
x_314 = l_Lake_LeanConfig_decodeToml___closed__20;
if (lean_is_scalar(x_313)) {
 x_315 = lean_alloc_ctor(0, 2, 0);
} else {
 x_315 = x_313;
}
lean_ctor_set(x_315, 0, x_312);
lean_ctor_set(x_315, 1, x_314);
x_284 = x_315;
goto block_289;
}
case 2:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_311, 0);
lean_inc(x_316);
lean_dec(x_311);
x_317 = l_Lake_LeanConfig_decodeToml___closed__20;
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_284 = x_318;
goto block_289;
}
case 3:
{
uint8_t x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get_uint8(x_311, sizeof(void*)*1);
lean_dec(x_311);
x_320 = lean_box(x_319);
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_320);
x_12 = x_321;
x_13 = x_11;
goto block_279;
}
default: 
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_322 = lean_ctor_get(x_311, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 x_323 = x_311;
} else {
 lean_dec_ref(x_311);
 x_323 = lean_box(0);
}
x_324 = l_Lake_LeanConfig_decodeToml___closed__20;
if (lean_is_scalar(x_323)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_323;
 lean_ctor_set_tag(x_325, 0);
}
lean_ctor_set(x_325, 0, x_322);
lean_ctor_set(x_325, 1, x_324);
x_284 = x_325;
goto block_289;
}
}
}
}
block_279:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_14 = lean_box(0);
x_268 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_269 = l_Lake_LeanConfig_decodeToml___closed__17;
lean_inc(x_1);
x_270 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_268, x_269, x_1);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; 
x_271 = l_Lake_decodeLeanOptions___closed__1;
x_15 = x_271;
x_16 = x_13;
goto block_267;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_270, 0);
lean_inc(x_272);
lean_dec(x_270);
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
lean_dec(x_272);
x_274 = l_Lake_decodeLeanOptions(x_273);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
lean_dec(x_274);
x_276 = l_Array_append___rarg(x_13, x_275);
lean_dec(x_275);
x_277 = l_Lake_decodeLeanOptions___closed__1;
x_15 = x_277;
x_16 = x_276;
goto block_267;
}
else
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_274, 0);
lean_inc(x_278);
lean_dec(x_274);
x_15 = x_278;
x_16 = x_13;
goto block_267;
}
}
block_267:
{
lean_object* x_17; lean_object* x_18; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_257 = l_Lake_LeanConfig_decodeToml___closed__15;
lean_inc(x_1);
x_258 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_256, x_257, x_1);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; 
x_259 = l_Lake_decodeLeanOptions___closed__1;
x_17 = x_259;
x_18 = x_16;
goto block_255;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_258, 0);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_262 = l_Lake_decodeLeanOptions(x_261);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec(x_262);
x_264 = l_Array_append___rarg(x_16, x_263);
lean_dec(x_263);
x_265 = l_Lake_decodeLeanOptions___closed__1;
x_17 = x_265;
x_18 = x_264;
goto block_255;
}
else
{
lean_object* x_266; 
x_266 = lean_ctor_get(x_262, 0);
lean_inc(x_266);
lean_dec(x_262);
x_17 = x_266;
x_18 = x_16;
goto block_255;
}
}
block_255:
{
lean_object* x_19; lean_object* x_20; lean_object* x_219; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_226 = l_Lake_LeanConfig_decodeToml___closed__2;
lean_inc(x_1);
x_227 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_225, x_226, x_1);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = l_Lake_decodeLeanOptions___closed__1;
x_19 = x_228;
x_20 = x_18;
goto block_218;
}
else
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
switch (lean_obj_tag(x_230)) {
case 0:
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_230, 1);
lean_dec(x_232);
x_233 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_230, 1, x_233);
x_219 = x_230;
goto block_224;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_230, 0);
lean_inc(x_234);
lean_dec(x_230);
x_235 = l_Lake_LeanConfig_decodeToml___closed__5;
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_219 = x_236;
goto block_224;
}
}
case 2:
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_230, 0);
lean_inc(x_237);
lean_dec(x_230);
x_238 = l_Lake_LeanConfig_decodeToml___closed__5;
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_219 = x_239;
goto block_224;
}
case 3:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_230, 0);
lean_inc(x_240);
lean_dec(x_230);
x_241 = l_Lake_LeanConfig_decodeToml___closed__5;
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_219 = x_242;
goto block_224;
}
case 5:
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_230, 1);
lean_inc(x_243);
lean_dec(x_230);
x_244 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_243);
lean_dec(x_243);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
lean_dec(x_244);
x_246 = l_Array_append___rarg(x_18, x_245);
lean_dec(x_245);
x_247 = l_Lake_decodeLeanOptions___closed__1;
x_19 = x_247;
x_20 = x_246;
goto block_218;
}
else
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_244, 0);
lean_inc(x_248);
lean_dec(x_244);
x_19 = x_248;
x_20 = x_18;
goto block_218;
}
}
default: 
{
uint8_t x_249; 
x_249 = !lean_is_exclusive(x_230);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_ctor_get(x_230, 1);
lean_dec(x_250);
x_251 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_230, 0);
lean_ctor_set(x_230, 1, x_251);
x_219 = x_230;
goto block_224;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_230, 0);
lean_inc(x_252);
lean_dec(x_230);
x_253 = l_Lake_LeanConfig_decodeToml___closed__5;
x_254 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_219 = x_254;
goto block_224;
}
}
}
}
block_218:
{
lean_object* x_21; lean_object* x_22; lean_object* x_182; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_189 = l_Lake_LeanConfig_decodeToml___closed__13;
lean_inc(x_1);
x_190 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_188, x_189, x_1);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; 
x_191 = l_Lake_decodeLeanOptions___closed__1;
x_21 = x_191;
x_22 = x_20;
goto block_181;
}
else
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_190, 0);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec(x_192);
switch (lean_obj_tag(x_193)) {
case 0:
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_193, 1);
lean_dec(x_195);
x_196 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_193, 1, x_196);
x_182 = x_193;
goto block_187;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_193, 0);
lean_inc(x_197);
lean_dec(x_193);
x_198 = l_Lake_LeanConfig_decodeToml___closed__5;
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_182 = x_199;
goto block_187;
}
}
case 2:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_193, 0);
lean_inc(x_200);
lean_dec(x_193);
x_201 = l_Lake_LeanConfig_decodeToml___closed__5;
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_182 = x_202;
goto block_187;
}
case 3:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_193, 0);
lean_inc(x_203);
lean_dec(x_193);
x_204 = l_Lake_LeanConfig_decodeToml___closed__5;
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_182 = x_205;
goto block_187;
}
case 5:
{
lean_object* x_206; lean_object* x_207; 
x_206 = lean_ctor_get(x_193, 1);
lean_inc(x_206);
lean_dec(x_193);
x_207 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_206);
lean_dec(x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = l_Array_append___rarg(x_20, x_208);
lean_dec(x_208);
x_210 = l_Lake_decodeLeanOptions___closed__1;
x_21 = x_210;
x_22 = x_209;
goto block_181;
}
else
{
lean_object* x_211; 
x_211 = lean_ctor_get(x_207, 0);
lean_inc(x_211);
lean_dec(x_207);
x_21 = x_211;
x_22 = x_20;
goto block_181;
}
}
default: 
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_193);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_193, 1);
lean_dec(x_213);
x_214 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_193, 0);
lean_ctor_set(x_193, 1, x_214);
x_182 = x_193;
goto block_187;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_193, 0);
lean_inc(x_215);
lean_dec(x_193);
x_216 = l_Lake_LeanConfig_decodeToml___closed__5;
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_182 = x_217;
goto block_187;
}
}
}
}
block_181:
{
lean_object* x_23; lean_object* x_24; lean_object* x_145; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_152 = l_Lake_LeanConfig_decodeToml___closed__11;
lean_inc(x_1);
x_153 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_151, x_152, x_1);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; 
x_154 = l_Lake_decodeLeanOptions___closed__1;
x_23 = x_154;
x_24 = x_22;
goto block_144;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
switch (lean_obj_tag(x_156)) {
case 0:
{
uint8_t x_157; 
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_156, 1);
lean_dec(x_158);
x_159 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_156, 1, x_159);
x_145 = x_156;
goto block_150;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_156, 0);
lean_inc(x_160);
lean_dec(x_156);
x_161 = l_Lake_LeanConfig_decodeToml___closed__5;
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_145 = x_162;
goto block_150;
}
}
case 2:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_156, 0);
lean_inc(x_163);
lean_dec(x_156);
x_164 = l_Lake_LeanConfig_decodeToml___closed__5;
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_145 = x_165;
goto block_150;
}
case 3:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_156, 0);
lean_inc(x_166);
lean_dec(x_156);
x_167 = l_Lake_LeanConfig_decodeToml___closed__5;
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_145 = x_168;
goto block_150;
}
case 5:
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_156, 1);
lean_inc(x_169);
lean_dec(x_156);
x_170 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_169);
lean_dec(x_169);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec(x_170);
x_172 = l_Array_append___rarg(x_22, x_171);
lean_dec(x_171);
x_173 = l_Lake_decodeLeanOptions___closed__1;
x_23 = x_173;
x_24 = x_172;
goto block_144;
}
else
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_170, 0);
lean_inc(x_174);
lean_dec(x_170);
x_23 = x_174;
x_24 = x_22;
goto block_144;
}
}
default: 
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_156);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_156, 1);
lean_dec(x_176);
x_177 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_156, 0);
lean_ctor_set(x_156, 1, x_177);
x_145 = x_156;
goto block_150;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_156, 0);
lean_inc(x_178);
lean_dec(x_156);
x_179 = l_Lake_LeanConfig_decodeToml___closed__5;
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_145 = x_180;
goto block_150;
}
}
}
}
block_144:
{
lean_object* x_25; lean_object* x_26; lean_object* x_108; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_115 = l_Lake_LeanConfig_decodeToml___closed__9;
lean_inc(x_1);
x_116 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_114, x_115, x_1);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = l_Lake_decodeLeanOptions___closed__1;
x_25 = x_117;
x_26 = x_24;
goto block_107;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
switch (lean_obj_tag(x_119)) {
case 0:
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 1);
lean_dec(x_121);
x_122 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_119, 1, x_122);
x_108 = x_119;
goto block_113;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_119, 0);
lean_inc(x_123);
lean_dec(x_119);
x_124 = l_Lake_LeanConfig_decodeToml___closed__5;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_108 = x_125;
goto block_113;
}
}
case 2:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_119, 0);
lean_inc(x_126);
lean_dec(x_119);
x_127 = l_Lake_LeanConfig_decodeToml___closed__5;
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
x_108 = x_128;
goto block_113;
}
case 3:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_119, 0);
lean_inc(x_129);
lean_dec(x_119);
x_130 = l_Lake_LeanConfig_decodeToml___closed__5;
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_108 = x_131;
goto block_113;
}
case 5:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_119, 1);
lean_inc(x_132);
lean_dec(x_119);
x_133 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_132);
lean_dec(x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec(x_133);
x_135 = l_Array_append___rarg(x_24, x_134);
lean_dec(x_134);
x_136 = l_Lake_decodeLeanOptions___closed__1;
x_25 = x_136;
x_26 = x_135;
goto block_107;
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
lean_dec(x_133);
x_25 = x_137;
x_26 = x_24;
goto block_107;
}
}
default: 
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_119);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_119, 1);
lean_dec(x_139);
x_140 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_119, 0);
lean_ctor_set(x_119, 1, x_140);
x_108 = x_119;
goto block_113;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_119, 0);
lean_inc(x_141);
lean_dec(x_119);
x_142 = l_Lake_LeanConfig_decodeToml___closed__5;
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_108 = x_143;
goto block_113;
}
}
}
}
block_107:
{
lean_object* x_27; lean_object* x_28; lean_object* x_71; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_78 = l_Lake_LeanConfig_decodeToml___closed__7;
lean_inc(x_1);
x_79 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_77, x_78, x_1);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = l_Lake_decodeLeanOptions___closed__1;
x_27 = x_80;
x_28 = x_26;
goto block_70;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
switch (lean_obj_tag(x_82)) {
case 0:
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 1);
lean_dec(x_84);
x_85 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_82, 1, x_85);
x_71 = x_82;
goto block_76;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = l_Lake_LeanConfig_decodeToml___closed__5;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_71 = x_88;
goto block_76;
}
}
case 2:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
lean_dec(x_82);
x_90 = l_Lake_LeanConfig_decodeToml___closed__5;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_71 = x_91;
goto block_76;
}
case 3:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_82, 0);
lean_inc(x_92);
lean_dec(x_82);
x_93 = l_Lake_LeanConfig_decodeToml___closed__5;
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_71 = x_94;
goto block_76;
}
case 5:
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_82, 1);
lean_inc(x_95);
lean_dec(x_82);
x_96 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_95);
lean_dec(x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Array_append___rarg(x_26, x_97);
lean_dec(x_97);
x_99 = l_Lake_decodeLeanOptions___closed__1;
x_27 = x_99;
x_28 = x_98;
goto block_70;
}
else
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_96, 0);
lean_inc(x_100);
lean_dec(x_96);
x_27 = x_100;
x_28 = x_26;
goto block_70;
}
}
default: 
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_82);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_82, 1);
lean_dec(x_102);
x_103 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_82, 0);
lean_ctor_set(x_82, 1, x_103);
x_71 = x_82;
goto block_76;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_82, 0);
lean_inc(x_104);
lean_dec(x_82);
x_105 = l_Lake_LeanConfig_decodeToml___closed__5;
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_71 = x_106;
goto block_76;
}
}
}
}
block_70:
{
lean_object* x_29; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_37 = l_Lake_LeanConfig_decodeToml___closed__4;
x_38 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_36, x_37, x_1);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lake_decodeLeanOptions___closed__1;
x_40 = lean_alloc_ctor(0, 11, 2);
lean_ctor_set(x_40, 0, x_15);
lean_ctor_set(x_40, 1, x_19);
lean_ctor_set(x_40, 2, x_21);
lean_ctor_set(x_40, 3, x_23);
lean_ctor_set(x_40, 4, x_17);
lean_ctor_set(x_40, 5, x_25);
lean_ctor_set(x_40, 6, x_27);
lean_ctor_set(x_40, 7, x_39);
lean_ctor_set(x_40, 8, x_12);
lean_ctor_set(x_40, 9, x_39);
lean_ctor_set(x_40, 10, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*11, x_8);
lean_ctor_set_uint8(x_40, sizeof(void*)*11 + 1, x_10);
x_2 = x_40;
x_3 = x_28;
goto block_7;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
switch (lean_obj_tag(x_42)) {
case 0:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 1);
lean_dec(x_44);
x_45 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_42, 1, x_45);
x_29 = x_42;
goto block_35;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_Lake_LeanConfig_decodeToml___closed__5;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_29 = x_48;
goto block_35;
}
}
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = l_Lake_LeanConfig_decodeToml___closed__5;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_29 = x_51;
goto block_35;
}
case 3:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_42, 0);
lean_inc(x_52);
lean_dec(x_42);
x_53 = l_Lake_LeanConfig_decodeToml___closed__5;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_29 = x_54;
goto block_35;
}
case 5:
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_42, 1);
lean_inc(x_55);
lean_dec(x_42);
x_56 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_55);
lean_dec(x_55);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Array_append___rarg(x_28, x_57);
lean_dec(x_57);
x_59 = l_Lake_decodeLeanOptions___closed__1;
x_60 = lean_alloc_ctor(0, 11, 2);
lean_ctor_set(x_60, 0, x_15);
lean_ctor_set(x_60, 1, x_19);
lean_ctor_set(x_60, 2, x_21);
lean_ctor_set(x_60, 3, x_23);
lean_ctor_set(x_60, 4, x_17);
lean_ctor_set(x_60, 5, x_25);
lean_ctor_set(x_60, 6, x_27);
lean_ctor_set(x_60, 7, x_59);
lean_ctor_set(x_60, 8, x_12);
lean_ctor_set(x_60, 9, x_59);
lean_ctor_set(x_60, 10, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*11, x_8);
lean_ctor_set_uint8(x_60, sizeof(void*)*11 + 1, x_10);
x_2 = x_60;
x_3 = x_58;
goto block_7;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = l_Lake_decodeLeanOptions___closed__1;
x_63 = lean_alloc_ctor(0, 11, 2);
lean_ctor_set(x_63, 0, x_15);
lean_ctor_set(x_63, 1, x_19);
lean_ctor_set(x_63, 2, x_21);
lean_ctor_set(x_63, 3, x_23);
lean_ctor_set(x_63, 4, x_17);
lean_ctor_set(x_63, 5, x_25);
lean_ctor_set(x_63, 6, x_27);
lean_ctor_set(x_63, 7, x_61);
lean_ctor_set(x_63, 8, x_12);
lean_ctor_set(x_63, 9, x_62);
lean_ctor_set(x_63, 10, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*11, x_8);
lean_ctor_set_uint8(x_63, sizeof(void*)*11 + 1, x_10);
x_2 = x_63;
x_3 = x_28;
goto block_7;
}
}
default: 
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_42);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_42, 1);
lean_dec(x_65);
x_66 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 1, x_66);
x_29 = x_42;
goto block_35;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_42, 0);
lean_inc(x_67);
lean_dec(x_42);
x_68 = l_Lake_LeanConfig_decodeToml___closed__5;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_29 = x_69;
goto block_35;
}
}
}
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
x_31 = lean_array_mk(x_30);
x_32 = l_Array_append___rarg(x_28, x_31);
lean_dec(x_31);
x_33 = l_Lake_decodeLeanOptions___closed__1;
x_34 = lean_alloc_ctor(0, 11, 2);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_19);
lean_ctor_set(x_34, 2, x_21);
lean_ctor_set(x_34, 3, x_23);
lean_ctor_set(x_34, 4, x_17);
lean_ctor_set(x_34, 5, x_25);
lean_ctor_set(x_34, 6, x_27);
lean_ctor_set(x_34, 7, x_33);
lean_ctor_set(x_34, 8, x_12);
lean_ctor_set(x_34, 9, x_33);
lean_ctor_set(x_34, 10, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*11, x_8);
lean_ctor_set_uint8(x_34, sizeof(void*)*11 + 1, x_10);
x_2 = x_34;
x_3 = x_32;
goto block_7;
}
}
block_76:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_14);
x_73 = lean_array_mk(x_72);
x_74 = l_Array_append___rarg(x_26, x_73);
lean_dec(x_73);
x_75 = l_Lake_decodeLeanOptions___closed__1;
x_27 = x_75;
x_28 = x_74;
goto block_70;
}
}
block_113:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_14);
x_110 = lean_array_mk(x_109);
x_111 = l_Array_append___rarg(x_24, x_110);
lean_dec(x_110);
x_112 = l_Lake_decodeLeanOptions___closed__1;
x_25 = x_112;
x_26 = x_111;
goto block_107;
}
}
block_150:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_14);
x_147 = lean_array_mk(x_146);
x_148 = l_Array_append___rarg(x_22, x_147);
lean_dec(x_147);
x_149 = l_Lake_decodeLeanOptions___closed__1;
x_23 = x_149;
x_24 = x_148;
goto block_144;
}
}
block_187:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_14);
x_184 = lean_array_mk(x_183);
x_185 = l_Array_append___rarg(x_20, x_184);
lean_dec(x_184);
x_186 = l_Lake_decodeLeanOptions___closed__1;
x_21 = x_186;
x_22 = x_185;
goto block_181;
}
}
block_224:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_14);
x_221 = lean_array_mk(x_220);
x_222 = l_Array_append___rarg(x_18, x_221);
lean_dec(x_221);
x_223 = l_Lake_decodeLeanOptions___closed__1;
x_19 = x_223;
x_20 = x_222;
goto block_218;
}
}
}
}
block_289:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_box(0);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_array_mk(x_286);
x_288 = l_Array_append___rarg(x_11, x_287);
lean_dec(x_287);
x_12 = x_283;
x_13 = x_288;
goto block_279;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanConfig___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_1, 1, x_10);
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_2 = x_13;
goto block_7;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
goto block_7;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_19;
goto block_7;
}
case 6:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lake_LeanConfig_decodeToml(x_20);
return x_21;
}
default: 
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_24);
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_2 = x_27;
goto block_7;
}
}
}
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_mk(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lake_instDecodeTomlLeanConfig___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instDecodeTomlLeanConfig___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instDecodeTomlLeanConfig() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instDecodeTomlLeanConfig___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_PackageConfig_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_21 = l_Lake_mergeErrors___rarg(x_4, x_19, x_20);
x_2 = x_8;
x_4 = x_21;
goto _start;
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_23);
lean_dec(x_6);
x_24 = l_Lake_Glob_decodeToml___closed__2;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_9 = x_25;
goto block_17;
}
case 3:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_6, 0);
lean_inc(x_26);
lean_dec(x_6);
x_27 = l_Lake_Glob_decodeToml___closed__2;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_9 = x_28;
goto block_17;
}
default: 
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_6);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_6, 1);
lean_dec(x_30);
x_31 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_31);
x_9 = x_6;
goto block_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
lean_dec(x_6);
x_33 = l_Lake_Glob_decodeToml___closed__2;
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_9 = x_34;
goto block_17;
}
}
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_mk(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_15 = l_Lake_mergeErrors___rarg(x_4, x_13, x_14);
x_2 = x_8;
x_4 = x_15;
goto _start;
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
x_5 = lean_alloc_ctor(0, 11, 2);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_3);
lean_ctor_set(x_5, 4, x_3);
lean_ctor_set(x_5, 5, x_3);
lean_ctor_set(x_5, 6, x_3);
lean_ctor_set(x_5, 7, x_3);
lean_ctor_set(x_5, 8, x_1);
lean_ctor_set(x_5, 9, x_3);
lean_ctor_set(x_5, 10, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*11, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*11 + 1, x_4);
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
x_1 = lean_mk_string_unchecked("README.md", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("readmeFile", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__11;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
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
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__59() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("srcDir", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_PackageConfig_decodeToml___closed__60() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_PackageConfig_decodeToml___closed__59;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
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
lean_object* x_3; lean_object* x_4; uint8_t x_9; lean_object* x_10; lean_object* x_794; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_802 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_803 = l_Lake_PackageConfig_decodeToml___closed__62;
lean_inc(x_2);
x_804 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_802, x_803, x_2);
if (lean_obj_tag(x_804) == 0)
{
uint8_t x_805; lean_object* x_806; 
x_805 = 0;
x_806 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_805;
x_10 = x_806;
goto block_793;
}
else
{
lean_object* x_807; lean_object* x_808; 
x_807 = lean_ctor_get(x_804, 0);
lean_inc(x_807);
lean_dec(x_804);
x_808 = lean_ctor_get(x_807, 1);
lean_inc(x_808);
lean_dec(x_807);
switch (lean_obj_tag(x_808)) {
case 0:
{
uint8_t x_809; 
x_809 = !lean_is_exclusive(x_808);
if (x_809 == 0)
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_ctor_get(x_808, 1);
lean_dec(x_810);
x_811 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_808, 1, x_811);
x_794 = x_808;
goto block_801;
}
else
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_808, 0);
lean_inc(x_812);
lean_dec(x_808);
x_813 = l_Lake_LeanConfig_decodeToml___closed__20;
x_814 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_814, 0, x_812);
lean_ctor_set(x_814, 1, x_813);
x_794 = x_814;
goto block_801;
}
}
case 2:
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_815 = lean_ctor_get(x_808, 0);
lean_inc(x_815);
lean_dec(x_808);
x_816 = l_Lake_LeanConfig_decodeToml___closed__20;
x_817 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_817, 0, x_815);
lean_ctor_set(x_817, 1, x_816);
x_794 = x_817;
goto block_801;
}
case 3:
{
uint8_t x_818; lean_object* x_819; 
x_818 = lean_ctor_get_uint8(x_808, sizeof(void*)*1);
lean_dec(x_808);
x_819 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_818;
x_10 = x_819;
goto block_793;
}
default: 
{
uint8_t x_820; 
x_820 = !lean_is_exclusive(x_808);
if (x_820 == 0)
{
lean_object* x_821; lean_object* x_822; 
x_821 = lean_ctor_get(x_808, 1);
lean_dec(x_821);
x_822 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_808, 0);
lean_ctor_set(x_808, 1, x_822);
x_794 = x_808;
goto block_801;
}
else
{
lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_823 = lean_ctor_get(x_808, 0);
lean_inc(x_823);
lean_dec(x_808);
x_824 = l_Lake_LeanConfig_decodeToml___closed__20;
x_825 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_825, 0, x_823);
lean_ctor_set(x_825, 1, x_824);
x_794 = x_825;
goto block_801;
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
block_793:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_757; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
x_11 = lean_box(0);
x_763 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_764 = l_Lake_PackageConfig_decodeToml___closed__2;
lean_inc(x_2);
x_765 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_763, x_764, x_2);
if (lean_obj_tag(x_765) == 0)
{
lean_object* x_766; 
x_766 = l_Lake_decodeLeanOptions___closed__1;
x_12 = x_766;
x_13 = x_10;
goto block_756;
}
else
{
lean_object* x_767; lean_object* x_768; 
x_767 = lean_ctor_get(x_765, 0);
lean_inc(x_767);
lean_dec(x_765);
x_768 = lean_ctor_get(x_767, 1);
lean_inc(x_768);
lean_dec(x_767);
switch (lean_obj_tag(x_768)) {
case 0:
{
uint8_t x_769; 
x_769 = !lean_is_exclusive(x_768);
if (x_769 == 0)
{
lean_object* x_770; lean_object* x_771; 
x_770 = lean_ctor_get(x_768, 1);
lean_dec(x_770);
x_771 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_768, 1, x_771);
x_757 = x_768;
goto block_762;
}
else
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; 
x_772 = lean_ctor_get(x_768, 0);
lean_inc(x_772);
lean_dec(x_768);
x_773 = l_Lake_LeanConfig_decodeToml___closed__5;
x_774 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_774, 0, x_772);
lean_ctor_set(x_774, 1, x_773);
x_757 = x_774;
goto block_762;
}
}
case 2:
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_775 = lean_ctor_get(x_768, 0);
lean_inc(x_775);
lean_dec(x_768);
x_776 = l_Lake_LeanConfig_decodeToml___closed__5;
x_777 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_777, 0, x_775);
lean_ctor_set(x_777, 1, x_776);
x_757 = x_777;
goto block_762;
}
case 3:
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_768, 0);
lean_inc(x_778);
lean_dec(x_768);
x_779 = l_Lake_LeanConfig_decodeToml___closed__5;
x_780 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
x_757 = x_780;
goto block_762;
}
case 5:
{
lean_object* x_781; lean_object* x_782; 
x_781 = lean_ctor_get(x_768, 1);
lean_inc(x_781);
lean_dec(x_768);
x_782 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_781);
lean_dec(x_781);
if (lean_obj_tag(x_782) == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
lean_dec(x_782);
x_784 = l_Array_append___rarg(x_10, x_783);
lean_dec(x_783);
x_785 = l_Lake_decodeLeanOptions___closed__1;
x_12 = x_785;
x_13 = x_784;
goto block_756;
}
else
{
lean_object* x_786; 
x_786 = lean_ctor_get(x_782, 0);
lean_inc(x_786);
lean_dec(x_782);
x_12 = x_786;
x_13 = x_10;
goto block_756;
}
}
default: 
{
uint8_t x_787; 
x_787 = !lean_is_exclusive(x_768);
if (x_787 == 0)
{
lean_object* x_788; lean_object* x_789; 
x_788 = lean_ctor_get(x_768, 1);
lean_dec(x_788);
x_789 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_768, 0);
lean_ctor_set(x_768, 1, x_789);
x_757 = x_768;
goto block_762;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_768, 0);
lean_inc(x_790);
lean_dec(x_768);
x_791 = l_Lake_LeanConfig_decodeToml___closed__5;
x_792 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_792, 0, x_790);
lean_ctor_set(x_792, 1, x_791);
x_757 = x_792;
goto block_762;
}
}
}
}
block_756:
{
lean_object* x_14; lean_object* x_15; lean_object* x_731; lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_738 = l_Lake_PackageConfig_decodeToml___closed__60;
lean_inc(x_2);
x_739 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_737, x_738, x_2);
if (lean_obj_tag(x_739) == 0)
{
lean_object* x_740; 
x_740 = l_Lake_PackageConfig_decodeToml___closed__58;
x_14 = x_740;
x_15 = x_13;
goto block_730;
}
else
{
lean_object* x_741; lean_object* x_742; 
x_741 = lean_ctor_get(x_739, 0);
lean_inc(x_741);
lean_dec(x_739);
x_742 = lean_ctor_get(x_741, 1);
lean_inc(x_742);
lean_dec(x_741);
switch (lean_obj_tag(x_742)) {
case 0:
{
lean_object* x_743; 
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
lean_dec(x_742);
x_14 = x_743;
x_15 = x_13;
goto block_730;
}
case 2:
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_744 = lean_ctor_get(x_742, 0);
lean_inc(x_744);
lean_dec(x_742);
x_745 = l_Lake_Glob_decodeToml___closed__2;
x_746 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_746, 0, x_744);
lean_ctor_set(x_746, 1, x_745);
x_731 = x_746;
goto block_736;
}
case 3:
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_747 = lean_ctor_get(x_742, 0);
lean_inc(x_747);
lean_dec(x_742);
x_748 = l_Lake_Glob_decodeToml___closed__2;
x_749 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_749, 0, x_747);
lean_ctor_set(x_749, 1, x_748);
x_731 = x_749;
goto block_736;
}
default: 
{
uint8_t x_750; 
x_750 = !lean_is_exclusive(x_742);
if (x_750 == 0)
{
lean_object* x_751; lean_object* x_752; 
x_751 = lean_ctor_get(x_742, 1);
lean_dec(x_751);
x_752 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_742, 0);
lean_ctor_set(x_742, 1, x_752);
x_731 = x_742;
goto block_736;
}
else
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_742, 0);
lean_inc(x_753);
lean_dec(x_742);
x_754 = l_Lake_Glob_decodeToml___closed__2;
x_755 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_755, 0, x_753);
lean_ctor_set(x_755, 1, x_754);
x_731 = x_755;
goto block_736;
}
}
}
}
block_730:
{
lean_object* x_16; lean_object* x_17; lean_object* x_705; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_712 = l_Lake_PackageConfig_decodeToml___closed__57;
lean_inc(x_2);
x_713 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_711, x_712, x_2);
if (lean_obj_tag(x_713) == 0)
{
lean_object* x_714; 
x_714 = l_Lake_defaultBuildDir;
x_16 = x_714;
x_17 = x_15;
goto block_704;
}
else
{
lean_object* x_715; lean_object* x_716; 
x_715 = lean_ctor_get(x_713, 0);
lean_inc(x_715);
lean_dec(x_713);
x_716 = lean_ctor_get(x_715, 1);
lean_inc(x_716);
lean_dec(x_715);
switch (lean_obj_tag(x_716)) {
case 0:
{
lean_object* x_717; 
x_717 = lean_ctor_get(x_716, 1);
lean_inc(x_717);
lean_dec(x_716);
x_16 = x_717;
x_17 = x_15;
goto block_704;
}
case 2:
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_716, 0);
lean_inc(x_718);
lean_dec(x_716);
x_719 = l_Lake_Glob_decodeToml___closed__2;
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
x_705 = x_720;
goto block_710;
}
case 3:
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_716, 0);
lean_inc(x_721);
lean_dec(x_716);
x_722 = l_Lake_Glob_decodeToml___closed__2;
x_723 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set(x_723, 1, x_722);
x_705 = x_723;
goto block_710;
}
default: 
{
uint8_t x_724; 
x_724 = !lean_is_exclusive(x_716);
if (x_724 == 0)
{
lean_object* x_725; lean_object* x_726; 
x_725 = lean_ctor_get(x_716, 1);
lean_dec(x_725);
x_726 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_716, 0);
lean_ctor_set(x_716, 1, x_726);
x_705 = x_716;
goto block_710;
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_727 = lean_ctor_get(x_716, 0);
lean_inc(x_727);
lean_dec(x_716);
x_728 = l_Lake_Glob_decodeToml___closed__2;
x_729 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_729, 0, x_727);
lean_ctor_set(x_729, 1, x_728);
x_705 = x_729;
goto block_710;
}
}
}
}
block_704:
{
lean_object* x_18; lean_object* x_19; lean_object* x_679; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_685 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_686 = l_Lake_PackageConfig_decodeToml___closed__55;
lean_inc(x_2);
x_687 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_685, x_686, x_2);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; 
x_688 = l_Lake_defaultLeanLibDir;
x_18 = x_688;
x_19 = x_17;
goto block_678;
}
else
{
lean_object* x_689; lean_object* x_690; 
x_689 = lean_ctor_get(x_687, 0);
lean_inc(x_689);
lean_dec(x_687);
x_690 = lean_ctor_get(x_689, 1);
lean_inc(x_690);
lean_dec(x_689);
switch (lean_obj_tag(x_690)) {
case 0:
{
lean_object* x_691; 
x_691 = lean_ctor_get(x_690, 1);
lean_inc(x_691);
lean_dec(x_690);
x_18 = x_691;
x_19 = x_17;
goto block_678;
}
case 2:
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; 
x_692 = lean_ctor_get(x_690, 0);
lean_inc(x_692);
lean_dec(x_690);
x_693 = l_Lake_Glob_decodeToml___closed__2;
x_694 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_694, 0, x_692);
lean_ctor_set(x_694, 1, x_693);
x_679 = x_694;
goto block_684;
}
case 3:
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_695 = lean_ctor_get(x_690, 0);
lean_inc(x_695);
lean_dec(x_690);
x_696 = l_Lake_Glob_decodeToml___closed__2;
x_697 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
x_679 = x_697;
goto block_684;
}
default: 
{
uint8_t x_698; 
x_698 = !lean_is_exclusive(x_690);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; 
x_699 = lean_ctor_get(x_690, 1);
lean_dec(x_699);
x_700 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_690, 0);
lean_ctor_set(x_690, 1, x_700);
x_679 = x_690;
goto block_684;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_690, 0);
lean_inc(x_701);
lean_dec(x_690);
x_702 = l_Lake_Glob_decodeToml___closed__2;
x_703 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set(x_703, 1, x_702);
x_679 = x_703;
goto block_684;
}
}
}
}
block_678:
{
lean_object* x_20; lean_object* x_21; lean_object* x_653; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_660 = l_Lake_PackageConfig_decodeToml___closed__53;
lean_inc(x_2);
x_661 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_659, x_660, x_2);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; 
x_662 = l_Lake_defaultNativeLibDir;
x_20 = x_662;
x_21 = x_19;
goto block_652;
}
else
{
lean_object* x_663; lean_object* x_664; 
x_663 = lean_ctor_get(x_661, 0);
lean_inc(x_663);
lean_dec(x_661);
x_664 = lean_ctor_get(x_663, 1);
lean_inc(x_664);
lean_dec(x_663);
switch (lean_obj_tag(x_664)) {
case 0:
{
lean_object* x_665; 
x_665 = lean_ctor_get(x_664, 1);
lean_inc(x_665);
lean_dec(x_664);
x_20 = x_665;
x_21 = x_19;
goto block_652;
}
case 2:
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_664, 0);
lean_inc(x_666);
lean_dec(x_664);
x_667 = l_Lake_Glob_decodeToml___closed__2;
x_668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
x_653 = x_668;
goto block_658;
}
case 3:
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_664, 0);
lean_inc(x_669);
lean_dec(x_664);
x_670 = l_Lake_Glob_decodeToml___closed__2;
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
x_653 = x_671;
goto block_658;
}
default: 
{
uint8_t x_672; 
x_672 = !lean_is_exclusive(x_664);
if (x_672 == 0)
{
lean_object* x_673; lean_object* x_674; 
x_673 = lean_ctor_get(x_664, 1);
lean_dec(x_673);
x_674 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_664, 0);
lean_ctor_set(x_664, 1, x_674);
x_653 = x_664;
goto block_658;
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_675 = lean_ctor_get(x_664, 0);
lean_inc(x_675);
lean_dec(x_664);
x_676 = l_Lake_Glob_decodeToml___closed__2;
x_677 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_677, 0, x_675);
lean_ctor_set(x_677, 1, x_676);
x_653 = x_677;
goto block_658;
}
}
}
}
block_652:
{
lean_object* x_22; lean_object* x_23; lean_object* x_627; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_634 = l_Lake_PackageConfig_decodeToml___closed__51;
lean_inc(x_2);
x_635 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_633, x_634, x_2);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; 
x_636 = l_Lake_defaultBinDir;
x_22 = x_636;
x_23 = x_21;
goto block_626;
}
else
{
lean_object* x_637; lean_object* x_638; 
x_637 = lean_ctor_get(x_635, 0);
lean_inc(x_637);
lean_dec(x_635);
x_638 = lean_ctor_get(x_637, 1);
lean_inc(x_638);
lean_dec(x_637);
switch (lean_obj_tag(x_638)) {
case 0:
{
lean_object* x_639; 
x_639 = lean_ctor_get(x_638, 1);
lean_inc(x_639);
lean_dec(x_638);
x_22 = x_639;
x_23 = x_21;
goto block_626;
}
case 2:
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_638, 0);
lean_inc(x_640);
lean_dec(x_638);
x_641 = l_Lake_Glob_decodeToml___closed__2;
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
x_627 = x_642;
goto block_632;
}
case 3:
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_638, 0);
lean_inc(x_643);
lean_dec(x_638);
x_644 = l_Lake_Glob_decodeToml___closed__2;
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_643);
lean_ctor_set(x_645, 1, x_644);
x_627 = x_645;
goto block_632;
}
default: 
{
uint8_t x_646; 
x_646 = !lean_is_exclusive(x_638);
if (x_646 == 0)
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_638, 1);
lean_dec(x_647);
x_648 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_638, 0);
lean_ctor_set(x_638, 1, x_648);
x_627 = x_638;
goto block_632;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_638, 0);
lean_inc(x_649);
lean_dec(x_638);
x_650 = l_Lake_Glob_decodeToml___closed__2;
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
x_627 = x_651;
goto block_632;
}
}
}
}
block_626:
{
lean_object* x_24; lean_object* x_25; lean_object* x_601; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_608 = l_Lake_PackageConfig_decodeToml___closed__49;
lean_inc(x_2);
x_609 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_607, x_608, x_2);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; 
x_610 = l_Lake_defaultIrDir;
x_24 = x_610;
x_25 = x_23;
goto block_600;
}
else
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_ctor_get(x_609, 0);
lean_inc(x_611);
lean_dec(x_609);
x_612 = lean_ctor_get(x_611, 1);
lean_inc(x_612);
lean_dec(x_611);
switch (lean_obj_tag(x_612)) {
case 0:
{
lean_object* x_613; 
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
lean_dec(x_612);
x_24 = x_613;
x_25 = x_23;
goto block_600;
}
case 2:
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_612, 0);
lean_inc(x_614);
lean_dec(x_612);
x_615 = l_Lake_Glob_decodeToml___closed__2;
x_616 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
x_601 = x_616;
goto block_606;
}
case 3:
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_612, 0);
lean_inc(x_617);
lean_dec(x_612);
x_618 = l_Lake_Glob_decodeToml___closed__2;
x_619 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_618);
x_601 = x_619;
goto block_606;
}
default: 
{
uint8_t x_620; 
x_620 = !lean_is_exclusive(x_612);
if (x_620 == 0)
{
lean_object* x_621; lean_object* x_622; 
x_621 = lean_ctor_get(x_612, 1);
lean_dec(x_621);
x_622 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_612, 0);
lean_ctor_set(x_612, 1, x_622);
x_601 = x_612;
goto block_606;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_612, 0);
lean_inc(x_623);
lean_dec(x_612);
x_624 = l_Lake_Glob_decodeToml___closed__2;
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
x_601 = x_625;
goto block_606;
}
}
}
}
block_600:
{
lean_object* x_26; lean_object* x_27; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_561 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_562 = l_Lake_PackageConfig_decodeToml___closed__47;
lean_inc(x_2);
x_563 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_561, x_562, x_2);
x_564 = lean_box(0);
if (lean_obj_tag(x_563) == 0)
{
x_26 = x_564;
x_27 = x_25;
goto block_560;
}
else
{
uint8_t x_570; 
x_570 = !lean_is_exclusive(x_563);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; 
x_571 = lean_ctor_get(x_563, 0);
x_572 = lean_ctor_get(x_571, 1);
lean_inc(x_572);
lean_dec(x_571);
switch (lean_obj_tag(x_572)) {
case 0:
{
lean_object* x_573; 
x_573 = lean_ctor_get(x_572, 1);
lean_inc(x_573);
lean_dec(x_572);
lean_ctor_set(x_563, 0, x_573);
x_26 = x_563;
x_27 = x_25;
goto block_560;
}
case 2:
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_free_object(x_563);
x_574 = lean_ctor_get(x_572, 0);
lean_inc(x_574);
lean_dec(x_572);
x_575 = l_Lake_Glob_decodeToml___closed__2;
x_576 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_576, 0, x_574);
lean_ctor_set(x_576, 1, x_575);
x_565 = x_576;
goto block_569;
}
case 3:
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_free_object(x_563);
x_577 = lean_ctor_get(x_572, 0);
lean_inc(x_577);
lean_dec(x_572);
x_578 = l_Lake_Glob_decodeToml___closed__2;
x_579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_579, 0, x_577);
lean_ctor_set(x_579, 1, x_578);
x_565 = x_579;
goto block_569;
}
default: 
{
uint8_t x_580; 
lean_free_object(x_563);
x_580 = !lean_is_exclusive(x_572);
if (x_580 == 0)
{
lean_object* x_581; lean_object* x_582; 
x_581 = lean_ctor_get(x_572, 1);
lean_dec(x_581);
x_582 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_572, 0);
lean_ctor_set(x_572, 1, x_582);
x_565 = x_572;
goto block_569;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_572, 0);
lean_inc(x_583);
lean_dec(x_572);
x_584 = l_Lake_Glob_decodeToml___closed__2;
x_585 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
x_565 = x_585;
goto block_569;
}
}
}
}
else
{
lean_object* x_586; lean_object* x_587; 
x_586 = lean_ctor_get(x_563, 0);
lean_inc(x_586);
lean_dec(x_563);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
lean_dec(x_586);
switch (lean_obj_tag(x_587)) {
case 0:
{
lean_object* x_588; lean_object* x_589; 
x_588 = lean_ctor_get(x_587, 1);
lean_inc(x_588);
lean_dec(x_587);
x_589 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_589, 0, x_588);
x_26 = x_589;
x_27 = x_25;
goto block_560;
}
case 2:
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_587, 0);
lean_inc(x_590);
lean_dec(x_587);
x_591 = l_Lake_Glob_decodeToml___closed__2;
x_592 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
x_565 = x_592;
goto block_569;
}
case 3:
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_587, 0);
lean_inc(x_593);
lean_dec(x_587);
x_594 = l_Lake_Glob_decodeToml___closed__2;
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_593);
lean_ctor_set(x_595, 1, x_594);
x_565 = x_595;
goto block_569;
}
default: 
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_596 = lean_ctor_get(x_587, 0);
lean_inc(x_596);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_597 = x_587;
} else {
 lean_dec_ref(x_587);
 x_597 = lean_box(0);
}
x_598 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_597)) {
 x_599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_599 = x_597;
 lean_ctor_set_tag(x_599, 0);
}
lean_ctor_set(x_599, 0, x_596);
lean_ctor_set(x_599, 1, x_598);
x_565 = x_599;
goto block_569;
}
}
}
}
block_560:
{
lean_object* x_28; lean_object* x_29; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_521 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_522 = l_Lake_PackageConfig_decodeToml___closed__45;
lean_inc(x_2);
x_523 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_521, x_522, x_2);
x_524 = lean_box(0);
if (lean_obj_tag(x_523) == 0)
{
x_28 = x_524;
x_29 = x_27;
goto block_520;
}
else
{
uint8_t x_530; 
x_530 = !lean_is_exclusive(x_523);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; 
x_531 = lean_ctor_get(x_523, 0);
x_532 = lean_ctor_get(x_531, 1);
lean_inc(x_532);
lean_dec(x_531);
switch (lean_obj_tag(x_532)) {
case 0:
{
lean_object* x_533; 
x_533 = lean_ctor_get(x_532, 1);
lean_inc(x_533);
lean_dec(x_532);
lean_ctor_set(x_523, 0, x_533);
x_28 = x_523;
x_29 = x_27;
goto block_520;
}
case 2:
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
lean_free_object(x_523);
x_534 = lean_ctor_get(x_532, 0);
lean_inc(x_534);
lean_dec(x_532);
x_535 = l_Lake_Glob_decodeToml___closed__2;
x_536 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_536, 0, x_534);
lean_ctor_set(x_536, 1, x_535);
x_525 = x_536;
goto block_529;
}
case 3:
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_free_object(x_523);
x_537 = lean_ctor_get(x_532, 0);
lean_inc(x_537);
lean_dec(x_532);
x_538 = l_Lake_Glob_decodeToml___closed__2;
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_537);
lean_ctor_set(x_539, 1, x_538);
x_525 = x_539;
goto block_529;
}
default: 
{
uint8_t x_540; 
lean_free_object(x_523);
x_540 = !lean_is_exclusive(x_532);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; 
x_541 = lean_ctor_get(x_532, 1);
lean_dec(x_541);
x_542 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_532, 0);
lean_ctor_set(x_532, 1, x_542);
x_525 = x_532;
goto block_529;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_532, 0);
lean_inc(x_543);
lean_dec(x_532);
x_544 = l_Lake_Glob_decodeToml___closed__2;
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
x_525 = x_545;
goto block_529;
}
}
}
}
else
{
lean_object* x_546; lean_object* x_547; 
x_546 = lean_ctor_get(x_523, 0);
lean_inc(x_546);
lean_dec(x_523);
x_547 = lean_ctor_get(x_546, 1);
lean_inc(x_547);
lean_dec(x_546);
switch (lean_obj_tag(x_547)) {
case 0:
{
lean_object* x_548; lean_object* x_549; 
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
lean_dec(x_547);
x_549 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_549, 0, x_548);
x_28 = x_549;
x_29 = x_27;
goto block_520;
}
case 2:
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_547, 0);
lean_inc(x_550);
lean_dec(x_547);
x_551 = l_Lake_Glob_decodeToml___closed__2;
x_552 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
x_525 = x_552;
goto block_529;
}
case 3:
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_547, 0);
lean_inc(x_553);
lean_dec(x_547);
x_554 = l_Lake_Glob_decodeToml___closed__2;
x_555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
x_525 = x_555;
goto block_529;
}
default: 
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_556 = lean_ctor_get(x_547, 0);
lean_inc(x_556);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_557 = x_547;
} else {
 lean_dec_ref(x_547);
 x_557 = lean_box(0);
}
x_558 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_557)) {
 x_559 = lean_alloc_ctor(0, 2, 0);
} else {
 x_559 = x_557;
 lean_ctor_set_tag(x_559, 0);
}
lean_ctor_set(x_559, 0, x_556);
lean_ctor_set(x_559, 1, x_558);
x_525 = x_559;
goto block_529;
}
}
}
}
block_520:
{
uint8_t x_30; lean_object* x_31; lean_object* x_492; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_499 = l_Lake_PackageConfig_decodeToml___closed__43;
lean_inc(x_2);
x_500 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_498, x_499, x_2);
if (lean_obj_tag(x_500) == 0)
{
uint8_t x_501; 
x_501 = 0;
x_30 = x_501;
x_31 = x_29;
goto block_491;
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_ctor_get(x_500, 0);
lean_inc(x_502);
lean_dec(x_500);
x_503 = lean_ctor_get(x_502, 1);
lean_inc(x_503);
lean_dec(x_502);
switch (lean_obj_tag(x_503)) {
case 0:
{
uint8_t x_504; 
x_504 = !lean_is_exclusive(x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
x_505 = lean_ctor_get(x_503, 1);
lean_dec(x_505);
x_506 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_503, 1, x_506);
x_492 = x_503;
goto block_497;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_507 = lean_ctor_get(x_503, 0);
lean_inc(x_507);
lean_dec(x_503);
x_508 = l_Lake_LeanConfig_decodeToml___closed__20;
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_507);
lean_ctor_set(x_509, 1, x_508);
x_492 = x_509;
goto block_497;
}
}
case 2:
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_510 = lean_ctor_get(x_503, 0);
lean_inc(x_510);
lean_dec(x_503);
x_511 = l_Lake_LeanConfig_decodeToml___closed__20;
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_510);
lean_ctor_set(x_512, 1, x_511);
x_492 = x_512;
goto block_497;
}
case 3:
{
uint8_t x_513; 
x_513 = lean_ctor_get_uint8(x_503, sizeof(void*)*1);
lean_dec(x_503);
x_30 = x_513;
x_31 = x_29;
goto block_491;
}
default: 
{
uint8_t x_514; 
x_514 = !lean_is_exclusive(x_503);
if (x_514 == 0)
{
lean_object* x_515; lean_object* x_516; 
x_515 = lean_ctor_get(x_503, 1);
lean_dec(x_515);
x_516 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_503, 0);
lean_ctor_set(x_503, 1, x_516);
x_492 = x_503;
goto block_497;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_503, 0);
lean_inc(x_517);
lean_dec(x_503);
x_518 = l_Lake_LeanConfig_decodeToml___closed__20;
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
x_492 = x_519;
goto block_497;
}
}
}
}
block_491:
{
lean_object* x_32; lean_object* x_33; lean_object* x_466; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_473 = l_Lake_PackageConfig_decodeToml___closed__41;
lean_inc(x_2);
x_474 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_472, x_473, x_2);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; 
x_475 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_32 = x_475;
x_33 = x_31;
goto block_465;
}
else
{
lean_object* x_476; lean_object* x_477; 
x_476 = lean_ctor_get(x_474, 0);
lean_inc(x_476);
lean_dec(x_474);
x_477 = lean_ctor_get(x_476, 1);
lean_inc(x_477);
lean_dec(x_476);
switch (lean_obj_tag(x_477)) {
case 0:
{
lean_object* x_478; 
x_478 = lean_ctor_get(x_477, 1);
lean_inc(x_478);
lean_dec(x_477);
x_32 = x_478;
x_33 = x_31;
goto block_465;
}
case 2:
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_477, 0);
lean_inc(x_479);
lean_dec(x_477);
x_480 = l_Lake_Glob_decodeToml___closed__2;
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
x_466 = x_481;
goto block_471;
}
case 3:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_477, 0);
lean_inc(x_482);
lean_dec(x_477);
x_483 = l_Lake_Glob_decodeToml___closed__2;
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
x_466 = x_484;
goto block_471;
}
default: 
{
uint8_t x_485; 
x_485 = !lean_is_exclusive(x_477);
if (x_485 == 0)
{
lean_object* x_486; lean_object* x_487; 
x_486 = lean_ctor_get(x_477, 1);
lean_dec(x_486);
x_487 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_477, 0);
lean_ctor_set(x_477, 1, x_487);
x_466 = x_477;
goto block_471;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_477, 0);
lean_inc(x_488);
lean_dec(x_477);
x_489 = l_Lake_Glob_decodeToml___closed__2;
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
x_466 = x_490;
goto block_471;
}
}
}
}
block_465:
{
lean_object* x_34; lean_object* x_35; lean_object* x_440; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_446 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_447 = l_Lake_PackageConfig_decodeToml___closed__39;
lean_inc(x_2);
x_448 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_446, x_447, x_2);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; 
x_449 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_449;
x_35 = x_33;
goto block_439;
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
lean_object* x_452; 
x_452 = lean_ctor_get(x_451, 1);
lean_inc(x_452);
lean_dec(x_451);
x_34 = x_452;
x_35 = x_33;
goto block_439;
}
case 2:
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_451, 0);
lean_inc(x_453);
lean_dec(x_451);
x_454 = l_Lake_Glob_decodeToml___closed__2;
x_455 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
x_440 = x_455;
goto block_445;
}
case 3:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_451, 0);
lean_inc(x_456);
lean_dec(x_451);
x_457 = l_Lake_Glob_decodeToml___closed__2;
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_456);
lean_ctor_set(x_458, 1, x_457);
x_440 = x_458;
goto block_445;
}
default: 
{
uint8_t x_459; 
x_459 = !lean_is_exclusive(x_451);
if (x_459 == 0)
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_ctor_get(x_451, 1);
lean_dec(x_460);
x_461 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_451, 0);
lean_ctor_set(x_451, 1, x_461);
x_440 = x_451;
goto block_445;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_451, 0);
lean_inc(x_462);
lean_dec(x_451);
x_463 = l_Lake_Glob_decodeToml___closed__2;
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
x_440 = x_464;
goto block_445;
}
}
}
}
block_439:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_string_utf8_byte_size(x_32);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_eq(x_36, x_37);
lean_dec(x_36);
x_39 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_40 = l_Lake_PackageConfig_decodeToml___closed__4;
lean_inc(x_2);
x_41 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_40, x_2);
if (x_38 == 0)
{
uint8_t x_433; 
x_433 = l_Lake_PackageConfig_decodeToml___closed__36;
if (x_433 == 0)
{
lean_dec(x_32);
x_42 = x_34;
goto block_432;
}
else
{
lean_object* x_434; uint8_t x_435; 
x_434 = lean_string_utf8_byte_size(x_34);
x_435 = lean_nat_dec_eq(x_434, x_37);
lean_dec(x_434);
if (x_435 == 0)
{
lean_dec(x_32);
x_42 = x_34;
goto block_432;
}
else
{
lean_dec(x_34);
x_42 = x_32;
goto block_432;
}
}
}
else
{
uint8_t x_436; 
x_436 = l_Lake_PackageConfig_decodeToml___closed__37;
if (x_436 == 0)
{
lean_dec(x_32);
x_42 = x_34;
goto block_432;
}
else
{
lean_object* x_437; uint8_t x_438; 
x_437 = lean_string_utf8_byte_size(x_34);
x_438 = lean_nat_dec_eq(x_437, x_37);
lean_dec(x_437);
if (x_438 == 0)
{
lean_dec(x_32);
x_42 = x_34;
goto block_432;
}
else
{
lean_dec(x_34);
x_42 = x_32;
goto block_432;
}
}
}
block_432:
{
lean_object* x_43; lean_object* x_44; lean_object* x_399; 
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_405; 
x_405 = l_Lake_decodeLeanOptions___closed__1;
x_43 = x_405;
x_44 = x_35;
goto block_398;
}
else
{
lean_object* x_406; lean_object* x_407; 
x_406 = lean_ctor_get(x_41, 0);
lean_inc(x_406);
lean_dec(x_41);
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
lean_dec(x_406);
switch (lean_obj_tag(x_407)) {
case 0:
{
uint8_t x_408; 
x_408 = !lean_is_exclusive(x_407);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_407, 1);
lean_dec(x_409);
x_410 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_407, 1, x_410);
x_399 = x_407;
goto block_404;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_407, 0);
lean_inc(x_411);
lean_dec(x_407);
x_412 = l_Lake_LeanConfig_decodeToml___closed__5;
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
x_399 = x_413;
goto block_404;
}
}
case 2:
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_407, 0);
lean_inc(x_414);
lean_dec(x_407);
x_415 = l_Lake_LeanConfig_decodeToml___closed__5;
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_414);
lean_ctor_set(x_416, 1, x_415);
x_399 = x_416;
goto block_404;
}
case 3:
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_417 = lean_ctor_get(x_407, 0);
lean_inc(x_417);
lean_dec(x_407);
x_418 = l_Lake_LeanConfig_decodeToml___closed__5;
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_417);
lean_ctor_set(x_419, 1, x_418);
x_399 = x_419;
goto block_404;
}
case 5:
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_407, 1);
lean_inc(x_420);
lean_dec(x_407);
x_421 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_420);
lean_dec(x_420);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; 
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
lean_dec(x_421);
x_423 = l_Array_append___rarg(x_35, x_422);
lean_dec(x_422);
x_424 = l_Lake_decodeLeanOptions___closed__1;
x_43 = x_424;
x_44 = x_423;
goto block_398;
}
else
{
lean_object* x_425; 
x_425 = lean_ctor_get(x_421, 0);
lean_inc(x_425);
lean_dec(x_421);
x_43 = x_425;
x_44 = x_35;
goto block_398;
}
}
default: 
{
uint8_t x_426; 
x_426 = !lean_is_exclusive(x_407);
if (x_426 == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_407, 1);
lean_dec(x_427);
x_428 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_407, 0);
lean_ctor_set(x_407, 1, x_428);
x_399 = x_407;
goto block_404;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_429 = lean_ctor_get(x_407, 0);
lean_inc(x_429);
lean_dec(x_407);
x_430 = l_Lake_LeanConfig_decodeToml___closed__5;
x_431 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_431, 0, x_429);
lean_ctor_set(x_431, 1, x_430);
x_399 = x_431;
goto block_404;
}
}
}
}
block_398:
{
lean_object* x_45; lean_object* x_46; lean_object* x_374; lean_object* x_380; lean_object* x_381; 
x_380 = l_Lake_PackageConfig_decodeToml___closed__35;
lean_inc(x_2);
x_381 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_380, x_2);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; 
x_382 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_45 = x_382;
x_46 = x_44;
goto block_373;
}
else
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
lean_dec(x_381);
x_384 = lean_ctor_get(x_383, 1);
lean_inc(x_384);
lean_dec(x_383);
switch (lean_obj_tag(x_384)) {
case 0:
{
lean_object* x_385; 
x_385 = lean_ctor_get(x_384, 1);
lean_inc(x_385);
lean_dec(x_384);
x_45 = x_385;
x_46 = x_44;
goto block_373;
}
case 2:
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_384, 0);
lean_inc(x_386);
lean_dec(x_384);
x_387 = l_Lake_Glob_decodeToml___closed__2;
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
x_374 = x_388;
goto block_379;
}
case 3:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_384, 0);
lean_inc(x_389);
lean_dec(x_384);
x_390 = l_Lake_Glob_decodeToml___closed__2;
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_389);
lean_ctor_set(x_391, 1, x_390);
x_374 = x_391;
goto block_379;
}
default: 
{
uint8_t x_392; 
x_392 = !lean_is_exclusive(x_384);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_384, 1);
lean_dec(x_393);
x_394 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_384, 0);
lean_ctor_set(x_384, 1, x_394);
x_374 = x_384;
goto block_379;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_395 = lean_ctor_get(x_384, 0);
lean_inc(x_395);
lean_dec(x_384);
x_396 = l_Lake_Glob_decodeToml___closed__2;
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
x_374 = x_397;
goto block_379;
}
}
}
}
block_373:
{
lean_object* x_47; lean_object* x_48; lean_object* x_338; lean_object* x_344; lean_object* x_345; 
x_344 = l_Lake_PackageConfig_decodeToml___closed__33;
lean_inc(x_2);
x_345 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_344, x_2);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; 
x_346 = l_Lake_decodeLeanOptions___closed__1;
x_47 = x_346;
x_48 = x_46;
goto block_337;
}
else
{
lean_object* x_347; lean_object* x_348; 
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get(x_347, 1);
lean_inc(x_348);
lean_dec(x_347);
switch (lean_obj_tag(x_348)) {
case 0:
{
uint8_t x_349; 
x_349 = !lean_is_exclusive(x_348);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_348, 1);
lean_dec(x_350);
x_351 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_348, 1, x_351);
x_338 = x_348;
goto block_343;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_352 = lean_ctor_get(x_348, 0);
lean_inc(x_352);
lean_dec(x_348);
x_353 = l_Lake_LeanConfig_decodeToml___closed__5;
x_354 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set(x_354, 1, x_353);
x_338 = x_354;
goto block_343;
}
}
case 2:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_348, 0);
lean_inc(x_355);
lean_dec(x_348);
x_356 = l_Lake_LeanConfig_decodeToml___closed__5;
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
x_338 = x_357;
goto block_343;
}
case 3:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_348, 0);
lean_inc(x_358);
lean_dec(x_348);
x_359 = l_Lake_LeanConfig_decodeToml___closed__5;
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
x_338 = x_360;
goto block_343;
}
case 5:
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_348, 1);
lean_inc(x_361);
lean_dec(x_348);
x_362 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_361);
lean_dec(x_361);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec(x_362);
x_364 = l_Array_append___rarg(x_46, x_363);
lean_dec(x_363);
x_365 = l_Lake_decodeLeanOptions___closed__1;
x_47 = x_365;
x_48 = x_364;
goto block_337;
}
else
{
lean_object* x_366; 
x_366 = lean_ctor_get(x_362, 0);
lean_inc(x_366);
lean_dec(x_362);
x_47 = x_366;
x_48 = x_46;
goto block_337;
}
}
default: 
{
uint8_t x_367; 
x_367 = !lean_is_exclusive(x_348);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; 
x_368 = lean_ctor_get(x_348, 1);
lean_dec(x_368);
x_369 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_348, 0);
lean_ctor_set(x_348, 1, x_369);
x_338 = x_348;
goto block_343;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_348, 0);
lean_inc(x_370);
lean_dec(x_348);
x_371 = l_Lake_LeanConfig_decodeToml___closed__5;
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_338 = x_372;
goto block_343;
}
}
}
}
block_337:
{
lean_object* x_49; lean_object* x_50; lean_object* x_327; lean_object* x_328; 
x_327 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_2);
x_328 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_327, x_2);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; 
x_329 = l_Lake_PackageConfig_decodeToml___closed__31;
x_49 = x_329;
x_50 = x_48;
goto block_326;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_328, 0);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_ctor_get(x_330, 1);
lean_inc(x_331);
lean_dec(x_330);
x_332 = l_Lake_StdVer_decodeToml(x_331);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
lean_dec(x_332);
x_334 = l_Array_append___rarg(x_48, x_333);
lean_dec(x_333);
x_335 = l_Lake_PackageConfig_decodeToml___closed__31;
x_49 = x_335;
x_50 = x_334;
goto block_326;
}
else
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_332, 0);
lean_inc(x_336);
lean_dec(x_332);
x_49 = x_336;
x_50 = x_48;
goto block_326;
}
}
block_326:
{
lean_object* x_51; lean_object* x_52; lean_object* x_315; lean_object* x_316; 
x_315 = l_Lake_PackageConfig_decodeToml___closed__27;
lean_inc(x_2);
x_316 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_315, x_2);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; 
x_317 = l_Lake_defaultVersionTags;
x_51 = x_317;
x_52 = x_50;
goto block_314;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_318 = lean_ctor_get(x_316, 0);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = l_Lake_versionTagPresets;
x_321 = l_Lake_StrPat_decodeToml(x_319, x_320);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
lean_dec(x_321);
x_323 = l_Array_append___rarg(x_50, x_322);
lean_dec(x_322);
x_324 = l_Lake_defaultVersionTags;
x_51 = x_324;
x_52 = x_323;
goto block_314;
}
else
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_321, 0);
lean_inc(x_325);
lean_dec(x_321);
x_51 = x_325;
x_52 = x_50;
goto block_314;
}
}
block_314:
{
lean_object* x_53; lean_object* x_54; lean_object* x_290; lean_object* x_296; lean_object* x_297; 
x_296 = l_Lake_PackageConfig_decodeToml___closed__25;
lean_inc(x_2);
x_297 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_296, x_2);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; 
x_298 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_53 = x_298;
x_54 = x_52;
goto block_289;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
lean_dec(x_299);
switch (lean_obj_tag(x_300)) {
case 0:
{
lean_object* x_301; 
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
lean_dec(x_300);
x_53 = x_301;
x_54 = x_52;
goto block_289;
}
case 2:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_300, 0);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l_Lake_Glob_decodeToml___closed__2;
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
x_290 = x_304;
goto block_295;
}
case 3:
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_300, 0);
lean_inc(x_305);
lean_dec(x_300);
x_306 = l_Lake_Glob_decodeToml___closed__2;
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_290 = x_307;
goto block_295;
}
default: 
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_300);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_300, 1);
lean_dec(x_309);
x_310 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_300, 0);
lean_ctor_set(x_300, 1, x_310);
x_290 = x_300;
goto block_295;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_300, 0);
lean_inc(x_311);
lean_dec(x_300);
x_312 = l_Lake_Glob_decodeToml___closed__2;
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
x_290 = x_313;
goto block_295;
}
}
}
}
block_289:
{
lean_object* x_55; lean_object* x_56; lean_object* x_254; lean_object* x_260; lean_object* x_261; 
x_260 = l_Lake_PackageConfig_decodeToml___closed__23;
lean_inc(x_2);
x_261 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_260, x_2);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
x_262 = l_Lake_decodeLeanOptions___closed__1;
x_55 = x_262;
x_56 = x_54;
goto block_253;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
switch (lean_obj_tag(x_264)) {
case 0:
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_264, 1);
lean_dec(x_266);
x_267 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_264, 1, x_267);
x_254 = x_264;
goto block_259;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_264, 0);
lean_inc(x_268);
lean_dec(x_264);
x_269 = l_Lake_LeanConfig_decodeToml___closed__5;
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
x_254 = x_270;
goto block_259;
}
}
case 2:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_264, 0);
lean_inc(x_271);
lean_dec(x_264);
x_272 = l_Lake_LeanConfig_decodeToml___closed__5;
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_254 = x_273;
goto block_259;
}
case 3:
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_264, 0);
lean_inc(x_274);
lean_dec(x_264);
x_275 = l_Lake_LeanConfig_decodeToml___closed__5;
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
x_254 = x_276;
goto block_259;
}
case 5:
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_264, 1);
lean_inc(x_277);
lean_dec(x_264);
x_278 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_277);
lean_dec(x_277);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec(x_278);
x_280 = l_Array_append___rarg(x_54, x_279);
lean_dec(x_279);
x_281 = l_Lake_decodeLeanOptions___closed__1;
x_55 = x_281;
x_56 = x_280;
goto block_253;
}
else
{
lean_object* x_282; 
x_282 = lean_ctor_get(x_278, 0);
lean_inc(x_282);
lean_dec(x_278);
x_55 = x_282;
x_56 = x_54;
goto block_253;
}
}
default: 
{
uint8_t x_283; 
x_283 = !lean_is_exclusive(x_264);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_264, 1);
lean_dec(x_284);
x_285 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_264, 0);
lean_ctor_set(x_264, 1, x_285);
x_254 = x_264;
goto block_259;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_264, 0);
lean_inc(x_286);
lean_dec(x_264);
x_287 = l_Lake_LeanConfig_decodeToml___closed__5;
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
x_254 = x_288;
goto block_259;
}
}
}
}
block_253:
{
lean_object* x_57; lean_object* x_58; lean_object* x_229; lean_object* x_235; lean_object* x_236; 
x_235 = l_Lake_PackageConfig_decodeToml___closed__21;
lean_inc(x_2);
x_236 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_235, x_2);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; 
x_237 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_57 = x_237;
x_58 = x_56;
goto block_228;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_236, 0);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
switch (lean_obj_tag(x_239)) {
case 0:
{
lean_object* x_240; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_57 = x_240;
x_58 = x_56;
goto block_228;
}
case 2:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_239, 0);
lean_inc(x_241);
lean_dec(x_239);
x_242 = l_Lake_Glob_decodeToml___closed__2;
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_229 = x_243;
goto block_234;
}
case 3:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_239, 0);
lean_inc(x_244);
lean_dec(x_239);
x_245 = l_Lake_Glob_decodeToml___closed__2;
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_229 = x_246;
goto block_234;
}
default: 
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_239);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
x_248 = lean_ctor_get(x_239, 1);
lean_dec(x_248);
x_249 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_239, 0);
lean_ctor_set(x_239, 1, x_249);
x_229 = x_239;
goto block_234;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_239, 0);
lean_inc(x_250);
lean_dec(x_239);
x_251 = l_Lake_Glob_decodeToml___closed__2;
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_229 = x_252;
goto block_234;
}
}
}
}
block_228:
{
lean_object* x_59; lean_object* x_60; lean_object* x_204; lean_object* x_210; lean_object* x_211; 
x_210 = l_Lake_PackageConfig_decodeToml___closed__19;
lean_inc(x_2);
x_211 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_210, x_2);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; 
x_212 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_59 = x_212;
x_60 = x_58;
goto block_203;
}
else
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_211, 0);
lean_inc(x_213);
lean_dec(x_211);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
switch (lean_obj_tag(x_214)) {
case 0:
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_59 = x_215;
x_60 = x_58;
goto block_203;
}
case 2:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
lean_dec(x_214);
x_217 = l_Lake_Glob_decodeToml___closed__2;
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_204 = x_218;
goto block_209;
}
case 3:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_214, 0);
lean_inc(x_219);
lean_dec(x_214);
x_220 = l_Lake_Glob_decodeToml___closed__2;
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_204 = x_221;
goto block_209;
}
default: 
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_214);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_214, 1);
lean_dec(x_223);
x_224 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_214, 0);
lean_ctor_set(x_214, 1, x_224);
x_204 = x_214;
goto block_209;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_214, 0);
lean_inc(x_225);
lean_dec(x_214);
x_226 = l_Lake_Glob_decodeToml___closed__2;
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_204 = x_227;
goto block_209;
}
}
}
}
block_203:
{
lean_object* x_61; lean_object* x_62; lean_object* x_168; lean_object* x_174; lean_object* x_175; 
x_174 = l_Lake_PackageConfig_decodeToml___closed__14;
lean_inc(x_2);
x_175 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_174, x_2);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = l_Lake_PackageConfig_decodeToml___closed__17;
x_61 = x_176;
x_62 = x_60;
goto block_167;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
switch (lean_obj_tag(x_178)) {
case 0:
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_178, 1);
lean_dec(x_180);
x_181 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_178, 1, x_181);
x_168 = x_178;
goto block_173;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_178, 0);
lean_inc(x_182);
lean_dec(x_178);
x_183 = l_Lake_LeanConfig_decodeToml___closed__5;
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_168 = x_184;
goto block_173;
}
}
case 2:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_178, 0);
lean_inc(x_185);
lean_dec(x_178);
x_186 = l_Lake_LeanConfig_decodeToml___closed__5;
x_187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_168 = x_187;
goto block_173;
}
case 3:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_178, 0);
lean_inc(x_188);
lean_dec(x_178);
x_189 = l_Lake_LeanConfig_decodeToml___closed__5;
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_168 = x_190;
goto block_173;
}
case 5:
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_178, 1);
lean_inc(x_191);
lean_dec(x_178);
x_192 = l_Lake_Toml_decodeArray___at_Lake_PackageConfig_decodeToml___spec__1(x_191);
lean_dec(x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = l_Array_append___rarg(x_60, x_193);
lean_dec(x_193);
x_195 = l_Lake_PackageConfig_decodeToml___closed__17;
x_61 = x_195;
x_62 = x_194;
goto block_167;
}
else
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
lean_dec(x_192);
x_61 = x_196;
x_62 = x_60;
goto block_167;
}
}
default: 
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_178);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_178, 1);
lean_dec(x_198);
x_199 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_178, 0);
lean_ctor_set(x_178, 1, x_199);
x_168 = x_178;
goto block_173;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_178, 0);
lean_inc(x_200);
lean_dec(x_178);
x_201 = l_Lake_LeanConfig_decodeToml___closed__5;
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
x_168 = x_202;
goto block_173;
}
}
}
}
block_167:
{
lean_object* x_63; lean_object* x_64; lean_object* x_143; lean_object* x_149; lean_object* x_150; 
x_149 = l_Lake_PackageConfig_decodeToml___closed__12;
lean_inc(x_2);
x_150 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_149, x_2);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = l_Lake_PackageConfig_decodeToml___closed__10;
x_63 = x_151;
x_64 = x_62;
goto block_142;
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
x_63 = x_154;
x_64 = x_62;
goto block_142;
}
case 2:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 0);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lake_Glob_decodeToml___closed__2;
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_143 = x_157;
goto block_148;
}
case 3:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_158);
lean_dec(x_153);
x_159 = l_Lake_Glob_decodeToml___closed__2;
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_143 = x_160;
goto block_148;
}
default: 
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_153);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_153, 1);
lean_dec(x_162);
x_163 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_153, 0);
lean_ctor_set(x_153, 1, x_163);
x_143 = x_153;
goto block_148;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_153, 0);
lean_inc(x_164);
lean_dec(x_153);
x_165 = l_Lake_Glob_decodeToml___closed__2;
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_143 = x_166;
goto block_148;
}
}
}
}
block_142:
{
uint8_t x_65; lean_object* x_66; lean_object* x_115; lean_object* x_121; lean_object* x_122; 
x_121 = l_Lake_PackageConfig_decodeToml___closed__9;
lean_inc(x_2);
x_122 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_39, x_121, x_2);
if (lean_obj_tag(x_122) == 0)
{
uint8_t x_123; 
x_123 = 1;
x_65 = x_123;
x_66 = x_64;
goto block_114;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
switch (lean_obj_tag(x_125)) {
case 0:
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 1);
lean_dec(x_127);
x_128 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_125, 1, x_128);
x_115 = x_125;
goto block_120;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_125, 0);
lean_inc(x_129);
lean_dec(x_125);
x_130 = l_Lake_LeanConfig_decodeToml___closed__20;
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_115 = x_131;
goto block_120;
}
}
case 2:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_125, 0);
lean_inc(x_132);
lean_dec(x_125);
x_133 = l_Lake_LeanConfig_decodeToml___closed__20;
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_115 = x_134;
goto block_120;
}
case 3:
{
uint8_t x_135; 
x_135 = lean_ctor_get_uint8(x_125, sizeof(void*)*1);
lean_dec(x_125);
x_65 = x_135;
x_66 = x_64;
goto block_114;
}
default: 
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_125);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_125, 1);
lean_dec(x_137);
x_138 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_125, 0);
lean_ctor_set(x_125, 1, x_138);
x_115 = x_125;
goto block_120;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_125, 0);
lean_inc(x_139);
lean_dec(x_125);
x_140 = l_Lake_LeanConfig_decodeToml___closed__20;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_115 = x_141;
goto block_120;
}
}
}
}
block_114:
{
lean_object* x_67; lean_object* x_68; lean_object* x_109; 
lean_inc(x_2);
x_109 = l_Lake_LeanConfig_decodeToml(x_2);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = l_Array_append___rarg(x_66, x_110);
lean_dec(x_110);
x_112 = l_Lake_PackageConfig_decodeToml___closed__7;
x_67 = x_112;
x_68 = x_111;
goto block_108;
}
else
{
lean_object* x_113; 
x_113 = lean_ctor_get(x_109, 0);
lean_inc(x_113);
lean_dec(x_109);
x_67 = x_113;
x_68 = x_66;
goto block_108;
}
block_108:
{
lean_object* x_69; 
x_69 = l_Lake_WorkspaceConfig_decodeToml(x_2);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Array_append___rarg(x_68, x_70);
lean_dec(x_70);
x_72 = lean_box(0);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_73 = 0;
x_74 = l_Lake_StrPat_decodeToml___closed__6;
x_75 = l_Lean_Name_toString(x_1, x_73, x_74);
x_76 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_77 = lean_string_append(x_76, x_75);
lean_dec(x_75);
x_78 = l_Lake_PackageConfig_decodeToml___closed__5;
x_79 = lean_string_append(x_77, x_78);
x_80 = l_System_Platform_target;
x_81 = lean_string_append(x_79, x_80);
x_82 = l_Lake_PackageConfig_decodeToml___closed__6;
x_83 = lean_string_append(x_81, x_82);
x_84 = l_Lake_decodeLeanOptions___closed__1;
x_85 = lean_alloc_ctor(0, 28, 3);
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_67);
lean_ctor_set(x_85, 2, x_72);
lean_ctor_set(x_85, 3, x_84);
lean_ctor_set(x_85, 4, x_84);
lean_ctor_set(x_85, 5, x_12);
lean_ctor_set(x_85, 6, x_14);
lean_ctor_set(x_85, 7, x_16);
lean_ctor_set(x_85, 8, x_18);
lean_ctor_set(x_85, 9, x_20);
lean_ctor_set(x_85, 10, x_22);
lean_ctor_set(x_85, 11, x_24);
lean_ctor_set(x_85, 12, x_72);
lean_ctor_set(x_85, 13, x_26);
lean_ctor_set(x_85, 14, x_28);
lean_ctor_set(x_85, 15, x_83);
lean_ctor_set(x_85, 16, x_42);
lean_ctor_set(x_85, 17, x_43);
lean_ctor_set(x_85, 18, x_45);
lean_ctor_set(x_85, 19, x_47);
lean_ctor_set(x_85, 20, x_49);
lean_ctor_set(x_85, 21, x_51);
lean_ctor_set(x_85, 22, x_53);
lean_ctor_set(x_85, 23, x_55);
lean_ctor_set(x_85, 24, x_57);
lean_ctor_set(x_85, 25, x_59);
lean_ctor_set(x_85, 26, x_61);
lean_ctor_set(x_85, 27, x_63);
lean_ctor_set_uint8(x_85, sizeof(void*)*28, x_9);
lean_ctor_set_uint8(x_85, sizeof(void*)*28 + 1, x_30);
lean_ctor_set_uint8(x_85, sizeof(void*)*28 + 2, x_65);
x_3 = x_85;
x_4 = x_71;
goto block_8;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_1);
x_86 = lean_ctor_get(x_28, 0);
lean_inc(x_86);
x_87 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_88 = l_Lake_decodeLeanOptions___closed__1;
x_89 = lean_alloc_ctor(0, 28, 3);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_67);
lean_ctor_set(x_89, 2, x_72);
lean_ctor_set(x_89, 3, x_88);
lean_ctor_set(x_89, 4, x_88);
lean_ctor_set(x_89, 5, x_12);
lean_ctor_set(x_89, 6, x_14);
lean_ctor_set(x_89, 7, x_16);
lean_ctor_set(x_89, 8, x_18);
lean_ctor_set(x_89, 9, x_20);
lean_ctor_set(x_89, 10, x_22);
lean_ctor_set(x_89, 11, x_24);
lean_ctor_set(x_89, 12, x_72);
lean_ctor_set(x_89, 13, x_26);
lean_ctor_set(x_89, 14, x_28);
lean_ctor_set(x_89, 15, x_86);
lean_ctor_set(x_89, 16, x_42);
lean_ctor_set(x_89, 17, x_43);
lean_ctor_set(x_89, 18, x_45);
lean_ctor_set(x_89, 19, x_47);
lean_ctor_set(x_89, 20, x_49);
lean_ctor_set(x_89, 21, x_51);
lean_ctor_set(x_89, 22, x_53);
lean_ctor_set(x_89, 23, x_55);
lean_ctor_set(x_89, 24, x_57);
lean_ctor_set(x_89, 25, x_59);
lean_ctor_set(x_89, 26, x_61);
lean_ctor_set(x_89, 27, x_63);
lean_ctor_set_uint8(x_89, sizeof(void*)*28, x_9);
lean_ctor_set_uint8(x_89, sizeof(void*)*28 + 1, x_30);
lean_ctor_set_uint8(x_89, sizeof(void*)*28 + 2, x_65);
x_3 = x_89;
x_4 = x_71;
goto block_8;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_69, 0);
lean_inc(x_90);
lean_dec(x_69);
x_91 = lean_box(0);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_92 = 0;
x_93 = l_Lake_StrPat_decodeToml___closed__6;
x_94 = l_Lean_Name_toString(x_1, x_92, x_93);
x_95 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_96 = lean_string_append(x_95, x_94);
lean_dec(x_94);
x_97 = l_Lake_PackageConfig_decodeToml___closed__5;
x_98 = lean_string_append(x_96, x_97);
x_99 = l_System_Platform_target;
x_100 = lean_string_append(x_98, x_99);
x_101 = l_Lake_PackageConfig_decodeToml___closed__6;
x_102 = lean_string_append(x_100, x_101);
x_103 = l_Lake_decodeLeanOptions___closed__1;
x_104 = lean_alloc_ctor(0, 28, 3);
lean_ctor_set(x_104, 0, x_90);
lean_ctor_set(x_104, 1, x_67);
lean_ctor_set(x_104, 2, x_91);
lean_ctor_set(x_104, 3, x_103);
lean_ctor_set(x_104, 4, x_103);
lean_ctor_set(x_104, 5, x_12);
lean_ctor_set(x_104, 6, x_14);
lean_ctor_set(x_104, 7, x_16);
lean_ctor_set(x_104, 8, x_18);
lean_ctor_set(x_104, 9, x_20);
lean_ctor_set(x_104, 10, x_22);
lean_ctor_set(x_104, 11, x_24);
lean_ctor_set(x_104, 12, x_91);
lean_ctor_set(x_104, 13, x_26);
lean_ctor_set(x_104, 14, x_28);
lean_ctor_set(x_104, 15, x_102);
lean_ctor_set(x_104, 16, x_42);
lean_ctor_set(x_104, 17, x_43);
lean_ctor_set(x_104, 18, x_45);
lean_ctor_set(x_104, 19, x_47);
lean_ctor_set(x_104, 20, x_49);
lean_ctor_set(x_104, 21, x_51);
lean_ctor_set(x_104, 22, x_53);
lean_ctor_set(x_104, 23, x_55);
lean_ctor_set(x_104, 24, x_57);
lean_ctor_set(x_104, 25, x_59);
lean_ctor_set(x_104, 26, x_61);
lean_ctor_set(x_104, 27, x_63);
lean_ctor_set_uint8(x_104, sizeof(void*)*28, x_9);
lean_ctor_set_uint8(x_104, sizeof(void*)*28 + 1, x_30);
lean_ctor_set_uint8(x_104, sizeof(void*)*28 + 2, x_65);
x_3 = x_104;
x_4 = x_68;
goto block_8;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_1);
x_105 = lean_ctor_get(x_28, 0);
lean_inc(x_105);
x_106 = l_Lake_decodeLeanOptions___closed__1;
x_107 = lean_alloc_ctor(0, 28, 3);
lean_ctor_set(x_107, 0, x_90);
lean_ctor_set(x_107, 1, x_67);
lean_ctor_set(x_107, 2, x_91);
lean_ctor_set(x_107, 3, x_106);
lean_ctor_set(x_107, 4, x_106);
lean_ctor_set(x_107, 5, x_12);
lean_ctor_set(x_107, 6, x_14);
lean_ctor_set(x_107, 7, x_16);
lean_ctor_set(x_107, 8, x_18);
lean_ctor_set(x_107, 9, x_20);
lean_ctor_set(x_107, 10, x_22);
lean_ctor_set(x_107, 11, x_24);
lean_ctor_set(x_107, 12, x_91);
lean_ctor_set(x_107, 13, x_26);
lean_ctor_set(x_107, 14, x_28);
lean_ctor_set(x_107, 15, x_105);
lean_ctor_set(x_107, 16, x_42);
lean_ctor_set(x_107, 17, x_43);
lean_ctor_set(x_107, 18, x_45);
lean_ctor_set(x_107, 19, x_47);
lean_ctor_set(x_107, 20, x_49);
lean_ctor_set(x_107, 21, x_51);
lean_ctor_set(x_107, 22, x_53);
lean_ctor_set(x_107, 23, x_55);
lean_ctor_set(x_107, 24, x_57);
lean_ctor_set(x_107, 25, x_59);
lean_ctor_set(x_107, 26, x_61);
lean_ctor_set(x_107, 27, x_63);
lean_ctor_set_uint8(x_107, sizeof(void*)*28, x_9);
lean_ctor_set_uint8(x_107, sizeof(void*)*28 + 1, x_30);
lean_ctor_set_uint8(x_107, sizeof(void*)*28 + 2, x_65);
x_3 = x_107;
x_4 = x_68;
goto block_8;
}
}
}
}
block_120:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_11);
x_117 = lean_array_mk(x_116);
x_118 = l_Array_append___rarg(x_64, x_117);
lean_dec(x_117);
x_119 = 1;
x_65 = x_119;
x_66 = x_118;
goto block_114;
}
}
block_148:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_11);
x_145 = lean_array_mk(x_144);
x_146 = l_Array_append___rarg(x_62, x_145);
lean_dec(x_145);
x_147 = l_Lake_PackageConfig_decodeToml___closed__10;
x_63 = x_147;
x_64 = x_146;
goto block_142;
}
}
block_173:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_11);
x_170 = lean_array_mk(x_169);
x_171 = l_Array_append___rarg(x_60, x_170);
lean_dec(x_170);
x_172 = l_Lake_PackageConfig_decodeToml___closed__17;
x_61 = x_172;
x_62 = x_171;
goto block_167;
}
}
block_209:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_11);
x_206 = lean_array_mk(x_205);
x_207 = l_Array_append___rarg(x_58, x_206);
lean_dec(x_206);
x_208 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_59 = x_208;
x_60 = x_207;
goto block_203;
}
}
block_234:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_11);
x_231 = lean_array_mk(x_230);
x_232 = l_Array_append___rarg(x_56, x_231);
lean_dec(x_231);
x_233 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_57 = x_233;
x_58 = x_232;
goto block_228;
}
}
block_259:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_11);
x_256 = lean_array_mk(x_255);
x_257 = l_Array_append___rarg(x_54, x_256);
lean_dec(x_256);
x_258 = l_Lake_decodeLeanOptions___closed__1;
x_55 = x_258;
x_56 = x_257;
goto block_253;
}
}
block_295:
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_291 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_11);
x_292 = lean_array_mk(x_291);
x_293 = l_Array_append___rarg(x_52, x_292);
lean_dec(x_292);
x_294 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_53 = x_294;
x_54 = x_293;
goto block_289;
}
}
}
}
block_343:
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_11);
x_340 = lean_array_mk(x_339);
x_341 = l_Array_append___rarg(x_46, x_340);
lean_dec(x_340);
x_342 = l_Lake_decodeLeanOptions___closed__1;
x_47 = x_342;
x_48 = x_341;
goto block_337;
}
}
block_379:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_375 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_11);
x_376 = lean_array_mk(x_375);
x_377 = l_Array_append___rarg(x_44, x_376);
lean_dec(x_376);
x_378 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_45 = x_378;
x_46 = x_377;
goto block_373;
}
}
block_404:
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_11);
x_401 = lean_array_mk(x_400);
x_402 = l_Array_append___rarg(x_35, x_401);
lean_dec(x_401);
x_403 = l_Lake_decodeLeanOptions___closed__1;
x_43 = x_403;
x_44 = x_402;
goto block_398;
}
}
}
block_445:
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_441 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_11);
x_442 = lean_array_mk(x_441);
x_443 = l_Array_append___rarg(x_33, x_442);
lean_dec(x_442);
x_444 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_34 = x_444;
x_35 = x_443;
goto block_439;
}
}
block_471:
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_467 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_467, 0, x_466);
lean_ctor_set(x_467, 1, x_11);
x_468 = lean_array_mk(x_467);
x_469 = l_Array_append___rarg(x_31, x_468);
lean_dec(x_468);
x_470 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_32 = x_470;
x_33 = x_469;
goto block_465;
}
}
block_497:
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_493 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_11);
x_494 = lean_array_mk(x_493);
x_495 = l_Array_append___rarg(x_29, x_494);
lean_dec(x_494);
x_496 = 0;
x_30 = x_496;
x_31 = x_495;
goto block_491;
}
}
block_529:
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_11);
x_527 = lean_array_mk(x_526);
x_528 = l_Array_append___rarg(x_27, x_527);
lean_dec(x_527);
x_28 = x_524;
x_29 = x_528;
goto block_520;
}
}
block_569:
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_565);
lean_ctor_set(x_566, 1, x_11);
x_567 = lean_array_mk(x_566);
x_568 = l_Array_append___rarg(x_25, x_567);
lean_dec(x_567);
x_26 = x_564;
x_27 = x_568;
goto block_560;
}
}
block_606:
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_11);
x_603 = lean_array_mk(x_602);
x_604 = l_Array_append___rarg(x_23, x_603);
lean_dec(x_603);
x_605 = l_Lake_defaultIrDir;
x_24 = x_605;
x_25 = x_604;
goto block_600;
}
}
block_632:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_627);
lean_ctor_set(x_628, 1, x_11);
x_629 = lean_array_mk(x_628);
x_630 = l_Array_append___rarg(x_21, x_629);
lean_dec(x_629);
x_631 = l_Lake_defaultBinDir;
x_22 = x_631;
x_23 = x_630;
goto block_626;
}
}
block_658:
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_654 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_11);
x_655 = lean_array_mk(x_654);
x_656 = l_Array_append___rarg(x_19, x_655);
lean_dec(x_655);
x_657 = l_Lake_defaultNativeLibDir;
x_20 = x_657;
x_21 = x_656;
goto block_652;
}
}
block_684:
{
lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_11);
x_681 = lean_array_mk(x_680);
x_682 = l_Array_append___rarg(x_17, x_681);
lean_dec(x_681);
x_683 = l_Lake_defaultLeanLibDir;
x_18 = x_683;
x_19 = x_682;
goto block_678;
}
}
block_710:
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_706 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_706, 0, x_705);
lean_ctor_set(x_706, 1, x_11);
x_707 = lean_array_mk(x_706);
x_708 = l_Array_append___rarg(x_15, x_707);
lean_dec(x_707);
x_709 = l_Lake_defaultBuildDir;
x_16 = x_709;
x_17 = x_708;
goto block_704;
}
}
block_736:
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_732 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_732, 0, x_731);
lean_ctor_set(x_732, 1, x_11);
x_733 = lean_array_mk(x_732);
x_734 = l_Array_append___rarg(x_13, x_733);
lean_dec(x_733);
x_735 = l_Lake_PackageConfig_decodeToml___closed__58;
x_14 = x_735;
x_15 = x_734;
goto block_730;
}
}
block_762:
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
x_758 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_758, 0, x_757);
lean_ctor_set(x_758, 1, x_11);
x_759 = lean_array_mk(x_758);
x_760 = l_Array_append___rarg(x_10, x_759);
lean_dec(x_759);
x_761 = l_Lake_decodeLeanOptions___closed__1;
x_12 = x_761;
x_13 = x_760;
goto block_756;
}
}
block_801:
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; uint8_t x_800; 
x_795 = lean_box(0);
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_794);
lean_ctor_set(x_796, 1, x_795);
x_797 = lean_array_mk(x_796);
x_798 = l_Lake_LeanOption_decodeToml___closed__3;
x_799 = l_Array_append___rarg(x_798, x_797);
lean_dec(x_797);
x_800 = 0;
x_9 = x_800;
x_10 = x_799;
goto block_793;
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
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlPackageConfig___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_2, 1, x_11);
x_3 = x_2;
goto block_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_3 = x_14;
goto block_8;
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_3 = x_17;
goto block_8;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_3 = x_20;
goto block_8;
}
case 6:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l_Lake_PackageConfig_decodeToml(x_1, x_21);
return x_22;
}
default: 
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 1);
lean_dec(x_24);
x_25 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_25);
x_3 = x_2;
goto block_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_3 = x_28;
goto block_8;
}
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_mk(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlPackageConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instDecodeTomlPackageConfig___lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_LeanLibConfig_decodeToml___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
x_21 = l_String_toName(x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
lean_ctor_set(x_6, 1, x_22);
x_9 = x_6;
goto block_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_6);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
x_24 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_25 = l_Lake_mergeErrors___rarg(x_4, x_23, x_24);
x_2 = x_8;
x_4 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get(x_6, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_6);
x_29 = l_String_toName(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_9 = x_31;
goto block_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_27);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_29);
x_33 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_34 = l_Lake_mergeErrors___rarg(x_4, x_32, x_33);
x_2 = x_8;
x_4 = x_34;
goto _start;
}
}
}
case 2:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = l_Lake_Glob_decodeToml___closed__2;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_9 = x_38;
goto block_17;
}
case 3:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
lean_dec(x_6);
x_40 = l_Lake_Glob_decodeToml___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_9 = x_41;
goto block_17;
}
default: 
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_6);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_6, 1);
lean_dec(x_43);
x_44 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_44);
x_9 = x_6;
goto block_17;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_6, 0);
lean_inc(x_45);
lean_dec(x_6);
x_46 = l_Lake_Glob_decodeToml___closed__2;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_9 = x_47;
goto block_17;
}
}
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_mk(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_15 = l_Lake_mergeErrors___rarg(x_4, x_13, x_14);
x_2 = x_8;
x_4 = x_15;
goto _start;
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
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_7, 0);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_mk(x_13);
lean_ctor_set(x_7, 0, x_14);
x_15 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_16 = l_Lake_mergeErrors___rarg(x_4, x_7, x_15);
x_2 = x_9;
x_4 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_mk(x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_24 = l_Lake_mergeErrors___rarg(x_4, x_22, x_23);
x_2 = x_9;
x_4 = x_24;
goto _start;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_28 = l_Lake_mergeErrors___rarg(x_4, x_7, x_27);
x_2 = x_9;
x_4 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_7, 0);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_33 = l_Lake_mergeErrors___rarg(x_4, x_31, x_32);
x_2 = x_9;
x_4 = x_33;
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
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_225; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_234 = l_Lake_PackageConfig_decodeToml___closed__60;
lean_inc(x_2);
x_235 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_233, x_234, x_2);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
x_236 = l_Lake_PackageConfig_decodeToml___closed__58;
x_237 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_236;
x_10 = x_237;
goto block_224;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_235, 0);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec(x_238);
switch (lean_obj_tag(x_239)) {
case 0:
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_241 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_240;
x_10 = x_241;
goto block_224;
}
case 2:
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_239, 0);
lean_inc(x_242);
lean_dec(x_239);
x_243 = l_Lake_Glob_decodeToml___closed__2;
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
x_225 = x_244;
goto block_232;
}
case 3:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_239, 0);
lean_inc(x_245);
lean_dec(x_239);
x_246 = l_Lake_Glob_decodeToml___closed__2;
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
x_225 = x_247;
goto block_232;
}
default: 
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_239);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_239, 1);
lean_dec(x_249);
x_250 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_239, 0);
lean_ctor_set(x_239, 1, x_250);
x_225 = x_239;
goto block_232;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_239, 0);
lean_inc(x_251);
lean_dec(x_239);
x_252 = l_Lake_Glob_decodeToml___closed__2;
x_253 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
x_225 = x_253;
goto block_232;
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
block_224:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_11 = lean_box(0);
lean_inc(x_1);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_1);
lean_ctor_set(x_189, 1, x_11);
x_190 = lean_array_mk(x_189);
x_196 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_197 = l_Lake_LeanLibConfig_decodeToml___closed__2;
lean_inc(x_2);
x_198 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_196, x_197, x_2);
if (lean_obj_tag(x_198) == 0)
{
x_12 = x_190;
x_13 = x_10;
goto block_188;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec(x_198);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
switch (lean_obj_tag(x_200)) {
case 0:
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_200, 1);
lean_dec(x_202);
x_203 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_200, 1, x_203);
x_191 = x_200;
goto block_195;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_200, 0);
lean_inc(x_204);
lean_dec(x_200);
x_205 = l_Lake_LeanConfig_decodeToml___closed__5;
x_206 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
x_191 = x_206;
goto block_195;
}
}
case 2:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_200, 0);
lean_inc(x_207);
lean_dec(x_200);
x_208 = l_Lake_LeanConfig_decodeToml___closed__5;
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_191 = x_209;
goto block_195;
}
case 3:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_200, 0);
lean_inc(x_210);
lean_dec(x_200);
x_211 = l_Lake_LeanConfig_decodeToml___closed__5;
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
x_191 = x_212;
goto block_195;
}
case 5:
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_200, 1);
lean_inc(x_213);
lean_dec(x_200);
x_214 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(x_213);
lean_dec(x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
lean_dec(x_214);
x_216 = l_Array_append___rarg(x_10, x_215);
lean_dec(x_215);
x_12 = x_190;
x_13 = x_216;
goto block_188;
}
else
{
lean_object* x_217; 
lean_dec(x_190);
x_217 = lean_ctor_get(x_214, 0);
lean_inc(x_217);
lean_dec(x_214);
x_12 = x_217;
x_13 = x_10;
goto block_188;
}
}
default: 
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_200);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_200, 1);
lean_dec(x_219);
x_220 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_200, 0);
lean_ctor_set(x_200, 1, x_220);
x_191 = x_200;
goto block_195;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_200, 0);
lean_inc(x_221);
lean_dec(x_200);
x_222 = l_Lake_LeanConfig_decodeToml___closed__5;
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_191 = x_223;
goto block_195;
}
}
}
}
block_188:
{
lean_object* x_14; lean_object* x_15; size_t x_127; size_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_127 = lean_array_size(x_12);
x_128 = 0;
lean_inc(x_12);
x_129 = l_Array_mapMUnsafe_map___at_Lake_LeanLibConfig_decodeToml___spec__3(x_127, x_128, x_12);
x_130 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_131 = l_Lake_LeanLibConfig_decodeToml___closed__12;
lean_inc(x_2);
x_132 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_130, x_131, x_2);
if (lean_obj_tag(x_132) == 0)
{
x_14 = x_129;
x_15 = x_13;
goto block_126;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec(x_132);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
switch (lean_obj_tag(x_134)) {
case 1:
{
lean_object* x_135; uint8_t x_136; 
lean_inc(x_134);
x_135 = l_Lake_Glob_decodeToml(x_134);
x_136 = !lean_is_exclusive(x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_134, 1);
lean_dec(x_137);
x_138 = lean_ctor_get(x_134, 0);
lean_dec(x_138);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_135, 0);
lean_inc(x_139);
lean_dec(x_135);
lean_ctor_set(x_134, 1, x_11);
lean_ctor_set(x_134, 0, x_139);
x_140 = lean_array_mk(x_134);
x_141 = l_Array_append___rarg(x_13, x_140);
lean_dec(x_140);
x_14 = x_129;
x_15 = x_141;
goto block_126;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_129);
x_142 = lean_ctor_get(x_135, 0);
lean_inc(x_142);
lean_dec(x_135);
lean_ctor_set(x_134, 1, x_11);
lean_ctor_set(x_134, 0, x_142);
x_143 = lean_array_mk(x_134);
x_14 = x_143;
x_15 = x_13;
goto block_126;
}
}
else
{
lean_dec(x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_135, 0);
lean_inc(x_144);
lean_dec(x_135);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_11);
x_146 = lean_array_mk(x_145);
x_147 = l_Array_append___rarg(x_13, x_146);
lean_dec(x_146);
x_14 = x_129;
x_15 = x_147;
goto block_126;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_129);
x_148 = lean_ctor_get(x_135, 0);
lean_inc(x_148);
lean_dec(x_135);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_11);
x_150 = lean_array_mk(x_149);
x_14 = x_150;
x_15 = x_13;
goto block_126;
}
}
}
case 2:
{
lean_object* x_151; 
x_151 = l_Lake_Glob_decodeToml(x_134);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_11);
x_154 = lean_array_mk(x_153);
x_155 = l_Array_append___rarg(x_13, x_154);
lean_dec(x_154);
x_14 = x_129;
x_15 = x_155;
goto block_126;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_129);
x_156 = lean_ctor_get(x_151, 0);
lean_inc(x_156);
lean_dec(x_151);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_11);
x_158 = lean_array_mk(x_157);
x_14 = x_158;
x_15 = x_13;
goto block_126;
}
}
case 3:
{
lean_object* x_159; 
x_159 = l_Lake_Glob_decodeToml(x_134);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_dec(x_159);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_11);
x_162 = lean_array_mk(x_161);
x_163 = l_Array_append___rarg(x_13, x_162);
lean_dec(x_162);
x_14 = x_129;
x_15 = x_163;
goto block_126;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_129);
x_164 = lean_ctor_get(x_159, 0);
lean_inc(x_164);
lean_dec(x_159);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_11);
x_166 = lean_array_mk(x_165);
x_14 = x_166;
x_15 = x_13;
goto block_126;
}
}
case 5:
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_134, 1);
lean_inc(x_167);
lean_dec(x_134);
x_168 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__4(x_167);
lean_dec(x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec(x_168);
x_170 = l_Array_append___rarg(x_13, x_169);
lean_dec(x_169);
x_14 = x_129;
x_15 = x_170;
goto block_126;
}
else
{
lean_object* x_171; 
lean_dec(x_129);
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
lean_dec(x_168);
x_14 = x_171;
x_15 = x_13;
goto block_126;
}
}
default: 
{
lean_object* x_172; uint8_t x_173; 
lean_inc(x_134);
x_172 = l_Lake_Glob_decodeToml(x_134);
x_173 = !lean_is_exclusive(x_134);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_134, 1);
lean_dec(x_174);
x_175 = lean_ctor_get(x_134, 0);
lean_dec(x_175);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_172, 0);
lean_inc(x_176);
lean_dec(x_172);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_11);
lean_ctor_set(x_134, 0, x_176);
x_177 = lean_array_mk(x_134);
x_178 = l_Array_append___rarg(x_13, x_177);
lean_dec(x_177);
x_14 = x_129;
x_15 = x_178;
goto block_126;
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_dec(x_129);
x_179 = lean_ctor_get(x_172, 0);
lean_inc(x_179);
lean_dec(x_172);
lean_ctor_set_tag(x_134, 1);
lean_ctor_set(x_134, 1, x_11);
lean_ctor_set(x_134, 0, x_179);
x_180 = lean_array_mk(x_134);
x_14 = x_180;
x_15 = x_13;
goto block_126;
}
}
else
{
lean_dec(x_134);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_ctor_get(x_172, 0);
lean_inc(x_181);
lean_dec(x_172);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_11);
x_183 = lean_array_mk(x_182);
x_184 = l_Array_append___rarg(x_13, x_183);
lean_dec(x_183);
x_14 = x_129;
x_15 = x_184;
goto block_126;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_129);
x_185 = lean_ctor_get(x_172, 0);
lean_inc(x_185);
lean_dec(x_172);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_11);
x_187 = lean_array_mk(x_186);
x_14 = x_187;
x_15 = x_13;
goto block_126;
}
}
}
}
}
block_126:
{
lean_object* x_16; lean_object* x_17; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_100 = 0;
x_101 = l_Lake_StrPat_decodeToml___closed__6;
x_102 = l_Lean_Name_toString(x_1, x_100, x_101);
x_108 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_109 = l_Lake_LeanLibConfig_decodeToml___closed__10;
lean_inc(x_2);
x_110 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_108, x_109, x_2);
if (lean_obj_tag(x_110) == 0)
{
x_16 = x_102;
x_17 = x_15;
goto block_99;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
switch (lean_obj_tag(x_112)) {
case 0:
{
lean_object* x_113; 
lean_dec(x_102);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_16 = x_113;
x_17 = x_15;
goto block_99;
}
case 2:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_112, 0);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lake_Glob_decodeToml___closed__2;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_103 = x_116;
goto block_107;
}
case 3:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_112, 0);
lean_inc(x_117);
lean_dec(x_112);
x_118 = l_Lake_Glob_decodeToml___closed__2;
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_103 = x_119;
goto block_107;
}
default: 
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_112);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_112, 1);
lean_dec(x_121);
x_122 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_112, 0);
lean_ctor_set(x_112, 1, x_122);
x_103 = x_112;
goto block_107;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_112, 0);
lean_inc(x_123);
lean_dec(x_112);
x_124 = l_Lake_Glob_decodeToml___closed__2;
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_103 = x_125;
goto block_107;
}
}
}
}
block_99:
{
uint8_t x_18; lean_object* x_19; lean_object* x_71; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_78 = l_Lake_PackageConfig_decodeToml___closed__62;
lean_inc(x_2);
x_79 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_77, x_78, x_2);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = 0;
x_18 = x_80;
x_19 = x_17;
goto block_70;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
switch (lean_obj_tag(x_82)) {
case 0:
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 1);
lean_dec(x_84);
x_85 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_82, 1, x_85);
x_71 = x_82;
goto block_76;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_82, 0);
lean_inc(x_86);
lean_dec(x_82);
x_87 = l_Lake_LeanConfig_decodeToml___closed__20;
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_71 = x_88;
goto block_76;
}
}
case 2:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_82, 0);
lean_inc(x_89);
lean_dec(x_82);
x_90 = l_Lake_LeanConfig_decodeToml___closed__20;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_71 = x_91;
goto block_76;
}
case 3:
{
uint8_t x_92; 
x_92 = lean_ctor_get_uint8(x_82, sizeof(void*)*1);
lean_dec(x_82);
x_18 = x_92;
x_19 = x_17;
goto block_70;
}
default: 
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_82);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_82, 1);
lean_dec(x_94);
x_95 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_82, 0);
lean_ctor_set(x_82, 1, x_95);
x_71 = x_82;
goto block_76;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_82, 0);
lean_inc(x_96);
lean_dec(x_82);
x_97 = l_Lake_LeanConfig_decodeToml___closed__20;
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_71 = x_98;
goto block_76;
}
}
}
}
block_70:
{
lean_object* x_20; lean_object* x_21; lean_object* x_34; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_41 = l_Lake_LeanLibConfig_decodeToml___closed__4;
lean_inc(x_2);
x_42 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_40, x_41, x_2);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_20 = x_43;
x_21 = x_19;
goto block_33;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
switch (lean_obj_tag(x_45)) {
case 0:
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 1);
lean_dec(x_47);
x_48 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_45, 1, x_48);
x_34 = x_45;
goto block_39;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec(x_45);
x_50 = l_Lake_LeanConfig_decodeToml___closed__5;
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_34 = x_51;
goto block_39;
}
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
x_53 = l_Lake_LeanConfig_decodeToml___closed__5;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_34 = x_54;
goto block_39;
}
case 3:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
lean_dec(x_45);
x_56 = l_Lake_LeanConfig_decodeToml___closed__5;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_34 = x_57;
goto block_39;
}
case 5:
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec(x_45);
x_59 = l_Lake_Toml_decodeArray___at_Lake_LeanLibConfig_decodeToml___spec__1(x_58);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = l_Array_append___rarg(x_19, x_60);
lean_dec(x_60);
x_62 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_20 = x_62;
x_21 = x_61;
goto block_33;
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
lean_dec(x_59);
x_20 = x_63;
x_21 = x_19;
goto block_33;
}
}
default: 
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_45);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_45, 1);
lean_dec(x_65);
x_66 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_45, 0);
lean_ctor_set(x_45, 1, x_66);
x_34 = x_45;
goto block_39;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_45, 0);
lean_inc(x_67);
lean_dec(x_45);
x_68 = l_Lake_LeanConfig_decodeToml___closed__5;
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_34 = x_69;
goto block_39;
}
}
}
}
block_33:
{
lean_object* x_22; 
x_22 = l_Lake_LeanConfig_decodeToml(x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_append___rarg(x_21, x_23);
lean_dec(x_23);
x_25 = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed), 2, 1);
lean_closure_set(x_25, 0, x_11);
x_26 = l_Lake_PackageConfig_decodeToml___closed__7;
x_27 = l_Lake_decodeLeanOptions___closed__1;
x_28 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_12);
lean_ctor_set(x_28, 3, x_14);
lean_ctor_set(x_28, 4, x_16);
lean_ctor_set(x_28, 5, x_27);
lean_ctor_set(x_28, 6, x_20);
lean_ctor_set(x_28, 7, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*8, x_18);
x_3 = x_28;
x_4 = x_24;
goto block_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_decodeToml___lambda__1___boxed), 2, 1);
lean_closure_set(x_30, 0, x_11);
x_31 = l_Lake_decodeLeanOptions___closed__1;
x_32 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_12);
lean_ctor_set(x_32, 3, x_14);
lean_ctor_set(x_32, 4, x_16);
lean_ctor_set(x_32, 5, x_31);
lean_ctor_set(x_32, 6, x_20);
lean_ctor_set(x_32, 7, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*8, x_18);
x_3 = x_32;
x_4 = x_21;
goto block_8;
}
}
block_39:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_11);
x_36 = lean_array_mk(x_35);
x_37 = l_Array_append___rarg(x_19, x_36);
lean_dec(x_36);
x_38 = l_Lake_LeanLibConfig_decodeToml___closed__8;
x_20 = x_38;
x_21 = x_37;
goto block_33;
}
}
block_76:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_11);
x_73 = lean_array_mk(x_72);
x_74 = l_Array_append___rarg(x_17, x_73);
lean_dec(x_73);
x_75 = 0;
x_18 = x_75;
x_19 = x_74;
goto block_70;
}
}
block_107:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_11);
x_105 = lean_array_mk(x_104);
x_106 = l_Array_append___rarg(x_15, x_105);
lean_dec(x_105);
x_16 = x_102;
x_17 = x_106;
goto block_99;
}
}
}
block_195:
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_191);
lean_ctor_set(x_192, 1, x_11);
x_193 = lean_array_mk(x_192);
x_194 = l_Array_append___rarg(x_10, x_193);
lean_dec(x_193);
x_12 = x_190;
x_13 = x_194;
goto block_188;
}
}
block_232:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_box(0);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_array_mk(x_227);
x_229 = l_Lake_LeanOption_decodeToml___closed__3;
x_230 = l_Array_append___rarg(x_229, x_228);
lean_dec(x_228);
x_231 = l_Lake_PackageConfig_decodeToml___closed__58;
x_9 = x_231;
x_10 = x_230;
goto block_224;
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
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanLibConfig___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_2, 1, x_11);
x_3 = x_2;
goto block_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_3 = x_14;
goto block_8;
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_3 = x_17;
goto block_8;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_3 = x_20;
goto block_8;
}
case 6:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l_Lake_LeanLibConfig_decodeToml(x_1, x_21);
return x_22;
}
default: 
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 1);
lean_dec(x_24);
x_25 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_25);
x_3 = x_2;
goto block_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_3 = x_28;
goto block_8;
}
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_mk(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanLibConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instDecodeTomlLeanLibConfig___lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
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
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_122; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_131 = l_Lake_PackageConfig_decodeToml___closed__60;
lean_inc(x_2);
x_132 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_130, x_131, x_2);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = l_Lake_PackageConfig_decodeToml___closed__58;
x_134 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_133;
x_10 = x_134;
goto block_121;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_132, 0);
lean_inc(x_135);
lean_dec(x_132);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
switch (lean_obj_tag(x_136)) {
case 0:
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_138 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_137;
x_10 = x_138;
goto block_121;
}
case 2:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
lean_dec(x_136);
x_140 = l_Lake_Glob_decodeToml___closed__2;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_122 = x_141;
goto block_129;
}
case 3:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_136, 0);
lean_inc(x_142);
lean_dec(x_136);
x_143 = l_Lake_Glob_decodeToml___closed__2;
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_122 = x_144;
goto block_129;
}
default: 
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_136);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_136, 1);
lean_dec(x_146);
x_147 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_136, 0);
lean_ctor_set(x_136, 1, x_147);
x_122 = x_136;
goto block_129;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_136, 0);
lean_inc(x_148);
lean_dec(x_136);
x_149 = l_Lake_Glob_decodeToml___closed__2;
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_122 = x_150;
goto block_129;
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
block_121:
{
lean_object* x_11; lean_object* x_12; lean_object* x_88; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_95 = l_Lake_LeanExeConfig_decodeToml___closed__7;
lean_inc(x_2);
x_96 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_94, x_95, x_2);
if (lean_obj_tag(x_96) == 0)
{
lean_inc(x_1);
x_11 = x_1;
x_12 = x_10;
goto block_87;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
switch (lean_obj_tag(x_98)) {
case 0:
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_ctor_get(x_98, 1);
x_102 = l_String_toName(x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
lean_ctor_set(x_98, 1, x_103);
x_88 = x_98;
goto block_93;
}
else
{
lean_free_object(x_98);
lean_dec(x_100);
x_11 = x_102;
x_12 = x_10;
goto block_87;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_98, 0);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_98);
x_106 = l_String_toName(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = l_Lake_Toml_decodeKeyval___at_Lake_LeanOption_decodeToml___spec__2___closed__1;
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
x_88 = x_108;
goto block_93;
}
else
{
lean_dec(x_104);
x_11 = x_106;
x_12 = x_10;
goto block_87;
}
}
}
case 2:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_98, 0);
lean_inc(x_109);
lean_dec(x_98);
x_110 = l_Lake_Glob_decodeToml___closed__2;
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_88 = x_111;
goto block_93;
}
case 3:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_98, 0);
lean_inc(x_112);
lean_dec(x_98);
x_113 = l_Lake_Glob_decodeToml___closed__2;
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_88 = x_114;
goto block_93;
}
default: 
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_98);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_98, 1);
lean_dec(x_116);
x_117 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_98, 0);
lean_ctor_set(x_98, 1, x_117);
x_88 = x_98;
goto block_93;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_98, 0);
lean_inc(x_118);
lean_dec(x_98);
x_119 = l_Lake_Glob_decodeToml___closed__2;
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_88 = x_120;
goto block_93;
}
}
}
}
block_87:
{
lean_object* x_13; lean_object* x_14; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_59 = l_Lake_PackageConfig_decodeToml___closed__5;
x_60 = 0;
x_61 = l_Lake_StrPat_decodeToml___closed__6;
x_62 = l_Lean_Name_toStringWithSep(x_59, x_60, x_1, x_61);
x_69 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_70 = l_Lake_LeanExeConfig_decodeToml___closed__5;
lean_inc(x_2);
x_71 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_69, x_70, x_2);
if (lean_obj_tag(x_71) == 0)
{
x_13 = x_62;
x_14 = x_12;
goto block_58;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
switch (lean_obj_tag(x_73)) {
case 0:
{
lean_object* x_74; 
lean_dec(x_62);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_13 = x_74;
x_14 = x_12;
goto block_58;
}
case 2:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lake_Glob_decodeToml___closed__2;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_63 = x_77;
goto block_68;
}
case 3:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_73, 0);
lean_inc(x_78);
lean_dec(x_73);
x_79 = l_Lake_Glob_decodeToml___closed__2;
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_63 = x_80;
goto block_68;
}
default: 
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_73);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_73, 1);
lean_dec(x_82);
x_83 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_73, 0);
lean_ctor_set(x_73, 1, x_83);
x_63 = x_73;
goto block_68;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_73, 0);
lean_inc(x_84);
lean_dec(x_73);
x_85 = l_Lake_Glob_decodeToml___closed__2;
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_63 = x_86;
goto block_68;
}
}
}
}
block_58:
{
uint8_t x_15; lean_object* x_16; lean_object* x_29; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_37 = l_Lake_LeanExeConfig_decodeToml___closed__3;
lean_inc(x_2);
x_38 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_36, x_37, x_2);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = 0;
x_15 = x_39;
x_16 = x_14;
goto block_28;
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
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 1);
lean_dec(x_43);
x_44 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set(x_41, 1, x_44);
x_29 = x_41;
goto block_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_dec(x_41);
x_46 = l_Lake_LeanConfig_decodeToml___closed__20;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_29 = x_47;
goto block_35;
}
}
case 2:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_41, 0);
lean_inc(x_48);
lean_dec(x_41);
x_49 = l_Lake_LeanConfig_decodeToml___closed__20;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_29 = x_50;
goto block_35;
}
case 3:
{
uint8_t x_51; 
x_51 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
x_15 = x_51;
x_16 = x_14;
goto block_28;
}
default: 
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_41, 1);
lean_dec(x_53);
x_54 = l_Lake_LeanConfig_decodeToml___closed__20;
lean_ctor_set_tag(x_41, 0);
lean_ctor_set(x_41, 1, x_54);
x_29 = x_41;
goto block_35;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_41, 0);
lean_inc(x_55);
lean_dec(x_41);
x_56 = l_Lake_LeanConfig_decodeToml___closed__20;
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_29 = x_57;
goto block_35;
}
}
}
}
block_28:
{
lean_object* x_17; 
x_17 = l_Lake_LeanConfig_decodeToml(x_2);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Array_append___rarg(x_16, x_18);
lean_dec(x_18);
x_20 = l_Lake_PackageConfig_decodeToml___closed__7;
x_21 = l_Lake_decodeLeanOptions___closed__1;
x_22 = l_Lake_LeanExeConfig_decodeToml___closed__1;
x_23 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_9);
lean_ctor_set(x_23, 2, x_11);
lean_ctor_set(x_23, 3, x_13);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*6, x_15);
x_3 = x_23;
x_4 = x_19;
goto block_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l_Lake_decodeLeanOptions___closed__1;
x_26 = l_Lake_LeanExeConfig_decodeToml___closed__1;
x_27 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_11);
lean_ctor_set(x_27, 3, x_13);
lean_ctor_set(x_27, 4, x_25);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_15);
x_3 = x_27;
x_4 = x_16;
goto block_8;
}
}
block_35:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_array_mk(x_31);
x_33 = l_Array_append___rarg(x_14, x_32);
lean_dec(x_32);
x_34 = 0;
x_15 = x_34;
x_16 = x_33;
goto block_28;
}
}
block_68:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_array_mk(x_65);
x_67 = l_Array_append___rarg(x_12, x_66);
lean_dec(x_66);
x_13 = x_62;
x_14 = x_67;
goto block_58;
}
}
block_93:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_array_mk(x_90);
x_92 = l_Array_append___rarg(x_10, x_91);
lean_dec(x_91);
lean_inc(x_1);
x_11 = x_1;
x_12 = x_92;
goto block_87;
}
}
block_129:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_123 = lean_box(0);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_array_mk(x_124);
x_126 = l_Lake_LeanOption_decodeToml___closed__3;
x_127 = l_Array_append___rarg(x_126, x_125);
lean_dec(x_125);
x_128 = l_Lake_PackageConfig_decodeToml___closed__58;
x_9 = x_128;
x_10 = x_127;
goto block_121;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanExeConfig___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
lean_dec(x_10);
x_11 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_2, 1, x_11);
x_3 = x_2;
goto block_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_3 = x_14;
goto block_8;
}
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_3 = x_17;
goto block_8;
}
case 3:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_3 = x_20;
goto block_8;
}
case 6:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_dec(x_2);
x_22 = l_Lake_LeanExeConfig_decodeToml(x_1, x_21);
return x_22;
}
default: 
{
uint8_t x_23; 
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 1);
lean_dec(x_24);
x_25 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_25);
x_3 = x_2;
goto block_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_3 = x_28;
goto block_8;
}
}
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_mk(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlLeanExeConfig(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instDecodeTomlLeanExeConfig___lambda__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_mk(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lake_Toml_decodeKeyval___at_Lake_StrPat_decodeToml___spec__4(x_2, x_17);
lean_dec(x_2);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lake_Glob_decodeToml___closed__2;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_3 = x_16;
goto block_11;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lake_Glob_decodeToml___closed__2;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_3 = x_19;
goto block_11;
}
default: 
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 1);
lean_dec(x_21);
x_22 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_22);
x_3 = x_2;
goto block_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lake_Glob_decodeToml___closed__2;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_3 = x_25;
goto block_11;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_array_mk(x_5);
x_7 = lean_array_size(x_6);
x_8 = 0;
x_9 = l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__4(x_1, x_7, x_8, x_6);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
lean_inc(x_2);
x_5 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_4, x_2, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
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
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_array_mk(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__3(x_2, x_17);
lean_dec(x_2);
return x_18;
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
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__10;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DependencySrc_decodeToml___closed__11;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_DependencySrc_decodeToml___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("path", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expected one of 'path' or 'git'", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("url", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dir", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_DependencySrc_decodeToml___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_DependencySrc_decodeToml___closed__19;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_DependencySrc_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_99; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_106 = l_Lake_DependencySrc_decodeToml___closed__6;
lean_inc(x_1);
x_107 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_105, x_106, x_1);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
lean_dec(x_2);
lean_dec(x_1);
x_108 = l_Lake_DependencySrc_decodeToml___closed__13;
return x_108;
}
else
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_107, 0);
x_111 = lean_ctor_get(x_110, 1);
lean_inc(x_111);
lean_dec(x_110);
switch (lean_obj_tag(x_111)) {
case 0:
{
uint8_t x_112; 
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
x_115 = l_Lake_DependencySrc_decodeToml___closed__14;
x_116 = lean_string_dec_eq(x_114, x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = l_Lake_DependencySrc_decodeToml___closed__15;
x_118 = lean_string_dec_eq(x_114, x_117);
lean_dec(x_114);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_box(0);
x_120 = l_Lake_DependencySrc_decodeToml___closed__16;
lean_ctor_set(x_111, 1, x_120);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_111);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_array_mk(x_121);
lean_ctor_set_tag(x_107, 0);
lean_ctor_set(x_107, 0, x_122);
return x_107;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_free_object(x_111);
lean_dec(x_113);
lean_free_object(x_107);
x_123 = l_Lake_DependencySrc_decodeToml___closed__18;
lean_inc(x_1);
x_124 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_123, x_2);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Lake_LeanOption_decodeToml___closed__3;
x_127 = l_Array_append___rarg(x_126, x_125);
lean_dec(x_125);
x_128 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_128;
x_10 = x_127;
goto block_98;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_124, 0);
lean_inc(x_129);
lean_dec(x_124);
x_130 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_129;
x_10 = x_130;
goto block_98;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_free_object(x_111);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_2);
x_131 = l_Lake_DependencySrc_decodeToml___closed__20;
x_132 = lean_box(0);
x_133 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__2(x_1, x_131, x_132);
if (lean_obj_tag(x_133) == 0)
{
uint8_t x_134; 
lean_free_object(x_107);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
return x_133;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
else
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_133);
if (x_137 == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_133, 0);
lean_ctor_set_tag(x_107, 0);
lean_ctor_set(x_107, 0, x_138);
lean_ctor_set(x_133, 0, x_107);
return x_133;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_133, 0);
lean_inc(x_139);
lean_dec(x_133);
lean_ctor_set_tag(x_107, 0);
lean_ctor_set(x_107, 0, x_139);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_107);
return x_140;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_111, 0);
x_142 = lean_ctor_get(x_111, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_111);
x_143 = l_Lake_DependencySrc_decodeToml___closed__14;
x_144 = lean_string_dec_eq(x_142, x_143);
if (x_144 == 0)
{
lean_object* x_145; uint8_t x_146; 
x_145 = l_Lake_DependencySrc_decodeToml___closed__15;
x_146 = lean_string_dec_eq(x_142, x_145);
lean_dec(x_142);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_2);
lean_dec(x_1);
x_147 = lean_box(0);
x_148 = l_Lake_DependencySrc_decodeToml___closed__16;
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_141);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
x_151 = lean_array_mk(x_150);
lean_ctor_set_tag(x_107, 0);
lean_ctor_set(x_107, 0, x_151);
return x_107;
}
else
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_141);
lean_free_object(x_107);
x_152 = l_Lake_DependencySrc_decodeToml___closed__18;
lean_inc(x_1);
x_153 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_152, x_2);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec(x_153);
x_155 = l_Lake_LeanOption_decodeToml___closed__3;
x_156 = l_Array_append___rarg(x_155, x_154);
lean_dec(x_154);
x_157 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_157;
x_10 = x_156;
goto block_98;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_153, 0);
lean_inc(x_158);
lean_dec(x_153);
x_159 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_158;
x_10 = x_159;
goto block_98;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_2);
x_160 = l_Lake_DependencySrc_decodeToml___closed__20;
x_161 = lean_box(0);
x_162 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__2(x_1, x_160, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_free_object(x_107);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 1, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_163);
return x_165;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_162, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 x_167 = x_162;
} else {
 lean_dec_ref(x_162);
 x_167 = lean_box(0);
}
lean_ctor_set_tag(x_107, 0);
lean_ctor_set(x_107, 0, x_166);
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(1, 1, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_107);
return x_168;
}
}
}
}
case 2:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_free_object(x_107);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_ctor_get(x_111, 0);
lean_inc(x_169);
lean_dec(x_111);
x_170 = l_Lake_Glob_decodeToml___closed__2;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
x_99 = x_171;
goto block_104;
}
case 3:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_free_object(x_107);
lean_dec(x_2);
lean_dec(x_1);
x_172 = lean_ctor_get(x_111, 0);
lean_inc(x_172);
lean_dec(x_111);
x_173 = l_Lake_Glob_decodeToml___closed__2;
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_99 = x_174;
goto block_104;
}
default: 
{
uint8_t x_175; 
lean_free_object(x_107);
lean_dec(x_2);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_111);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_111, 1);
lean_dec(x_176);
x_177 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_111, 0);
lean_ctor_set(x_111, 1, x_177);
x_99 = x_111;
goto block_104;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_111, 0);
lean_inc(x_178);
lean_dec(x_111);
x_179 = l_Lake_Glob_decodeToml___closed__2;
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_99 = x_180;
goto block_104;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_107, 0);
lean_inc(x_181);
lean_dec(x_107);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
switch (lean_obj_tag(x_182)) {
case 0:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_185 = x_182;
} else {
 lean_dec_ref(x_182);
 x_185 = lean_box(0);
}
x_186 = l_Lake_DependencySrc_decodeToml___closed__14;
x_187 = lean_string_dec_eq(x_184, x_186);
if (x_187 == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = l_Lake_DependencySrc_decodeToml___closed__15;
x_189 = lean_string_dec_eq(x_184, x_188);
lean_dec(x_184);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_box(0);
x_191 = l_Lake_DependencySrc_decodeToml___closed__16;
if (lean_is_scalar(x_185)) {
 x_192 = lean_alloc_ctor(0, 2, 0);
} else {
 x_192 = x_185;
}
lean_ctor_set(x_192, 0, x_183);
lean_ctor_set(x_192, 1, x_191);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_190);
x_194 = lean_array_mk(x_193);
x_195 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_185);
lean_dec(x_183);
x_196 = l_Lake_DependencySrc_decodeToml___closed__18;
lean_inc(x_1);
x_197 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_196, x_2);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
lean_dec(x_197);
x_199 = l_Lake_LeanOption_decodeToml___closed__3;
x_200 = l_Array_append___rarg(x_199, x_198);
lean_dec(x_198);
x_201 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_201;
x_10 = x_200;
goto block_98;
}
else
{
lean_object* x_202; lean_object* x_203; 
x_202 = lean_ctor_get(x_197, 0);
lean_inc(x_202);
lean_dec(x_197);
x_203 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_202;
x_10 = x_203;
goto block_98;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_2);
x_204 = l_Lake_DependencySrc_decodeToml___closed__20;
x_205 = lean_box(0);
x_206 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__2(x_1, x_204, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(0, 1, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_207);
return x_209;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_210 = lean_ctor_get(x_206, 0);
lean_inc(x_210);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_211 = x_206;
} else {
 lean_dec_ref(x_206);
 x_211 = lean_box(0);
}
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_210);
if (lean_is_scalar(x_211)) {
 x_213 = lean_alloc_ctor(1, 1, 0);
} else {
 x_213 = x_211;
}
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
}
case 2:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_2);
lean_dec(x_1);
x_214 = lean_ctor_get(x_182, 0);
lean_inc(x_214);
lean_dec(x_182);
x_215 = l_Lake_Glob_decodeToml___closed__2;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_99 = x_216;
goto block_104;
}
case 3:
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_2);
lean_dec(x_1);
x_217 = lean_ctor_get(x_182, 0);
lean_inc(x_217);
lean_dec(x_182);
x_218 = l_Lake_Glob_decodeToml___closed__2;
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_99 = x_219;
goto block_104;
}
default: 
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_182, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_221 = x_182;
} else {
 lean_dec_ref(x_182);
 x_221 = lean_box(0);
}
x_222 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_221;
 lean_ctor_set_tag(x_223, 0);
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_222);
x_99 = x_223;
goto block_104;
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
block_98:
{
lean_object* x_11; lean_object* x_12; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_59 = l_Lake_DependencySrc_decodeToml___closed__4;
lean_inc(x_1);
x_60 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_58, x_59, x_1);
x_61 = lean_box(0);
if (lean_obj_tag(x_60) == 0)
{
x_11 = x_61;
x_12 = x_10;
goto block_57;
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_60, 0);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
switch (lean_obj_tag(x_70)) {
case 0:
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_ctor_set(x_60, 0, x_71);
x_11 = x_60;
x_12 = x_10;
goto block_57;
}
case 2:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_free_object(x_60);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lake_Glob_decodeToml___closed__2;
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_62 = x_74;
goto block_67;
}
case 3:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_free_object(x_60);
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec(x_70);
x_76 = l_Lake_Glob_decodeToml___closed__2;
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_62 = x_77;
goto block_67;
}
default: 
{
uint8_t x_78; 
lean_free_object(x_60);
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_70, 1);
lean_dec(x_79);
x_80 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_70, 0);
lean_ctor_set(x_70, 1, x_80);
x_62 = x_70;
goto block_67;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_70, 0);
lean_inc(x_81);
lean_dec(x_70);
x_82 = l_Lake_Glob_decodeToml___closed__2;
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_62 = x_83;
goto block_67;
}
}
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_60, 0);
lean_inc(x_84);
lean_dec(x_60);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
switch (lean_obj_tag(x_85)) {
case 0:
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_11 = x_87;
x_12 = x_10;
goto block_57;
}
case 2:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec(x_85);
x_89 = l_Lake_Glob_decodeToml___closed__2;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_62 = x_90;
goto block_67;
}
case 3:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_85, 0);
lean_inc(x_91);
lean_dec(x_85);
x_92 = l_Lake_Glob_decodeToml___closed__2;
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_62 = x_93;
goto block_67;
}
default: 
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_85, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_95 = x_85;
} else {
 lean_dec_ref(x_85);
 x_95 = lean_box(0);
}
x_96 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
 lean_ctor_set_tag(x_97, 0);
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_62 = x_97;
goto block_67;
}
}
}
}
block_57:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_14 = l_Lake_DependencySrc_decodeToml___closed__2;
x_15 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_13, x_14, x_1);
x_16 = lean_box(0);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_9);
lean_ctor_set(x_24, 1, x_11);
lean_ctor_set(x_24, 2, x_16);
x_3 = x_24;
x_4 = x_12;
goto block_8;
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
switch (lean_obj_tag(x_27)) {
case 0:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
lean_ctor_set(x_15, 0, x_28);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_9);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_15);
x_3 = x_29;
x_4 = x_12;
goto block_8;
}
case 2:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_15);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = l_Lake_Glob_decodeToml___closed__2;
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_17 = x_32;
goto block_23;
}
case 3:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_15);
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
lean_dec(x_27);
x_34 = l_Lake_Glob_decodeToml___closed__2;
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_17 = x_35;
goto block_23;
}
default: 
{
uint8_t x_36; 
lean_free_object(x_15);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 1);
lean_dec(x_37);
x_38 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 1, x_38);
x_17 = x_27;
goto block_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
lean_dec(x_27);
x_40 = l_Lake_Glob_decodeToml___closed__2;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_17 = x_41;
goto block_23;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_15, 0);
lean_inc(x_42);
lean_dec(x_15);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
switch (lean_obj_tag(x_43)) {
case 0:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_46, 0, x_9);
lean_ctor_set(x_46, 1, x_11);
lean_ctor_set(x_46, 2, x_45);
x_3 = x_46;
x_4 = x_12;
goto block_8;
}
case 2:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_43, 0);
lean_inc(x_47);
lean_dec(x_43);
x_48 = l_Lake_Glob_decodeToml___closed__2;
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_17 = x_49;
goto block_23;
}
case 3:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_43, 0);
lean_inc(x_50);
lean_dec(x_43);
x_51 = l_Lake_Glob_decodeToml___closed__2;
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_17 = x_52;
goto block_23;
}
default: 
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_43, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_54 = x_43;
} else {
 lean_dec_ref(x_43);
 x_54 = lean_box(0);
}
x_55 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
 lean_ctor_set_tag(x_56, 0);
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_17 = x_56;
goto block_23;
}
}
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_mk(x_19);
x_21 = l_Array_append___rarg(x_12, x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_16);
x_3 = x_22;
x_4 = x_21;
goto block_8;
}
}
block_67:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_array_mk(x_64);
x_66 = l_Array_append___rarg(x_10, x_65);
lean_dec(x_65);
x_11 = x_61;
x_12 = x_66;
goto block_57;
}
}
block_104:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_array_mk(x_101);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lake_DependencySrc_decodeToml___spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_decodeKeyval___at_Lake_DependencySrc_decodeToml___spec__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependencySrc___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_1, 1, x_10);
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_2 = x_13;
goto block_7;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
goto block_7;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_19;
goto block_7;
}
case 6:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lake_DependencySrc_decodeToml(x_21, x_20);
return x_22;
}
default: 
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_25);
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_2 = x_28;
goto block_7;
}
}
}
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_mk(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lake_instDecodeTomlDependencySrc___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instDecodeTomlDependencySrc___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instDecodeTomlDependencySrc() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instDecodeTomlDependencySrc___closed__1;
return x_1;
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
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_11 = x_6;
} else {
 lean_dec_ref(x_6);
 x_11 = lean_box(0);
}
x_12 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at_Lake_Dependency_decodeToml___spec__2___lambda__1), 3, 1);
lean_closure_set(x_12, 0, x_9);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_11);
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lake_mergeErrors___rarg(x_4, x_22, x_12);
x_2 = x_8;
x_4 = x_23;
goto _start;
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
lean_dec(x_10);
x_26 = l_Lake_Glob_decodeToml___closed__2;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_13 = x_27;
goto block_20;
}
case 3:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_dec(x_10);
x_29 = l_Lake_Glob_decodeToml___closed__2;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_13 = x_30;
goto block_20;
}
default: 
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_10, 1);
lean_dec(x_32);
x_33 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_33);
x_13 = x_10;
goto block_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_10, 0);
lean_inc(x_34);
lean_dec(x_10);
x_35 = l_Lake_Glob_decodeToml___closed__2;
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_13 = x_36;
goto block_20;
}
}
}
block_20:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_15 = lean_alloc_ctor(1, 2, 0);
} else {
 x_15 = x_11;
 lean_ctor_set_tag(x_15, 1);
}
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_mk(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lake_mergeErrors___rarg(x_4, x_17, x_12);
x_2 = x_8;
x_4 = x_18;
goto _start;
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
x_2 = l_Lake_DependencySrc_decodeToml___closed__15;
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
x_2 = l_Lake_DependencySrc_decodeToml___closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Dependency_decodeToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; lean_object* x_10; lean_object* x_1642; lean_object* x_1643; 
x_1642 = l_Lake_LeanOption_decodeToml___closed__10;
lean_inc(x_1);
x_1643 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1, x_1642, x_2);
if (lean_obj_tag(x_1643) == 0)
{
lean_object* x_1644; lean_object* x_1645; lean_object* x_1646; lean_object* x_1647; 
x_1644 = lean_ctor_get(x_1643, 0);
lean_inc(x_1644);
lean_dec(x_1643);
x_1645 = l_Lake_LeanOption_decodeToml___closed__3;
x_1646 = l_Array_append___rarg(x_1645, x_1644);
lean_dec(x_1644);
x_1647 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_9 = x_1647;
x_10 = x_1646;
goto block_1641;
}
else
{
lean_object* x_1648; lean_object* x_1649; 
x_1648 = lean_ctor_get(x_1643, 0);
lean_inc(x_1648);
lean_dec(x_1643);
x_1649 = l_Lake_LeanOption_decodeToml___closed__3;
x_9 = x_1648;
x_10 = x_1649;
goto block_1641;
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
block_1641:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; 
x_11 = l_Lake_stringToLegalOrSimpleName(x_9);
x_1601 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_1602 = l_Lake_DependencySrc_decodeToml___closed__4;
lean_inc(x_1);
x_1603 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1601, x_1602, x_1);
x_1604 = lean_box(0);
if (lean_obj_tag(x_1603) == 0)
{
x_12 = x_1604;
x_13 = x_10;
goto block_1600;
}
else
{
uint8_t x_1611; 
x_1611 = !lean_is_exclusive(x_1603);
if (x_1611 == 0)
{
lean_object* x_1612; lean_object* x_1613; 
x_1612 = lean_ctor_get(x_1603, 0);
x_1613 = lean_ctor_get(x_1612, 1);
lean_inc(x_1613);
lean_dec(x_1612);
switch (lean_obj_tag(x_1613)) {
case 0:
{
lean_object* x_1614; 
x_1614 = lean_ctor_get(x_1613, 1);
lean_inc(x_1614);
lean_dec(x_1613);
lean_ctor_set(x_1603, 0, x_1614);
x_12 = x_1603;
x_13 = x_10;
goto block_1600;
}
case 2:
{
lean_object* x_1615; lean_object* x_1616; lean_object* x_1617; 
lean_free_object(x_1603);
x_1615 = lean_ctor_get(x_1613, 0);
lean_inc(x_1615);
lean_dec(x_1613);
x_1616 = l_Lake_Glob_decodeToml___closed__2;
x_1617 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1617, 0, x_1615);
lean_ctor_set(x_1617, 1, x_1616);
x_1605 = x_1617;
goto block_1610;
}
case 3:
{
lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; 
lean_free_object(x_1603);
x_1618 = lean_ctor_get(x_1613, 0);
lean_inc(x_1618);
lean_dec(x_1613);
x_1619 = l_Lake_Glob_decodeToml___closed__2;
x_1620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1620, 0, x_1618);
lean_ctor_set(x_1620, 1, x_1619);
x_1605 = x_1620;
goto block_1610;
}
default: 
{
uint8_t x_1621; 
lean_free_object(x_1603);
x_1621 = !lean_is_exclusive(x_1613);
if (x_1621 == 0)
{
lean_object* x_1622; lean_object* x_1623; 
x_1622 = lean_ctor_get(x_1613, 1);
lean_dec(x_1622);
x_1623 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1613, 0);
lean_ctor_set(x_1613, 1, x_1623);
x_1605 = x_1613;
goto block_1610;
}
else
{
lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; 
x_1624 = lean_ctor_get(x_1613, 0);
lean_inc(x_1624);
lean_dec(x_1613);
x_1625 = l_Lake_Glob_decodeToml___closed__2;
x_1626 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1626, 0, x_1624);
lean_ctor_set(x_1626, 1, x_1625);
x_1605 = x_1626;
goto block_1610;
}
}
}
}
else
{
lean_object* x_1627; lean_object* x_1628; 
x_1627 = lean_ctor_get(x_1603, 0);
lean_inc(x_1627);
lean_dec(x_1603);
x_1628 = lean_ctor_get(x_1627, 1);
lean_inc(x_1628);
lean_dec(x_1627);
switch (lean_obj_tag(x_1628)) {
case 0:
{
lean_object* x_1629; lean_object* x_1630; 
x_1629 = lean_ctor_get(x_1628, 1);
lean_inc(x_1629);
lean_dec(x_1628);
x_1630 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1630, 0, x_1629);
x_12 = x_1630;
x_13 = x_10;
goto block_1600;
}
case 2:
{
lean_object* x_1631; lean_object* x_1632; lean_object* x_1633; 
x_1631 = lean_ctor_get(x_1628, 0);
lean_inc(x_1631);
lean_dec(x_1628);
x_1632 = l_Lake_Glob_decodeToml___closed__2;
x_1633 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1633, 0, x_1631);
lean_ctor_set(x_1633, 1, x_1632);
x_1605 = x_1633;
goto block_1610;
}
case 3:
{
lean_object* x_1634; lean_object* x_1635; lean_object* x_1636; 
x_1634 = lean_ctor_get(x_1628, 0);
lean_inc(x_1634);
lean_dec(x_1628);
x_1635 = l_Lake_Glob_decodeToml___closed__2;
x_1636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1636, 0, x_1634);
lean_ctor_set(x_1636, 1, x_1635);
x_1605 = x_1636;
goto block_1610;
}
default: 
{
lean_object* x_1637; lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; 
x_1637 = lean_ctor_get(x_1628, 0);
lean_inc(x_1637);
if (lean_is_exclusive(x_1628)) {
 lean_ctor_release(x_1628, 0);
 lean_ctor_release(x_1628, 1);
 x_1638 = x_1628;
} else {
 lean_dec_ref(x_1628);
 x_1638 = lean_box(0);
}
x_1639 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_1638)) {
 x_1640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1640 = x_1638;
 lean_ctor_set_tag(x_1640, 0);
}
lean_ctor_set(x_1640, 0, x_1637);
lean_ctor_set(x_1640, 1, x_1639);
x_1605 = x_1640;
goto block_1610;
}
}
}
}
block_1600:
{
lean_object* x_14; lean_object* x_15; lean_object* x_148; lean_object* x_149; lean_object* x_395; lean_object* x_396; lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1174 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_1175 = l_Lake_Dependency_decodeToml___closed__10;
lean_inc(x_1);
x_1176 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1175, x_1);
x_1177 = lean_box(0);
if (lean_obj_tag(x_1176) == 0)
{
lean_object* x_1184; lean_object* x_1185; 
x_1184 = l_Lake_Dependency_decodeToml___closed__6;
lean_inc(x_1);
x_1185 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1184, x_1);
if (lean_obj_tag(x_1185) == 0)
{
lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; 
x_1186 = l_Lake_Dependency_decodeToml___closed__8;
lean_inc(x_1);
x_1187 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1186, x_1);
if (lean_obj_tag(x_1187) == 0)
{
x_14 = x_1177;
x_15 = x_13;
goto block_147;
}
else
{
uint8_t x_1194; 
x_1194 = !lean_is_exclusive(x_1187);
if (x_1194 == 0)
{
lean_object* x_1195; lean_object* x_1196; 
x_1195 = lean_ctor_get(x_1187, 0);
x_1196 = lean_ctor_get(x_1195, 1);
lean_inc(x_1196);
lean_dec(x_1195);
switch (lean_obj_tag(x_1196)) {
case 0:
{
uint8_t x_1197; 
lean_free_object(x_1187);
x_1197 = !lean_is_exclusive(x_1196);
if (x_1197 == 0)
{
lean_object* x_1198; lean_object* x_1199; 
x_1198 = lean_ctor_get(x_1196, 1);
lean_dec(x_1198);
x_1199 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_1196, 1, x_1199);
x_1188 = x_1196;
goto block_1193;
}
else
{
lean_object* x_1200; lean_object* x_1201; lean_object* x_1202; 
x_1200 = lean_ctor_get(x_1196, 0);
lean_inc(x_1200);
lean_dec(x_1196);
x_1201 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1202, 0, x_1200);
lean_ctor_set(x_1202, 1, x_1201);
x_1188 = x_1202;
goto block_1193;
}
}
case 2:
{
lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; 
lean_free_object(x_1187);
x_1203 = lean_ctor_get(x_1196, 0);
lean_inc(x_1203);
lean_dec(x_1196);
x_1204 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1205, 0, x_1203);
lean_ctor_set(x_1205, 1, x_1204);
x_1188 = x_1205;
goto block_1193;
}
case 3:
{
lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
lean_free_object(x_1187);
x_1206 = lean_ctor_get(x_1196, 0);
lean_inc(x_1206);
lean_dec(x_1196);
x_1207 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1208, 0, x_1206);
lean_ctor_set(x_1208, 1, x_1207);
x_1188 = x_1208;
goto block_1193;
}
case 6:
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1209 = lean_ctor_get(x_1196, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1196, 1);
lean_inc(x_1210);
lean_dec(x_1196);
x_1211 = l_Lake_DependencySrc_decodeToml(x_1210, x_1209);
if (lean_obj_tag(x_1211) == 0)
{
lean_object* x_1212; lean_object* x_1213; 
lean_free_object(x_1187);
x_1212 = lean_ctor_get(x_1211, 0);
lean_inc(x_1212);
lean_dec(x_1211);
x_1213 = l_Array_append___rarg(x_13, x_1212);
lean_dec(x_1212);
x_14 = x_1177;
x_15 = x_1213;
goto block_147;
}
else
{
lean_object* x_1214; 
x_1214 = lean_ctor_get(x_1211, 0);
lean_inc(x_1214);
lean_dec(x_1211);
lean_ctor_set(x_1187, 0, x_1214);
x_14 = x_1187;
x_15 = x_13;
goto block_147;
}
}
default: 
{
uint8_t x_1215; 
lean_free_object(x_1187);
x_1215 = !lean_is_exclusive(x_1196);
if (x_1215 == 0)
{
lean_object* x_1216; lean_object* x_1217; 
x_1216 = lean_ctor_get(x_1196, 1);
lean_dec(x_1216);
x_1217 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_1196, 0);
lean_ctor_set(x_1196, 1, x_1217);
x_1188 = x_1196;
goto block_1193;
}
else
{
lean_object* x_1218; lean_object* x_1219; lean_object* x_1220; 
x_1218 = lean_ctor_get(x_1196, 0);
lean_inc(x_1218);
lean_dec(x_1196);
x_1219 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1220, 0, x_1218);
lean_ctor_set(x_1220, 1, x_1219);
x_1188 = x_1220;
goto block_1193;
}
}
}
}
else
{
lean_object* x_1221; lean_object* x_1222; 
x_1221 = lean_ctor_get(x_1187, 0);
lean_inc(x_1221);
lean_dec(x_1187);
x_1222 = lean_ctor_get(x_1221, 1);
lean_inc(x_1222);
lean_dec(x_1221);
switch (lean_obj_tag(x_1222)) {
case 0:
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
x_1223 = lean_ctor_get(x_1222, 0);
lean_inc(x_1223);
if (lean_is_exclusive(x_1222)) {
 lean_ctor_release(x_1222, 0);
 lean_ctor_release(x_1222, 1);
 x_1224 = x_1222;
} else {
 lean_dec_ref(x_1222);
 x_1224 = lean_box(0);
}
x_1225 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
if (lean_is_scalar(x_1224)) {
 x_1226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1226 = x_1224;
}
lean_ctor_set(x_1226, 0, x_1223);
lean_ctor_set(x_1226, 1, x_1225);
x_1188 = x_1226;
goto block_1193;
}
case 2:
{
lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; 
x_1227 = lean_ctor_get(x_1222, 0);
lean_inc(x_1227);
lean_dec(x_1222);
x_1228 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1229, 0, x_1227);
lean_ctor_set(x_1229, 1, x_1228);
x_1188 = x_1229;
goto block_1193;
}
case 3:
{
lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; 
x_1230 = lean_ctor_get(x_1222, 0);
lean_inc(x_1230);
lean_dec(x_1222);
x_1231 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1232, 0, x_1230);
lean_ctor_set(x_1232, 1, x_1231);
x_1188 = x_1232;
goto block_1193;
}
case 6:
{
lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
x_1233 = lean_ctor_get(x_1222, 0);
lean_inc(x_1233);
x_1234 = lean_ctor_get(x_1222, 1);
lean_inc(x_1234);
lean_dec(x_1222);
x_1235 = l_Lake_DependencySrc_decodeToml(x_1234, x_1233);
if (lean_obj_tag(x_1235) == 0)
{
lean_object* x_1236; lean_object* x_1237; 
x_1236 = lean_ctor_get(x_1235, 0);
lean_inc(x_1236);
lean_dec(x_1235);
x_1237 = l_Array_append___rarg(x_13, x_1236);
lean_dec(x_1236);
x_14 = x_1177;
x_15 = x_1237;
goto block_147;
}
else
{
lean_object* x_1238; lean_object* x_1239; 
x_1238 = lean_ctor_get(x_1235, 0);
lean_inc(x_1238);
lean_dec(x_1235);
x_1239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1239, 0, x_1238);
x_14 = x_1239;
x_15 = x_13;
goto block_147;
}
}
default: 
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; 
x_1240 = lean_ctor_get(x_1222, 0);
lean_inc(x_1240);
if (lean_is_exclusive(x_1222)) {
 lean_ctor_release(x_1222, 0);
 lean_ctor_release(x_1222, 1);
 x_1241 = x_1222;
} else {
 lean_dec_ref(x_1222);
 x_1241 = lean_box(0);
}
x_1242 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
if (lean_is_scalar(x_1241)) {
 x_1243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1243 = x_1241;
 lean_ctor_set_tag(x_1243, 0);
}
lean_ctor_set(x_1243, 0, x_1240);
lean_ctor_set(x_1243, 1, x_1242);
x_1188 = x_1243;
goto block_1193;
}
}
}
}
block_1193:
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1189 = lean_box(0);
x_1190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1190, 0, x_1188);
lean_ctor_set(x_1190, 1, x_1189);
x_1191 = lean_array_mk(x_1190);
x_1192 = l_Array_append___rarg(x_13, x_1191);
lean_dec(x_1191);
x_14 = x_1177;
x_15 = x_1192;
goto block_147;
}
}
else
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1244 = lean_ctor_get(x_1185, 0);
lean_inc(x_1244);
if (lean_is_exclusive(x_1185)) {
 lean_ctor_release(x_1185, 0);
 x_1245 = x_1185;
} else {
 lean_dec_ref(x_1185);
 x_1245 = lean_box(0);
}
x_1246 = lean_ctor_get(x_1244, 1);
lean_inc(x_1246);
lean_dec(x_1244);
switch (lean_obj_tag(x_1246)) {
case 0:
{
lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1247 = lean_ctor_get(x_1246, 1);
lean_inc(x_1247);
if (lean_is_exclusive(x_1246)) {
 lean_ctor_release(x_1246, 0);
 lean_ctor_release(x_1246, 1);
 x_1248 = x_1246;
} else {
 lean_dec_ref(x_1246);
 x_1248 = lean_box(0);
}
x_1249 = l_Lake_DependencySrc_decodeToml___closed__2;
lean_inc(x_1);
x_1250 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1249, x_1);
if (lean_obj_tag(x_1250) == 0)
{
lean_object* x_1259; lean_object* x_1260; 
lean_dec(x_1248);
lean_dec(x_1245);
lean_inc(x_12);
x_1259 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1259, 0, x_1247);
lean_ctor_set(x_1259, 1, x_12);
lean_ctor_set(x_1259, 2, x_1177);
x_1260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1260, 0, x_1259);
x_14 = x_1260;
x_15 = x_13;
goto block_147;
}
else
{
uint8_t x_1261; 
x_1261 = !lean_is_exclusive(x_1250);
if (x_1261 == 0)
{
lean_object* x_1262; lean_object* x_1263; 
x_1262 = lean_ctor_get(x_1250, 0);
x_1263 = lean_ctor_get(x_1262, 1);
lean_inc(x_1263);
lean_dec(x_1262);
switch (lean_obj_tag(x_1263)) {
case 0:
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; 
lean_dec(x_1248);
lean_dec(x_1245);
x_1264 = lean_ctor_get(x_1263, 1);
lean_inc(x_1264);
lean_dec(x_1263);
lean_ctor_set(x_1250, 0, x_1264);
lean_inc(x_12);
x_1265 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1265, 0, x_1247);
lean_ctor_set(x_1265, 1, x_12);
lean_ctor_set(x_1265, 2, x_1250);
x_1266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1266, 0, x_1265);
x_14 = x_1266;
x_15 = x_13;
goto block_147;
}
case 2:
{
lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
lean_free_object(x_1250);
x_1267 = lean_ctor_get(x_1263, 0);
lean_inc(x_1267);
lean_dec(x_1263);
x_1268 = l_Lake_Glob_decodeToml___closed__2;
x_1269 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1269, 0, x_1267);
lean_ctor_set(x_1269, 1, x_1268);
x_1251 = x_1269;
goto block_1258;
}
case 3:
{
lean_object* x_1270; lean_object* x_1271; lean_object* x_1272; 
lean_free_object(x_1250);
x_1270 = lean_ctor_get(x_1263, 0);
lean_inc(x_1270);
lean_dec(x_1263);
x_1271 = l_Lake_Glob_decodeToml___closed__2;
x_1272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1272, 0, x_1270);
lean_ctor_set(x_1272, 1, x_1271);
x_1251 = x_1272;
goto block_1258;
}
default: 
{
uint8_t x_1273; 
lean_free_object(x_1250);
x_1273 = !lean_is_exclusive(x_1263);
if (x_1273 == 0)
{
lean_object* x_1274; lean_object* x_1275; 
x_1274 = lean_ctor_get(x_1263, 1);
lean_dec(x_1274);
x_1275 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1263, 0);
lean_ctor_set(x_1263, 1, x_1275);
x_1251 = x_1263;
goto block_1258;
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; 
x_1276 = lean_ctor_get(x_1263, 0);
lean_inc(x_1276);
lean_dec(x_1263);
x_1277 = l_Lake_Glob_decodeToml___closed__2;
x_1278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1278, 0, x_1276);
lean_ctor_set(x_1278, 1, x_1277);
x_1251 = x_1278;
goto block_1258;
}
}
}
}
else
{
lean_object* x_1279; lean_object* x_1280; 
x_1279 = lean_ctor_get(x_1250, 0);
lean_inc(x_1279);
lean_dec(x_1250);
x_1280 = lean_ctor_get(x_1279, 1);
lean_inc(x_1280);
lean_dec(x_1279);
switch (lean_obj_tag(x_1280)) {
case 0:
{
lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; 
lean_dec(x_1248);
lean_dec(x_1245);
x_1281 = lean_ctor_get(x_1280, 1);
lean_inc(x_1281);
lean_dec(x_1280);
x_1282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1282, 0, x_1281);
lean_inc(x_12);
x_1283 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1283, 0, x_1247);
lean_ctor_set(x_1283, 1, x_12);
lean_ctor_set(x_1283, 2, x_1282);
x_1284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1284, 0, x_1283);
x_14 = x_1284;
x_15 = x_13;
goto block_147;
}
case 2:
{
lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; 
x_1285 = lean_ctor_get(x_1280, 0);
lean_inc(x_1285);
lean_dec(x_1280);
x_1286 = l_Lake_Glob_decodeToml___closed__2;
x_1287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1287, 0, x_1285);
lean_ctor_set(x_1287, 1, x_1286);
x_1251 = x_1287;
goto block_1258;
}
case 3:
{
lean_object* x_1288; lean_object* x_1289; lean_object* x_1290; 
x_1288 = lean_ctor_get(x_1280, 0);
lean_inc(x_1288);
lean_dec(x_1280);
x_1289 = l_Lake_Glob_decodeToml___closed__2;
x_1290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1290, 0, x_1288);
lean_ctor_set(x_1290, 1, x_1289);
x_1251 = x_1290;
goto block_1258;
}
default: 
{
lean_object* x_1291; lean_object* x_1292; lean_object* x_1293; lean_object* x_1294; 
x_1291 = lean_ctor_get(x_1280, 0);
lean_inc(x_1291);
if (lean_is_exclusive(x_1280)) {
 lean_ctor_release(x_1280, 0);
 lean_ctor_release(x_1280, 1);
 x_1292 = x_1280;
} else {
 lean_dec_ref(x_1280);
 x_1292 = lean_box(0);
}
x_1293 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_1292)) {
 x_1294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1294 = x_1292;
 lean_ctor_set_tag(x_1294, 0);
}
lean_ctor_set(x_1294, 0, x_1291);
lean_ctor_set(x_1294, 1, x_1293);
x_1251 = x_1294;
goto block_1258;
}
}
}
}
block_1258:
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; lean_object* x_1256; lean_object* x_1257; 
x_1252 = lean_box(0);
if (lean_is_scalar(x_1248)) {
 x_1253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1253 = x_1248;
 lean_ctor_set_tag(x_1253, 1);
}
lean_ctor_set(x_1253, 0, x_1251);
lean_ctor_set(x_1253, 1, x_1252);
x_1254 = lean_array_mk(x_1253);
x_1255 = l_Array_append___rarg(x_13, x_1254);
lean_dec(x_1254);
lean_inc(x_12);
x_1256 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1256, 0, x_1247);
lean_ctor_set(x_1256, 1, x_12);
lean_ctor_set(x_1256, 2, x_1177);
if (lean_is_scalar(x_1245)) {
 x_1257 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1257 = x_1245;
}
lean_ctor_set(x_1257, 0, x_1256);
x_14 = x_1257;
x_15 = x_1255;
goto block_147;
}
}
case 2:
{
lean_object* x_1295; lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; 
lean_dec(x_1245);
x_1295 = lean_ctor_get(x_1246, 0);
lean_inc(x_1295);
lean_dec(x_1246);
x_1296 = l_Lake_Dependency_decodeToml___closed__9;
x_1297 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1297, 0, x_1295);
lean_ctor_set(x_1297, 1, x_1296);
x_1298 = lean_array_push(x_13, x_1297);
x_148 = x_1177;
x_149 = x_1298;
goto block_394;
}
case 3:
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; lean_object* x_1302; 
lean_dec(x_1245);
x_1299 = lean_ctor_get(x_1246, 0);
lean_inc(x_1299);
lean_dec(x_1246);
x_1300 = l_Lake_Dependency_decodeToml___closed__9;
x_1301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1301, 0, x_1299);
lean_ctor_set(x_1301, 1, x_1300);
x_1302 = lean_array_push(x_13, x_1301);
x_148 = x_1177;
x_149 = x_1302;
goto block_394;
}
case 6:
{
lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; lean_object* x_1307; lean_object* x_1556; lean_object* x_1557; 
x_1303 = lean_ctor_get(x_1246, 0);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_1246, 1);
lean_inc(x_1304);
if (lean_is_exclusive(x_1246)) {
 lean_ctor_release(x_1246, 0);
 lean_ctor_release(x_1246, 1);
 x_1305 = x_1246;
} else {
 lean_dec_ref(x_1246);
 x_1305 = lean_box(0);
}
x_1556 = l_Lake_DependencySrc_decodeToml___closed__18;
lean_inc(x_1304);
x_1557 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_1304, x_1556, x_1303);
if (lean_obj_tag(x_1557) == 0)
{
lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; 
x_1558 = lean_ctor_get(x_1557, 0);
lean_inc(x_1558);
lean_dec(x_1557);
x_1559 = l_Array_append___rarg(x_13, x_1558);
lean_dec(x_1558);
x_1560 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1306 = x_1560;
x_1307 = x_1559;
goto block_1555;
}
else
{
lean_object* x_1561; 
x_1561 = lean_ctor_get(x_1557, 0);
lean_inc(x_1561);
lean_dec(x_1557);
x_1306 = x_1561;
x_1307 = x_13;
goto block_1555;
}
block_1555:
{
lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; 
x_1308 = l_Lake_DependencySrc_decodeToml___closed__2;
x_1309 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1308, x_1304);
if (lean_obj_tag(x_1309) == 0)
{
lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1408; lean_object* x_1415; lean_object* x_1416; 
lean_dec(x_1305);
lean_dec(x_1245);
x_1318 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1318, 0, x_1306);
lean_ctor_set(x_1318, 1, x_12);
lean_ctor_set(x_1318, 2, x_1177);
x_1319 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1319, 0, x_1318);
x_1415 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_1416 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1415, x_1);
if (lean_obj_tag(x_1416) == 0)
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1462; lean_object* x_1463; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; 
x_1468 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_1469 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1468, x_1);
if (lean_obj_tag(x_1469) == 0)
{
x_1417 = x_1177;
x_1418 = x_1307;
goto block_1461;
}
else
{
uint8_t x_1476; 
x_1476 = !lean_is_exclusive(x_1469);
if (x_1476 == 0)
{
lean_object* x_1477; lean_object* x_1478; 
x_1477 = lean_ctor_get(x_1469, 0);
x_1478 = lean_ctor_get(x_1477, 1);
lean_inc(x_1478);
lean_dec(x_1477);
switch (lean_obj_tag(x_1478)) {
case 0:
{
lean_object* x_1479; 
x_1479 = lean_ctor_get(x_1478, 1);
lean_inc(x_1479);
lean_dec(x_1478);
lean_ctor_set(x_1469, 0, x_1479);
x_1462 = x_1469;
x_1463 = x_1307;
goto block_1467;
}
case 2:
{
lean_object* x_1480; lean_object* x_1481; lean_object* x_1482; 
lean_free_object(x_1469);
x_1480 = lean_ctor_get(x_1478, 0);
lean_inc(x_1480);
lean_dec(x_1478);
x_1481 = l_Lake_Glob_decodeToml___closed__2;
x_1482 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1482, 0, x_1480);
lean_ctor_set(x_1482, 1, x_1481);
x_1470 = x_1482;
goto block_1475;
}
case 3:
{
lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; 
lean_free_object(x_1469);
x_1483 = lean_ctor_get(x_1478, 0);
lean_inc(x_1483);
lean_dec(x_1478);
x_1484 = l_Lake_Glob_decodeToml___closed__2;
x_1485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1485, 0, x_1483);
lean_ctor_set(x_1485, 1, x_1484);
x_1470 = x_1485;
goto block_1475;
}
default: 
{
uint8_t x_1486; 
lean_free_object(x_1469);
x_1486 = !lean_is_exclusive(x_1478);
if (x_1486 == 0)
{
lean_object* x_1487; lean_object* x_1488; 
x_1487 = lean_ctor_get(x_1478, 1);
lean_dec(x_1487);
x_1488 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1478, 0);
lean_ctor_set(x_1478, 1, x_1488);
x_1470 = x_1478;
goto block_1475;
}
else
{
lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; 
x_1489 = lean_ctor_get(x_1478, 0);
lean_inc(x_1489);
lean_dec(x_1478);
x_1490 = l_Lake_Glob_decodeToml___closed__2;
x_1491 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1491, 0, x_1489);
lean_ctor_set(x_1491, 1, x_1490);
x_1470 = x_1491;
goto block_1475;
}
}
}
}
else
{
lean_object* x_1492; lean_object* x_1493; 
x_1492 = lean_ctor_get(x_1469, 0);
lean_inc(x_1492);
lean_dec(x_1469);
x_1493 = lean_ctor_get(x_1492, 1);
lean_inc(x_1493);
lean_dec(x_1492);
switch (lean_obj_tag(x_1493)) {
case 0:
{
lean_object* x_1494; lean_object* x_1495; 
x_1494 = lean_ctor_get(x_1493, 1);
lean_inc(x_1494);
lean_dec(x_1493);
x_1495 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1495, 0, x_1494);
x_1462 = x_1495;
x_1463 = x_1307;
goto block_1467;
}
case 2:
{
lean_object* x_1496; lean_object* x_1497; lean_object* x_1498; 
x_1496 = lean_ctor_get(x_1493, 0);
lean_inc(x_1496);
lean_dec(x_1493);
x_1497 = l_Lake_Glob_decodeToml___closed__2;
x_1498 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1498, 0, x_1496);
lean_ctor_set(x_1498, 1, x_1497);
x_1470 = x_1498;
goto block_1475;
}
case 3:
{
lean_object* x_1499; lean_object* x_1500; lean_object* x_1501; 
x_1499 = lean_ctor_get(x_1493, 0);
lean_inc(x_1499);
lean_dec(x_1493);
x_1500 = l_Lake_Glob_decodeToml___closed__2;
x_1501 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1501, 0, x_1499);
lean_ctor_set(x_1501, 1, x_1500);
x_1470 = x_1501;
goto block_1475;
}
default: 
{
lean_object* x_1502; lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; 
x_1502 = lean_ctor_get(x_1493, 0);
lean_inc(x_1502);
if (lean_is_exclusive(x_1493)) {
 lean_ctor_release(x_1493, 0);
 lean_ctor_release(x_1493, 1);
 x_1503 = x_1493;
} else {
 lean_dec_ref(x_1493);
 x_1503 = lean_box(0);
}
x_1504 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_1503)) {
 x_1505 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1505 = x_1503;
 lean_ctor_set_tag(x_1505, 0);
}
lean_ctor_set(x_1505, 0, x_1502);
lean_ctor_set(x_1505, 1, x_1504);
x_1470 = x_1505;
goto block_1475;
}
}
}
}
block_1461:
{
lean_object* x_1419; lean_object* x_1420; lean_object* x_1428; lean_object* x_1429; 
x_1419 = lean_box(0);
x_1428 = l_Lake_Dependency_decodeToml___closed__2;
x_1429 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1428, x_1);
if (lean_obj_tag(x_1429) == 0)
{
lean_object* x_1430; lean_object* x_1431; 
x_1430 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1431 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1431, 0, x_11);
lean_ctor_set(x_1431, 1, x_1430);
lean_ctor_set(x_1431, 2, x_1417);
lean_ctor_set(x_1431, 3, x_1319);
lean_ctor_set(x_1431, 4, x_1419);
x_3 = x_1431;
x_4 = x_1418;
goto block_8;
}
else
{
lean_object* x_1432; lean_object* x_1433; 
x_1432 = lean_ctor_get(x_1429, 0);
lean_inc(x_1432);
lean_dec(x_1429);
x_1433 = lean_ctor_get(x_1432, 1);
lean_inc(x_1433);
lean_dec(x_1432);
switch (lean_obj_tag(x_1433)) {
case 0:
{
uint8_t x_1434; 
x_1434 = !lean_is_exclusive(x_1433);
if (x_1434 == 0)
{
lean_object* x_1435; lean_object* x_1436; 
x_1435 = lean_ctor_get(x_1433, 1);
lean_dec(x_1435);
x_1436 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_1433, 1, x_1436);
x_1420 = x_1433;
goto block_1427;
}
else
{
lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; 
x_1437 = lean_ctor_get(x_1433, 0);
lean_inc(x_1437);
lean_dec(x_1433);
x_1438 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1439, 0, x_1437);
lean_ctor_set(x_1439, 1, x_1438);
x_1420 = x_1439;
goto block_1427;
}
}
case 2:
{
lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
x_1440 = lean_ctor_get(x_1433, 0);
lean_inc(x_1440);
lean_dec(x_1433);
x_1441 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1442, 0, x_1440);
lean_ctor_set(x_1442, 1, x_1441);
x_1420 = x_1442;
goto block_1427;
}
case 3:
{
lean_object* x_1443; lean_object* x_1444; lean_object* x_1445; 
x_1443 = lean_ctor_get(x_1433, 0);
lean_inc(x_1443);
lean_dec(x_1433);
x_1444 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1445, 0, x_1443);
lean_ctor_set(x_1445, 1, x_1444);
x_1420 = x_1445;
goto block_1427;
}
case 6:
{
lean_object* x_1446; lean_object* x_1447; 
x_1446 = lean_ctor_get(x_1433, 1);
lean_inc(x_1446);
lean_dec(x_1433);
x_1447 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_1446);
lean_dec(x_1446);
if (lean_obj_tag(x_1447) == 0)
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; 
x_1448 = lean_ctor_get(x_1447, 0);
lean_inc(x_1448);
lean_dec(x_1447);
x_1449 = l_Array_append___rarg(x_1418, x_1448);
lean_dec(x_1448);
x_1450 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1451 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1451, 0, x_11);
lean_ctor_set(x_1451, 1, x_1450);
lean_ctor_set(x_1451, 2, x_1417);
lean_ctor_set(x_1451, 3, x_1319);
lean_ctor_set(x_1451, 4, x_1419);
x_3 = x_1451;
x_4 = x_1449;
goto block_8;
}
else
{
lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; 
x_1452 = lean_ctor_get(x_1447, 0);
lean_inc(x_1452);
lean_dec(x_1447);
x_1453 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1454 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1454, 0, x_11);
lean_ctor_set(x_1454, 1, x_1453);
lean_ctor_set(x_1454, 2, x_1417);
lean_ctor_set(x_1454, 3, x_1319);
lean_ctor_set(x_1454, 4, x_1452);
x_3 = x_1454;
x_4 = x_1418;
goto block_8;
}
}
default: 
{
uint8_t x_1455; 
x_1455 = !lean_is_exclusive(x_1433);
if (x_1455 == 0)
{
lean_object* x_1456; lean_object* x_1457; 
x_1456 = lean_ctor_get(x_1433, 1);
lean_dec(x_1456);
x_1457 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_1433, 0);
lean_ctor_set(x_1433, 1, x_1457);
x_1420 = x_1433;
goto block_1427;
}
else
{
lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
x_1458 = lean_ctor_get(x_1433, 0);
lean_inc(x_1458);
lean_dec(x_1433);
x_1459 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1460, 0, x_1458);
lean_ctor_set(x_1460, 1, x_1459);
x_1420 = x_1460;
goto block_1427;
}
}
}
}
block_1427:
{
lean_object* x_1421; lean_object* x_1422; lean_object* x_1423; lean_object* x_1424; lean_object* x_1425; lean_object* x_1426; 
x_1421 = lean_box(0);
x_1422 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1422, 0, x_1420);
lean_ctor_set(x_1422, 1, x_1421);
x_1423 = lean_array_mk(x_1422);
x_1424 = l_Array_append___rarg(x_1418, x_1423);
lean_dec(x_1423);
x_1425 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1426 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1426, 0, x_11);
lean_ctor_set(x_1426, 1, x_1425);
lean_ctor_set(x_1426, 2, x_1417);
lean_ctor_set(x_1426, 3, x_1319);
lean_ctor_set(x_1426, 4, x_1419);
x_3 = x_1426;
x_4 = x_1424;
goto block_8;
}
}
block_1467:
{
if (lean_obj_tag(x_1462) == 0)
{
x_1417 = x_1177;
x_1418 = x_1463;
goto block_1461;
}
else
{
uint8_t x_1464; 
x_1464 = !lean_is_exclusive(x_1462);
if (x_1464 == 0)
{
x_1417 = x_1462;
x_1418 = x_1463;
goto block_1461;
}
else
{
lean_object* x_1465; lean_object* x_1466; 
x_1465 = lean_ctor_get(x_1462, 0);
lean_inc(x_1465);
lean_dec(x_1462);
x_1466 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1466, 0, x_1465);
x_1417 = x_1466;
x_1418 = x_1463;
goto block_1461;
}
}
}
block_1475:
{
lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; 
x_1471 = lean_box(0);
x_1472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1472, 0, x_1470);
lean_ctor_set(x_1472, 1, x_1471);
x_1473 = lean_array_mk(x_1472);
x_1474 = l_Array_append___rarg(x_1307, x_1473);
lean_dec(x_1473);
x_1462 = x_1177;
x_1463 = x_1474;
goto block_1467;
}
}
else
{
lean_object* x_1506; lean_object* x_1507; 
x_1506 = lean_ctor_get(x_1416, 0);
lean_inc(x_1506);
lean_dec(x_1416);
x_1507 = lean_ctor_get(x_1506, 1);
lean_inc(x_1507);
lean_dec(x_1506);
switch (lean_obj_tag(x_1507)) {
case 0:
{
lean_object* x_1508; 
x_1508 = lean_ctor_get(x_1507, 1);
lean_inc(x_1508);
lean_dec(x_1507);
x_1320 = x_1508;
x_1321 = x_1307;
goto block_1407;
}
case 2:
{
lean_object* x_1509; lean_object* x_1510; lean_object* x_1511; 
x_1509 = lean_ctor_get(x_1507, 0);
lean_inc(x_1509);
lean_dec(x_1507);
x_1510 = l_Lake_Glob_decodeToml___closed__2;
x_1511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1511, 0, x_1509);
lean_ctor_set(x_1511, 1, x_1510);
x_1408 = x_1511;
goto block_1414;
}
case 3:
{
lean_object* x_1512; lean_object* x_1513; lean_object* x_1514; 
x_1512 = lean_ctor_get(x_1507, 0);
lean_inc(x_1512);
lean_dec(x_1507);
x_1513 = l_Lake_Glob_decodeToml___closed__2;
x_1514 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1514, 0, x_1512);
lean_ctor_set(x_1514, 1, x_1513);
x_1408 = x_1514;
goto block_1414;
}
default: 
{
uint8_t x_1515; 
x_1515 = !lean_is_exclusive(x_1507);
if (x_1515 == 0)
{
lean_object* x_1516; lean_object* x_1517; 
x_1516 = lean_ctor_get(x_1507, 1);
lean_dec(x_1516);
x_1517 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1507, 0);
lean_ctor_set(x_1507, 1, x_1517);
x_1408 = x_1507;
goto block_1414;
}
else
{
lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; 
x_1518 = lean_ctor_get(x_1507, 0);
lean_inc(x_1518);
lean_dec(x_1507);
x_1519 = l_Lake_Glob_decodeToml___closed__2;
x_1520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1520, 0, x_1518);
lean_ctor_set(x_1520, 1, x_1519);
x_1408 = x_1520;
goto block_1414;
}
}
}
}
block_1407:
{
lean_object* x_1322; lean_object* x_1323; lean_object* x_1363; lean_object* x_1364; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
x_1369 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_1370 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1369, x_1);
if (lean_obj_tag(x_1370) == 0)
{
x_1363 = x_1177;
x_1364 = x_1321;
goto block_1368;
}
else
{
uint8_t x_1377; 
x_1377 = !lean_is_exclusive(x_1370);
if (x_1377 == 0)
{
lean_object* x_1378; lean_object* x_1379; 
x_1378 = lean_ctor_get(x_1370, 0);
x_1379 = lean_ctor_get(x_1378, 1);
lean_inc(x_1379);
lean_dec(x_1378);
switch (lean_obj_tag(x_1379)) {
case 0:
{
lean_object* x_1380; 
x_1380 = lean_ctor_get(x_1379, 1);
lean_inc(x_1380);
lean_dec(x_1379);
lean_ctor_set(x_1370, 0, x_1380);
x_1363 = x_1370;
x_1364 = x_1321;
goto block_1368;
}
case 2:
{
lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; 
lean_free_object(x_1370);
x_1381 = lean_ctor_get(x_1379, 0);
lean_inc(x_1381);
lean_dec(x_1379);
x_1382 = l_Lake_Glob_decodeToml___closed__2;
x_1383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1383, 0, x_1381);
lean_ctor_set(x_1383, 1, x_1382);
x_1371 = x_1383;
goto block_1376;
}
case 3:
{
lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; 
lean_free_object(x_1370);
x_1384 = lean_ctor_get(x_1379, 0);
lean_inc(x_1384);
lean_dec(x_1379);
x_1385 = l_Lake_Glob_decodeToml___closed__2;
x_1386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1386, 0, x_1384);
lean_ctor_set(x_1386, 1, x_1385);
x_1371 = x_1386;
goto block_1376;
}
default: 
{
uint8_t x_1387; 
lean_free_object(x_1370);
x_1387 = !lean_is_exclusive(x_1379);
if (x_1387 == 0)
{
lean_object* x_1388; lean_object* x_1389; 
x_1388 = lean_ctor_get(x_1379, 1);
lean_dec(x_1388);
x_1389 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1379, 0);
lean_ctor_set(x_1379, 1, x_1389);
x_1371 = x_1379;
goto block_1376;
}
else
{
lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; 
x_1390 = lean_ctor_get(x_1379, 0);
lean_inc(x_1390);
lean_dec(x_1379);
x_1391 = l_Lake_Glob_decodeToml___closed__2;
x_1392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1392, 0, x_1390);
lean_ctor_set(x_1392, 1, x_1391);
x_1371 = x_1392;
goto block_1376;
}
}
}
}
else
{
lean_object* x_1393; lean_object* x_1394; 
x_1393 = lean_ctor_get(x_1370, 0);
lean_inc(x_1393);
lean_dec(x_1370);
x_1394 = lean_ctor_get(x_1393, 1);
lean_inc(x_1394);
lean_dec(x_1393);
switch (lean_obj_tag(x_1394)) {
case 0:
{
lean_object* x_1395; lean_object* x_1396; 
x_1395 = lean_ctor_get(x_1394, 1);
lean_inc(x_1395);
lean_dec(x_1394);
x_1396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1396, 0, x_1395);
x_1363 = x_1396;
x_1364 = x_1321;
goto block_1368;
}
case 2:
{
lean_object* x_1397; lean_object* x_1398; lean_object* x_1399; 
x_1397 = lean_ctor_get(x_1394, 0);
lean_inc(x_1397);
lean_dec(x_1394);
x_1398 = l_Lake_Glob_decodeToml___closed__2;
x_1399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1399, 0, x_1397);
lean_ctor_set(x_1399, 1, x_1398);
x_1371 = x_1399;
goto block_1376;
}
case 3:
{
lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; 
x_1400 = lean_ctor_get(x_1394, 0);
lean_inc(x_1400);
lean_dec(x_1394);
x_1401 = l_Lake_Glob_decodeToml___closed__2;
x_1402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1402, 0, x_1400);
lean_ctor_set(x_1402, 1, x_1401);
x_1371 = x_1402;
goto block_1376;
}
default: 
{
lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; 
x_1403 = lean_ctor_get(x_1394, 0);
lean_inc(x_1403);
if (lean_is_exclusive(x_1394)) {
 lean_ctor_release(x_1394, 0);
 lean_ctor_release(x_1394, 1);
 x_1404 = x_1394;
} else {
 lean_dec_ref(x_1394);
 x_1404 = lean_box(0);
}
x_1405 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_1404)) {
 x_1406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1406 = x_1404;
 lean_ctor_set_tag(x_1406, 0);
}
lean_ctor_set(x_1406, 0, x_1403);
lean_ctor_set(x_1406, 1, x_1405);
x_1371 = x_1406;
goto block_1376;
}
}
}
}
block_1362:
{
lean_object* x_1324; lean_object* x_1325; lean_object* x_1332; lean_object* x_1333; 
x_1324 = lean_box(0);
x_1332 = l_Lake_Dependency_decodeToml___closed__2;
x_1333 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1174, x_1332, x_1);
if (lean_obj_tag(x_1333) == 0)
{
lean_object* x_1334; 
x_1334 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1334, 0, x_11);
lean_ctor_set(x_1334, 1, x_1320);
lean_ctor_set(x_1334, 2, x_1322);
lean_ctor_set(x_1334, 3, x_1319);
lean_ctor_set(x_1334, 4, x_1324);
x_3 = x_1334;
x_4 = x_1323;
goto block_8;
}
else
{
lean_object* x_1335; lean_object* x_1336; 
x_1335 = lean_ctor_get(x_1333, 0);
lean_inc(x_1335);
lean_dec(x_1333);
x_1336 = lean_ctor_get(x_1335, 1);
lean_inc(x_1336);
lean_dec(x_1335);
switch (lean_obj_tag(x_1336)) {
case 0:
{
uint8_t x_1337; 
x_1337 = !lean_is_exclusive(x_1336);
if (x_1337 == 0)
{
lean_object* x_1338; lean_object* x_1339; 
x_1338 = lean_ctor_get(x_1336, 1);
lean_dec(x_1338);
x_1339 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_1336, 1, x_1339);
x_1325 = x_1336;
goto block_1331;
}
else
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; 
x_1340 = lean_ctor_get(x_1336, 0);
lean_inc(x_1340);
lean_dec(x_1336);
x_1341 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1342, 0, x_1340);
lean_ctor_set(x_1342, 1, x_1341);
x_1325 = x_1342;
goto block_1331;
}
}
case 2:
{
lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; 
x_1343 = lean_ctor_get(x_1336, 0);
lean_inc(x_1343);
lean_dec(x_1336);
x_1344 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1345, 0, x_1343);
lean_ctor_set(x_1345, 1, x_1344);
x_1325 = x_1345;
goto block_1331;
}
case 3:
{
lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; 
x_1346 = lean_ctor_get(x_1336, 0);
lean_inc(x_1346);
lean_dec(x_1336);
x_1347 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1348, 0, x_1346);
lean_ctor_set(x_1348, 1, x_1347);
x_1325 = x_1348;
goto block_1331;
}
case 6:
{
lean_object* x_1349; lean_object* x_1350; 
x_1349 = lean_ctor_get(x_1336, 1);
lean_inc(x_1349);
lean_dec(x_1336);
x_1350 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_1349);
lean_dec(x_1349);
if (lean_obj_tag(x_1350) == 0)
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
x_1351 = lean_ctor_get(x_1350, 0);
lean_inc(x_1351);
lean_dec(x_1350);
x_1352 = l_Array_append___rarg(x_1323, x_1351);
lean_dec(x_1351);
x_1353 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1353, 0, x_11);
lean_ctor_set(x_1353, 1, x_1320);
lean_ctor_set(x_1353, 2, x_1322);
lean_ctor_set(x_1353, 3, x_1319);
lean_ctor_set(x_1353, 4, x_1324);
x_3 = x_1353;
x_4 = x_1352;
goto block_8;
}
else
{
lean_object* x_1354; lean_object* x_1355; 
x_1354 = lean_ctor_get(x_1350, 0);
lean_inc(x_1354);
lean_dec(x_1350);
x_1355 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1355, 0, x_11);
lean_ctor_set(x_1355, 1, x_1320);
lean_ctor_set(x_1355, 2, x_1322);
lean_ctor_set(x_1355, 3, x_1319);
lean_ctor_set(x_1355, 4, x_1354);
x_3 = x_1355;
x_4 = x_1323;
goto block_8;
}
}
default: 
{
uint8_t x_1356; 
x_1356 = !lean_is_exclusive(x_1336);
if (x_1356 == 0)
{
lean_object* x_1357; lean_object* x_1358; 
x_1357 = lean_ctor_get(x_1336, 1);
lean_dec(x_1357);
x_1358 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_1336, 0);
lean_ctor_set(x_1336, 1, x_1358);
x_1325 = x_1336;
goto block_1331;
}
else
{
lean_object* x_1359; lean_object* x_1360; lean_object* x_1361; 
x_1359 = lean_ctor_get(x_1336, 0);
lean_inc(x_1359);
lean_dec(x_1336);
x_1360 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1361, 0, x_1359);
lean_ctor_set(x_1361, 1, x_1360);
x_1325 = x_1361;
goto block_1331;
}
}
}
}
block_1331:
{
lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
x_1326 = lean_box(0);
x_1327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1327, 0, x_1325);
lean_ctor_set(x_1327, 1, x_1326);
x_1328 = lean_array_mk(x_1327);
x_1329 = l_Array_append___rarg(x_1323, x_1328);
lean_dec(x_1328);
x_1330 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1330, 0, x_11);
lean_ctor_set(x_1330, 1, x_1320);
lean_ctor_set(x_1330, 2, x_1322);
lean_ctor_set(x_1330, 3, x_1319);
lean_ctor_set(x_1330, 4, x_1324);
x_3 = x_1330;
x_4 = x_1329;
goto block_8;
}
}
block_1368:
{
if (lean_obj_tag(x_1363) == 0)
{
x_1322 = x_1177;
x_1323 = x_1364;
goto block_1362;
}
else
{
uint8_t x_1365; 
x_1365 = !lean_is_exclusive(x_1363);
if (x_1365 == 0)
{
x_1322 = x_1363;
x_1323 = x_1364;
goto block_1362;
}
else
{
lean_object* x_1366; lean_object* x_1367; 
x_1366 = lean_ctor_get(x_1363, 0);
lean_inc(x_1366);
lean_dec(x_1363);
x_1367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1367, 0, x_1366);
x_1322 = x_1367;
x_1323 = x_1364;
goto block_1362;
}
}
}
block_1376:
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1372 = lean_box(0);
x_1373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1373, 0, x_1371);
lean_ctor_set(x_1373, 1, x_1372);
x_1374 = lean_array_mk(x_1373);
x_1375 = l_Array_append___rarg(x_1321, x_1374);
lean_dec(x_1374);
x_1363 = x_1177;
x_1364 = x_1375;
goto block_1368;
}
}
block_1414:
{
lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; lean_object* x_1412; lean_object* x_1413; 
x_1409 = lean_box(0);
x_1410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1410, 0, x_1408);
lean_ctor_set(x_1410, 1, x_1409);
x_1411 = lean_array_mk(x_1410);
x_1412 = l_Array_append___rarg(x_1307, x_1411);
lean_dec(x_1411);
x_1413 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1320 = x_1413;
x_1321 = x_1412;
goto block_1407;
}
}
else
{
uint8_t x_1521; 
x_1521 = !lean_is_exclusive(x_1309);
if (x_1521 == 0)
{
lean_object* x_1522; lean_object* x_1523; 
x_1522 = lean_ctor_get(x_1309, 0);
x_1523 = lean_ctor_get(x_1522, 1);
lean_inc(x_1523);
lean_dec(x_1522);
switch (lean_obj_tag(x_1523)) {
case 0:
{
lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; 
lean_dec(x_1305);
lean_dec(x_1245);
x_1524 = lean_ctor_get(x_1523, 1);
lean_inc(x_1524);
lean_dec(x_1523);
lean_ctor_set(x_1309, 0, x_1524);
lean_inc(x_12);
x_1525 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1525, 0, x_1306);
lean_ctor_set(x_1525, 1, x_12);
lean_ctor_set(x_1525, 2, x_1309);
x_1526 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1526, 0, x_1525);
x_14 = x_1526;
x_15 = x_1307;
goto block_147;
}
case 2:
{
lean_object* x_1527; lean_object* x_1528; lean_object* x_1529; 
lean_free_object(x_1309);
x_1527 = lean_ctor_get(x_1523, 0);
lean_inc(x_1527);
lean_dec(x_1523);
x_1528 = l_Lake_Glob_decodeToml___closed__2;
x_1529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1529, 0, x_1527);
lean_ctor_set(x_1529, 1, x_1528);
x_1310 = x_1529;
goto block_1317;
}
case 3:
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; 
lean_free_object(x_1309);
x_1530 = lean_ctor_get(x_1523, 0);
lean_inc(x_1530);
lean_dec(x_1523);
x_1531 = l_Lake_Glob_decodeToml___closed__2;
x_1532 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1532, 0, x_1530);
lean_ctor_set(x_1532, 1, x_1531);
x_1310 = x_1532;
goto block_1317;
}
default: 
{
uint8_t x_1533; 
lean_free_object(x_1309);
x_1533 = !lean_is_exclusive(x_1523);
if (x_1533 == 0)
{
lean_object* x_1534; lean_object* x_1535; 
x_1534 = lean_ctor_get(x_1523, 1);
lean_dec(x_1534);
x_1535 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1523, 0);
lean_ctor_set(x_1523, 1, x_1535);
x_1310 = x_1523;
goto block_1317;
}
else
{
lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; 
x_1536 = lean_ctor_get(x_1523, 0);
lean_inc(x_1536);
lean_dec(x_1523);
x_1537 = l_Lake_Glob_decodeToml___closed__2;
x_1538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1538, 0, x_1536);
lean_ctor_set(x_1538, 1, x_1537);
x_1310 = x_1538;
goto block_1317;
}
}
}
}
else
{
lean_object* x_1539; lean_object* x_1540; 
x_1539 = lean_ctor_get(x_1309, 0);
lean_inc(x_1539);
lean_dec(x_1309);
x_1540 = lean_ctor_get(x_1539, 1);
lean_inc(x_1540);
lean_dec(x_1539);
switch (lean_obj_tag(x_1540)) {
case 0:
{
lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; lean_object* x_1544; 
lean_dec(x_1305);
lean_dec(x_1245);
x_1541 = lean_ctor_get(x_1540, 1);
lean_inc(x_1541);
lean_dec(x_1540);
x_1542 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1542, 0, x_1541);
lean_inc(x_12);
x_1543 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1543, 0, x_1306);
lean_ctor_set(x_1543, 1, x_12);
lean_ctor_set(x_1543, 2, x_1542);
x_1544 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1544, 0, x_1543);
x_14 = x_1544;
x_15 = x_1307;
goto block_147;
}
case 2:
{
lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; 
x_1545 = lean_ctor_get(x_1540, 0);
lean_inc(x_1545);
lean_dec(x_1540);
x_1546 = l_Lake_Glob_decodeToml___closed__2;
x_1547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1547, 0, x_1545);
lean_ctor_set(x_1547, 1, x_1546);
x_1310 = x_1547;
goto block_1317;
}
case 3:
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; 
x_1548 = lean_ctor_get(x_1540, 0);
lean_inc(x_1548);
lean_dec(x_1540);
x_1549 = l_Lake_Glob_decodeToml___closed__2;
x_1550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1550, 0, x_1548);
lean_ctor_set(x_1550, 1, x_1549);
x_1310 = x_1550;
goto block_1317;
}
default: 
{
lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; 
x_1551 = lean_ctor_get(x_1540, 0);
lean_inc(x_1551);
if (lean_is_exclusive(x_1540)) {
 lean_ctor_release(x_1540, 0);
 lean_ctor_release(x_1540, 1);
 x_1552 = x_1540;
} else {
 lean_dec_ref(x_1540);
 x_1552 = lean_box(0);
}
x_1553 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_1552)) {
 x_1554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1554 = x_1552;
 lean_ctor_set_tag(x_1554, 0);
}
lean_ctor_set(x_1554, 0, x_1551);
lean_ctor_set(x_1554, 1, x_1553);
x_1310 = x_1554;
goto block_1317;
}
}
}
}
block_1317:
{
lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
x_1311 = lean_box(0);
if (lean_is_scalar(x_1305)) {
 x_1312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1312 = x_1305;
 lean_ctor_set_tag(x_1312, 1);
}
lean_ctor_set(x_1312, 0, x_1310);
lean_ctor_set(x_1312, 1, x_1311);
x_1313 = lean_array_mk(x_1312);
x_1314 = l_Array_append___rarg(x_1307, x_1313);
lean_dec(x_1313);
lean_inc(x_12);
x_1315 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_1315, 0, x_1306);
lean_ctor_set(x_1315, 1, x_12);
lean_ctor_set(x_1315, 2, x_1177);
if (lean_is_scalar(x_1245)) {
 x_1316 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1316 = x_1245;
}
lean_ctor_set(x_1316, 0, x_1315);
x_14 = x_1316;
x_15 = x_1314;
goto block_147;
}
}
}
default: 
{
uint8_t x_1562; 
lean_dec(x_1245);
x_1562 = !lean_is_exclusive(x_1246);
if (x_1562 == 0)
{
lean_object* x_1563; lean_object* x_1564; lean_object* x_1565; 
x_1563 = lean_ctor_get(x_1246, 1);
lean_dec(x_1563);
x_1564 = l_Lake_Dependency_decodeToml___closed__9;
lean_ctor_set_tag(x_1246, 0);
lean_ctor_set(x_1246, 1, x_1564);
x_1565 = lean_array_push(x_13, x_1246);
x_148 = x_1177;
x_149 = x_1565;
goto block_394;
}
else
{
lean_object* x_1566; lean_object* x_1567; lean_object* x_1568; lean_object* x_1569; 
x_1566 = lean_ctor_get(x_1246, 0);
lean_inc(x_1566);
lean_dec(x_1246);
x_1567 = l_Lake_Dependency_decodeToml___closed__9;
x_1568 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1568, 0, x_1566);
lean_ctor_set(x_1568, 1, x_1567);
x_1569 = lean_array_push(x_13, x_1568);
x_148 = x_1177;
x_149 = x_1569;
goto block_394;
}
}
}
}
}
else
{
uint8_t x_1570; 
x_1570 = !lean_is_exclusive(x_1176);
if (x_1570 == 0)
{
lean_object* x_1571; lean_object* x_1572; 
x_1571 = lean_ctor_get(x_1176, 0);
x_1572 = lean_ctor_get(x_1571, 1);
lean_inc(x_1572);
lean_dec(x_1571);
switch (lean_obj_tag(x_1572)) {
case 0:
{
lean_object* x_1573; 
x_1573 = lean_ctor_get(x_1572, 1);
lean_inc(x_1573);
lean_dec(x_1572);
lean_ctor_set(x_1176, 0, x_1573);
x_395 = x_1176;
x_396 = x_13;
goto block_1173;
}
case 2:
{
lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; 
lean_free_object(x_1176);
x_1574 = lean_ctor_get(x_1572, 0);
lean_inc(x_1574);
lean_dec(x_1572);
x_1575 = l_Lake_Glob_decodeToml___closed__2;
x_1576 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1576, 0, x_1574);
lean_ctor_set(x_1576, 1, x_1575);
x_1178 = x_1576;
goto block_1183;
}
case 3:
{
lean_object* x_1577; lean_object* x_1578; lean_object* x_1579; 
lean_free_object(x_1176);
x_1577 = lean_ctor_get(x_1572, 0);
lean_inc(x_1577);
lean_dec(x_1572);
x_1578 = l_Lake_Glob_decodeToml___closed__2;
x_1579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1579, 0, x_1577);
lean_ctor_set(x_1579, 1, x_1578);
x_1178 = x_1579;
goto block_1183;
}
default: 
{
uint8_t x_1580; 
lean_free_object(x_1176);
x_1580 = !lean_is_exclusive(x_1572);
if (x_1580 == 0)
{
lean_object* x_1581; lean_object* x_1582; 
x_1581 = lean_ctor_get(x_1572, 1);
lean_dec(x_1581);
x_1582 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_1572, 0);
lean_ctor_set(x_1572, 1, x_1582);
x_1178 = x_1572;
goto block_1183;
}
else
{
lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; 
x_1583 = lean_ctor_get(x_1572, 0);
lean_inc(x_1583);
lean_dec(x_1572);
x_1584 = l_Lake_Glob_decodeToml___closed__2;
x_1585 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1585, 0, x_1583);
lean_ctor_set(x_1585, 1, x_1584);
x_1178 = x_1585;
goto block_1183;
}
}
}
}
else
{
lean_object* x_1586; lean_object* x_1587; 
x_1586 = lean_ctor_get(x_1176, 0);
lean_inc(x_1586);
lean_dec(x_1176);
x_1587 = lean_ctor_get(x_1586, 1);
lean_inc(x_1587);
lean_dec(x_1586);
switch (lean_obj_tag(x_1587)) {
case 0:
{
lean_object* x_1588; lean_object* x_1589; 
x_1588 = lean_ctor_get(x_1587, 1);
lean_inc(x_1588);
lean_dec(x_1587);
x_1589 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1589, 0, x_1588);
x_395 = x_1589;
x_396 = x_13;
goto block_1173;
}
case 2:
{
lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; 
x_1590 = lean_ctor_get(x_1587, 0);
lean_inc(x_1590);
lean_dec(x_1587);
x_1591 = l_Lake_Glob_decodeToml___closed__2;
x_1592 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1592, 0, x_1590);
lean_ctor_set(x_1592, 1, x_1591);
x_1178 = x_1592;
goto block_1183;
}
case 3:
{
lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; 
x_1593 = lean_ctor_get(x_1587, 0);
lean_inc(x_1593);
lean_dec(x_1587);
x_1594 = l_Lake_Glob_decodeToml___closed__2;
x_1595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1595, 0, x_1593);
lean_ctor_set(x_1595, 1, x_1594);
x_1178 = x_1595;
goto block_1183;
}
default: 
{
lean_object* x_1596; lean_object* x_1597; lean_object* x_1598; lean_object* x_1599; 
x_1596 = lean_ctor_get(x_1587, 0);
lean_inc(x_1596);
if (lean_is_exclusive(x_1587)) {
 lean_ctor_release(x_1587, 0);
 lean_ctor_release(x_1587, 1);
 x_1597 = x_1587;
} else {
 lean_dec_ref(x_1587);
 x_1597 = lean_box(0);
}
x_1598 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_1597)) {
 x_1599 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1599 = x_1597;
 lean_ctor_set_tag(x_1599, 0);
}
lean_ctor_set(x_1599, 0, x_1596);
lean_ctor_set(x_1599, 1, x_1598);
x_1178 = x_1599;
goto block_1183;
}
}
}
}
block_147:
{
lean_object* x_16; lean_object* x_17; lean_object* x_121; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_129 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_130 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_128, x_129, x_1);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_16 = x_131;
x_17 = x_15;
goto block_120;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec(x_132);
switch (lean_obj_tag(x_133)) {
case 0:
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
x_16 = x_134;
x_17 = x_15;
goto block_120;
}
case 2:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_133, 0);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lake_Glob_decodeToml___closed__2;
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_121 = x_137;
goto block_127;
}
case 3:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_133, 0);
lean_inc(x_138);
lean_dec(x_133);
x_139 = l_Lake_Glob_decodeToml___closed__2;
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_121 = x_140;
goto block_127;
}
default: 
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_133);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_133, 1);
lean_dec(x_142);
x_143 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_133, 0);
lean_ctor_set(x_133, 1, x_143);
x_121 = x_133;
goto block_127;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_133, 0);
lean_inc(x_144);
lean_dec(x_133);
x_145 = l_Lake_Glob_decodeToml___closed__2;
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_121 = x_146;
goto block_127;
}
}
}
}
block_120:
{
lean_object* x_18; lean_object* x_19; lean_object* x_60; lean_object* x_61; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_81 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_82 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_80, x_81, x_1);
x_83 = lean_box(0);
if (lean_obj_tag(x_82) == 0)
{
x_60 = x_83;
x_61 = x_17;
goto block_79;
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_82);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_82, 0);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
switch (lean_obj_tag(x_92)) {
case 0:
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
lean_ctor_set(x_82, 0, x_93);
x_60 = x_82;
x_61 = x_17;
goto block_79;
}
case 2:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_82);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lake_Glob_decodeToml___closed__2;
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_84 = x_96;
goto block_89;
}
case 3:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_free_object(x_82);
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_98 = l_Lake_Glob_decodeToml___closed__2;
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_84 = x_99;
goto block_89;
}
default: 
{
uint8_t x_100; 
lean_free_object(x_82);
x_100 = !lean_is_exclusive(x_92);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_92, 1);
lean_dec(x_101);
x_102 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_92, 0);
lean_ctor_set(x_92, 1, x_102);
x_84 = x_92;
goto block_89;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_92, 0);
lean_inc(x_103);
lean_dec(x_92);
x_104 = l_Lake_Glob_decodeToml___closed__2;
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_84 = x_105;
goto block_89;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_82, 0);
lean_inc(x_106);
lean_dec(x_82);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
switch (lean_obj_tag(x_107)) {
case 0:
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_60 = x_109;
x_61 = x_17;
goto block_79;
}
case 2:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
lean_dec(x_107);
x_111 = l_Lake_Glob_decodeToml___closed__2;
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_84 = x_112;
goto block_89;
}
case 3:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
lean_dec(x_107);
x_114 = l_Lake_Glob_decodeToml___closed__2;
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_84 = x_115;
goto block_89;
}
default: 
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_107, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_117 = x_107;
} else {
 lean_dec_ref(x_107);
 x_117 = lean_box(0);
}
x_118 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
 lean_ctor_set_tag(x_119, 0);
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
x_84 = x_119;
goto block_89;
}
}
}
}
block_59:
{
lean_object* x_20; lean_object* x_21; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_20 = lean_box(0);
x_28 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_29 = l_Lake_Dependency_decodeToml___closed__2;
x_30 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_28, x_29, x_1);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_16);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_14);
lean_ctor_set(x_31, 4, x_20);
x_3 = x_31;
x_4 = x_19;
goto block_8;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
switch (lean_obj_tag(x_33)) {
case 0:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_33, 1);
lean_dec(x_35);
x_36 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_33, 1, x_36);
x_21 = x_33;
goto block_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
lean_inc(x_37);
lean_dec(x_33);
x_38 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_21 = x_39;
goto block_27;
}
}
case 2:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
lean_dec(x_33);
x_41 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_21 = x_42;
goto block_27;
}
case 3:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
lean_dec(x_33);
x_44 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_21 = x_45;
goto block_27;
}
case 6:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_33, 1);
lean_inc(x_46);
lean_dec(x_33);
x_47 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_46);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Array_append___rarg(x_19, x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_11);
lean_ctor_set(x_50, 1, x_16);
lean_ctor_set(x_50, 2, x_18);
lean_ctor_set(x_50, 3, x_14);
lean_ctor_set(x_50, 4, x_20);
x_3 = x_50;
x_4 = x_49;
goto block_8;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_47, 0);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_11);
lean_ctor_set(x_52, 1, x_16);
lean_ctor_set(x_52, 2, x_18);
lean_ctor_set(x_52, 3, x_14);
lean_ctor_set(x_52, 4, x_51);
x_3 = x_52;
x_4 = x_19;
goto block_8;
}
}
default: 
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_33);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_33, 1);
lean_dec(x_54);
x_55 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 1, x_55);
x_21 = x_33;
goto block_27;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_33, 0);
lean_inc(x_56);
lean_dec(x_33);
x_57 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_21 = x_58;
goto block_27;
}
}
}
}
block_27:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_array_mk(x_23);
x_25 = l_Array_append___rarg(x_19, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_14);
lean_ctor_set(x_26, 4, x_20);
x_3 = x_26;
x_4 = x_25;
goto block_8;
}
}
block_79:
{
if (lean_obj_tag(x_60) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_62; 
x_62 = lean_box(0);
x_18 = x_62;
x_19 = x_61;
goto block_59;
}
else
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_12);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_12, 0);
x_65 = l_Lake_Dependency_decodeToml___closed__3;
x_66 = lean_string_append(x_65, x_64);
lean_dec(x_64);
x_67 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_68 = lean_string_append(x_66, x_67);
lean_ctor_set(x_12, 0, x_68);
x_18 = x_12;
x_19 = x_61;
goto block_59;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_12, 0);
lean_inc(x_69);
lean_dec(x_12);
x_70 = l_Lake_Dependency_decodeToml___closed__3;
x_71 = lean_string_append(x_70, x_69);
lean_dec(x_69);
x_72 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_73 = lean_string_append(x_71, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_18 = x_74;
x_19 = x_61;
goto block_59;
}
}
else
{
lean_object* x_75; 
lean_dec(x_12);
x_75 = lean_box(0);
x_18 = x_75;
x_19 = x_61;
goto block_59;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_12);
x_76 = !lean_is_exclusive(x_60);
if (x_76 == 0)
{
x_18 = x_60;
x_19 = x_61;
goto block_59;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_60, 0);
lean_inc(x_77);
lean_dec(x_60);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_18 = x_78;
x_19 = x_61;
goto block_59;
}
}
}
block_89:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_array_mk(x_86);
x_88 = l_Array_append___rarg(x_17, x_87);
lean_dec(x_87);
x_60 = x_83;
x_61 = x_88;
goto block_79;
}
}
block_127:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_array_mk(x_123);
x_125 = l_Array_append___rarg(x_15, x_124);
lean_dec(x_124);
x_126 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_16 = x_126;
x_17 = x_125;
goto block_120;
}
}
block_394:
{
lean_object* x_150; lean_object* x_151; lean_object* x_254; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_262 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_263 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_261, x_262, x_1);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_309; lean_object* x_310; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_328 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_329 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_261, x_328, x_1);
x_330 = lean_box(0);
if (lean_obj_tag(x_329) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
x_264 = x_330;
x_265 = x_149;
goto block_308;
}
else
{
uint8_t x_337; 
x_337 = !lean_is_exclusive(x_12);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_338 = lean_ctor_get(x_12, 0);
x_339 = l_Lake_Dependency_decodeToml___closed__3;
x_340 = lean_string_append(x_339, x_338);
lean_dec(x_338);
x_341 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_342 = lean_string_append(x_340, x_341);
lean_ctor_set(x_12, 0, x_342);
x_264 = x_12;
x_265 = x_149;
goto block_308;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_343 = lean_ctor_get(x_12, 0);
lean_inc(x_343);
lean_dec(x_12);
x_344 = l_Lake_Dependency_decodeToml___closed__3;
x_345 = lean_string_append(x_344, x_343);
lean_dec(x_343);
x_346 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_347 = lean_string_append(x_345, x_346);
x_348 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_348, 0, x_347);
x_264 = x_348;
x_265 = x_149;
goto block_308;
}
}
}
else
{
uint8_t x_349; 
x_349 = !lean_is_exclusive(x_329);
if (x_349 == 0)
{
lean_object* x_350; lean_object* x_351; 
x_350 = lean_ctor_get(x_329, 0);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
lean_dec(x_350);
switch (lean_obj_tag(x_351)) {
case 0:
{
lean_object* x_352; 
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
lean_dec(x_351);
lean_ctor_set(x_329, 0, x_352);
x_309 = x_329;
x_310 = x_149;
goto block_327;
}
case 2:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_free_object(x_329);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
lean_dec(x_351);
x_354 = l_Lake_Glob_decodeToml___closed__2;
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_353);
lean_ctor_set(x_355, 1, x_354);
x_331 = x_355;
goto block_336;
}
case 3:
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_free_object(x_329);
x_356 = lean_ctor_get(x_351, 0);
lean_inc(x_356);
lean_dec(x_351);
x_357 = l_Lake_Glob_decodeToml___closed__2;
x_358 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_357);
x_331 = x_358;
goto block_336;
}
default: 
{
uint8_t x_359; 
lean_free_object(x_329);
x_359 = !lean_is_exclusive(x_351);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; 
x_360 = lean_ctor_get(x_351, 1);
lean_dec(x_360);
x_361 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_351, 0);
lean_ctor_set(x_351, 1, x_361);
x_331 = x_351;
goto block_336;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_351, 0);
lean_inc(x_362);
lean_dec(x_351);
x_363 = l_Lake_Glob_decodeToml___closed__2;
x_364 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
x_331 = x_364;
goto block_336;
}
}
}
}
else
{
lean_object* x_365; lean_object* x_366; 
x_365 = lean_ctor_get(x_329, 0);
lean_inc(x_365);
lean_dec(x_329);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
lean_dec(x_365);
switch (lean_obj_tag(x_366)) {
case 0:
{
lean_object* x_367; lean_object* x_368; 
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_367);
x_309 = x_368;
x_310 = x_149;
goto block_327;
}
case 2:
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_369 = lean_ctor_get(x_366, 0);
lean_inc(x_369);
lean_dec(x_366);
x_370 = l_Lake_Glob_decodeToml___closed__2;
x_371 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set(x_371, 1, x_370);
x_331 = x_371;
goto block_336;
}
case 3:
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_366, 0);
lean_inc(x_372);
lean_dec(x_366);
x_373 = l_Lake_Glob_decodeToml___closed__2;
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_331 = x_374;
goto block_336;
}
default: 
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_375 = lean_ctor_get(x_366, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_376 = x_366;
} else {
 lean_dec_ref(x_366);
 x_376 = lean_box(0);
}
x_377 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_376)) {
 x_378 = lean_alloc_ctor(0, 2, 0);
} else {
 x_378 = x_376;
 lean_ctor_set_tag(x_378, 0);
}
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_377);
x_331 = x_378;
goto block_336;
}
}
}
}
block_308:
{
lean_object* x_266; lean_object* x_267; lean_object* x_275; lean_object* x_276; 
x_266 = lean_box(0);
x_275 = l_Lake_Dependency_decodeToml___closed__2;
x_276 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_261, x_275, x_1);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; lean_object* x_278; 
x_277 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_278 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_278, 0, x_11);
lean_ctor_set(x_278, 1, x_277);
lean_ctor_set(x_278, 2, x_264);
lean_ctor_set(x_278, 3, x_148);
lean_ctor_set(x_278, 4, x_266);
x_3 = x_278;
x_4 = x_265;
goto block_8;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_276, 0);
lean_inc(x_279);
lean_dec(x_276);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
switch (lean_obj_tag(x_280)) {
case 0:
{
uint8_t x_281; 
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_280, 1);
lean_dec(x_282);
x_283 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_280, 1, x_283);
x_267 = x_280;
goto block_274;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_280, 0);
lean_inc(x_284);
lean_dec(x_280);
x_285 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
x_267 = x_286;
goto block_274;
}
}
case 2:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_280, 0);
lean_inc(x_287);
lean_dec(x_280);
x_288 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_287);
lean_ctor_set(x_289, 1, x_288);
x_267 = x_289;
goto block_274;
}
case 3:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_280, 0);
lean_inc(x_290);
lean_dec(x_280);
x_291 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
x_267 = x_292;
goto block_274;
}
case 6:
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_280, 1);
lean_inc(x_293);
lean_dec(x_280);
x_294 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_293);
lean_dec(x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec(x_294);
x_296 = l_Array_append___rarg(x_265, x_295);
lean_dec(x_295);
x_297 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_298 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_298, 0, x_11);
lean_ctor_set(x_298, 1, x_297);
lean_ctor_set(x_298, 2, x_264);
lean_ctor_set(x_298, 3, x_148);
lean_ctor_set(x_298, 4, x_266);
x_3 = x_298;
x_4 = x_296;
goto block_8;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_294, 0);
lean_inc(x_299);
lean_dec(x_294);
x_300 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_301 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_301, 0, x_11);
lean_ctor_set(x_301, 1, x_300);
lean_ctor_set(x_301, 2, x_264);
lean_ctor_set(x_301, 3, x_148);
lean_ctor_set(x_301, 4, x_299);
x_3 = x_301;
x_4 = x_265;
goto block_8;
}
}
default: 
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_280);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_280, 1);
lean_dec(x_303);
x_304 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_280, 0);
lean_ctor_set(x_280, 1, x_304);
x_267 = x_280;
goto block_274;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_280, 0);
lean_inc(x_305);
lean_dec(x_280);
x_306 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_267 = x_307;
goto block_274;
}
}
}
}
block_274:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_268 = lean_box(0);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_array_mk(x_269);
x_271 = l_Array_append___rarg(x_265, x_270);
lean_dec(x_270);
x_272 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_273 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_273, 0, x_11);
lean_ctor_set(x_273, 1, x_272);
lean_ctor_set(x_273, 2, x_264);
lean_ctor_set(x_273, 3, x_148);
lean_ctor_set(x_273, 4, x_266);
x_3 = x_273;
x_4 = x_271;
goto block_8;
}
}
block_327:
{
if (lean_obj_tag(x_309) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_311; 
x_311 = lean_box(0);
x_264 = x_311;
x_265 = x_310;
goto block_308;
}
else
{
uint8_t x_312; 
x_312 = !lean_is_exclusive(x_12);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_313 = lean_ctor_get(x_12, 0);
x_314 = l_Lake_Dependency_decodeToml___closed__3;
x_315 = lean_string_append(x_314, x_313);
lean_dec(x_313);
x_316 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_317 = lean_string_append(x_315, x_316);
lean_ctor_set(x_12, 0, x_317);
x_264 = x_12;
x_265 = x_310;
goto block_308;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_318 = lean_ctor_get(x_12, 0);
lean_inc(x_318);
lean_dec(x_12);
x_319 = l_Lake_Dependency_decodeToml___closed__3;
x_320 = lean_string_append(x_319, x_318);
lean_dec(x_318);
x_321 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_322 = lean_string_append(x_320, x_321);
x_323 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_323, 0, x_322);
x_264 = x_323;
x_265 = x_310;
goto block_308;
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_12);
x_324 = !lean_is_exclusive(x_309);
if (x_324 == 0)
{
x_264 = x_309;
x_265 = x_310;
goto block_308;
}
else
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_ctor_get(x_309, 0);
lean_inc(x_325);
lean_dec(x_309);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_264 = x_326;
x_265 = x_310;
goto block_308;
}
}
}
block_336:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_332 = lean_box(0);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_array_mk(x_333);
x_335 = l_Array_append___rarg(x_149, x_334);
lean_dec(x_334);
x_309 = x_330;
x_310 = x_335;
goto block_327;
}
}
else
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_263, 0);
lean_inc(x_379);
lean_dec(x_263);
x_380 = lean_ctor_get(x_379, 1);
lean_inc(x_380);
lean_dec(x_379);
switch (lean_obj_tag(x_380)) {
case 0:
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_150 = x_381;
x_151 = x_149;
goto block_253;
}
case 2:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_380, 0);
lean_inc(x_382);
lean_dec(x_380);
x_383 = l_Lake_Glob_decodeToml___closed__2;
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
x_254 = x_384;
goto block_260;
}
case 3:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_380, 0);
lean_inc(x_385);
lean_dec(x_380);
x_386 = l_Lake_Glob_decodeToml___closed__2;
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
x_254 = x_387;
goto block_260;
}
default: 
{
uint8_t x_388; 
x_388 = !lean_is_exclusive(x_380);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_ctor_get(x_380, 1);
lean_dec(x_389);
x_390 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_380, 0);
lean_ctor_set(x_380, 1, x_390);
x_254 = x_380;
goto block_260;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_391 = lean_ctor_get(x_380, 0);
lean_inc(x_391);
lean_dec(x_380);
x_392 = l_Lake_Glob_decodeToml___closed__2;
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set(x_393, 1, x_392);
x_254 = x_393;
goto block_260;
}
}
}
}
block_253:
{
lean_object* x_152; lean_object* x_153; lean_object* x_194; lean_object* x_195; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_213 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_214 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_215 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_213, x_214, x_1);
x_216 = lean_box(0);
if (lean_obj_tag(x_215) == 0)
{
x_194 = x_216;
x_195 = x_151;
goto block_212;
}
else
{
uint8_t x_223; 
x_223 = !lean_is_exclusive(x_215);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
x_224 = lean_ctor_get(x_215, 0);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
switch (lean_obj_tag(x_225)) {
case 0:
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 1);
lean_inc(x_226);
lean_dec(x_225);
lean_ctor_set(x_215, 0, x_226);
x_194 = x_215;
x_195 = x_151;
goto block_212;
}
case 2:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_free_object(x_215);
x_227 = lean_ctor_get(x_225, 0);
lean_inc(x_227);
lean_dec(x_225);
x_228 = l_Lake_Glob_decodeToml___closed__2;
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_227);
lean_ctor_set(x_229, 1, x_228);
x_217 = x_229;
goto block_222;
}
case 3:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_free_object(x_215);
x_230 = lean_ctor_get(x_225, 0);
lean_inc(x_230);
lean_dec(x_225);
x_231 = l_Lake_Glob_decodeToml___closed__2;
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_217 = x_232;
goto block_222;
}
default: 
{
uint8_t x_233; 
lean_free_object(x_215);
x_233 = !lean_is_exclusive(x_225);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_225, 1);
lean_dec(x_234);
x_235 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_225, 0);
lean_ctor_set(x_225, 1, x_235);
x_217 = x_225;
goto block_222;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_225, 0);
lean_inc(x_236);
lean_dec(x_225);
x_237 = l_Lake_Glob_decodeToml___closed__2;
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_217 = x_238;
goto block_222;
}
}
}
}
else
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_215, 0);
lean_inc(x_239);
lean_dec(x_215);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
switch (lean_obj_tag(x_240)) {
case 0:
{
lean_object* x_241; lean_object* x_242; 
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_194 = x_242;
x_195 = x_151;
goto block_212;
}
case 2:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_240, 0);
lean_inc(x_243);
lean_dec(x_240);
x_244 = l_Lake_Glob_decodeToml___closed__2;
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
x_217 = x_245;
goto block_222;
}
case 3:
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_240, 0);
lean_inc(x_246);
lean_dec(x_240);
x_247 = l_Lake_Glob_decodeToml___closed__2;
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_217 = x_248;
goto block_222;
}
default: 
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_240, 0);
lean_inc(x_249);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_250 = x_240;
} else {
 lean_dec_ref(x_240);
 x_250 = lean_box(0);
}
x_251 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_250)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_250;
 lean_ctor_set_tag(x_252, 0);
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_251);
x_217 = x_252;
goto block_222;
}
}
}
}
block_193:
{
lean_object* x_154; lean_object* x_155; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_box(0);
x_162 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_163 = l_Lake_Dependency_decodeToml___closed__2;
x_164 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_162, x_163, x_1);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_165, 0, x_11);
lean_ctor_set(x_165, 1, x_150);
lean_ctor_set(x_165, 2, x_152);
lean_ctor_set(x_165, 3, x_148);
lean_ctor_set(x_165, 4, x_154);
x_3 = x_165;
x_4 = x_153;
goto block_8;
}
else
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_ctor_get(x_166, 1);
lean_inc(x_167);
lean_dec(x_166);
switch (lean_obj_tag(x_167)) {
case 0:
{
uint8_t x_168; 
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_167, 1);
lean_dec(x_169);
x_170 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_167, 1, x_170);
x_155 = x_167;
goto block_161;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_167, 0);
lean_inc(x_171);
lean_dec(x_167);
x_172 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
x_155 = x_173;
goto block_161;
}
}
case 2:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_167, 0);
lean_inc(x_174);
lean_dec(x_167);
x_175 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
x_155 = x_176;
goto block_161;
}
case 3:
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_167, 0);
lean_inc(x_177);
lean_dec(x_167);
x_178 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_155 = x_179;
goto block_161;
}
case 6:
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_167, 1);
lean_inc(x_180);
lean_dec(x_167);
x_181 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_180);
lean_dec(x_180);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Array_append___rarg(x_153, x_182);
lean_dec(x_182);
x_184 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_184, 0, x_11);
lean_ctor_set(x_184, 1, x_150);
lean_ctor_set(x_184, 2, x_152);
lean_ctor_set(x_184, 3, x_148);
lean_ctor_set(x_184, 4, x_154);
x_3 = x_184;
x_4 = x_183;
goto block_8;
}
else
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_181, 0);
lean_inc(x_185);
lean_dec(x_181);
x_186 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_186, 0, x_11);
lean_ctor_set(x_186, 1, x_150);
lean_ctor_set(x_186, 2, x_152);
lean_ctor_set(x_186, 3, x_148);
lean_ctor_set(x_186, 4, x_185);
x_3 = x_186;
x_4 = x_153;
goto block_8;
}
}
default: 
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_167);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_167, 1);
lean_dec(x_188);
x_189 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_167, 0);
lean_ctor_set(x_167, 1, x_189);
x_155 = x_167;
goto block_161;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_167, 0);
lean_inc(x_190);
lean_dec(x_167);
x_191 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_155 = x_192;
goto block_161;
}
}
}
}
block_161:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = lean_array_mk(x_157);
x_159 = l_Array_append___rarg(x_153, x_158);
lean_dec(x_158);
x_160 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_160, 0, x_11);
lean_ctor_set(x_160, 1, x_150);
lean_ctor_set(x_160, 2, x_152);
lean_ctor_set(x_160, 3, x_148);
lean_ctor_set(x_160, 4, x_154);
x_3 = x_160;
x_4 = x_159;
goto block_8;
}
}
block_212:
{
if (lean_obj_tag(x_194) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_196; 
x_196 = lean_box(0);
x_152 = x_196;
x_153 = x_195;
goto block_193;
}
else
{
uint8_t x_197; 
x_197 = !lean_is_exclusive(x_12);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_198 = lean_ctor_get(x_12, 0);
x_199 = l_Lake_Dependency_decodeToml___closed__3;
x_200 = lean_string_append(x_199, x_198);
lean_dec(x_198);
x_201 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_202 = lean_string_append(x_200, x_201);
lean_ctor_set(x_12, 0, x_202);
x_152 = x_12;
x_153 = x_195;
goto block_193;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_203 = lean_ctor_get(x_12, 0);
lean_inc(x_203);
lean_dec(x_12);
x_204 = l_Lake_Dependency_decodeToml___closed__3;
x_205 = lean_string_append(x_204, x_203);
lean_dec(x_203);
x_206 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_207 = lean_string_append(x_205, x_206);
x_208 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_152 = x_208;
x_153 = x_195;
goto block_193;
}
}
}
else
{
uint8_t x_209; 
lean_dec(x_12);
x_209 = !lean_is_exclusive(x_194);
if (x_209 == 0)
{
x_152 = x_194;
x_153 = x_195;
goto block_193;
}
else
{
lean_object* x_210; lean_object* x_211; 
x_210 = lean_ctor_get(x_194, 0);
lean_inc(x_210);
lean_dec(x_194);
x_211 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_152 = x_211;
x_153 = x_195;
goto block_193;
}
}
}
block_222:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_array_mk(x_219);
x_221 = l_Array_append___rarg(x_151, x_220);
lean_dec(x_220);
x_194 = x_216;
x_195 = x_221;
goto block_212;
}
}
block_260:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_255 = lean_box(0);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
x_257 = lean_array_mk(x_256);
x_258 = l_Array_append___rarg(x_149, x_257);
lean_dec(x_257);
x_259 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_150 = x_259;
x_151 = x_258;
goto block_253;
}
}
block_1173:
{
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_398 = l_Lake_Dependency_decodeToml___closed__6;
lean_inc(x_1);
x_399 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_397, x_398, x_1);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_400 = l_Lake_Dependency_decodeToml___closed__8;
lean_inc(x_1);
x_401 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_397, x_400, x_1);
x_402 = lean_box(0);
if (lean_obj_tag(x_401) == 0)
{
x_14 = x_402;
x_15 = x_396;
goto block_147;
}
else
{
uint8_t x_409; 
x_409 = !lean_is_exclusive(x_401);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; 
x_410 = lean_ctor_get(x_401, 0);
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
switch (lean_obj_tag(x_411)) {
case 0:
{
uint8_t x_412; 
lean_free_object(x_401);
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_411, 1);
lean_dec(x_413);
x_414 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_411, 1, x_414);
x_403 = x_411;
goto block_408;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_411, 0);
lean_inc(x_415);
lean_dec(x_411);
x_416 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
x_403 = x_417;
goto block_408;
}
}
case 2:
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_free_object(x_401);
x_418 = lean_ctor_get(x_411, 0);
lean_inc(x_418);
lean_dec(x_411);
x_419 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_420 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_403 = x_420;
goto block_408;
}
case 3:
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_free_object(x_401);
x_421 = lean_ctor_get(x_411, 0);
lean_inc(x_421);
lean_dec(x_411);
x_422 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
x_403 = x_423;
goto block_408;
}
case 6:
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_411, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_411, 1);
lean_inc(x_425);
lean_dec(x_411);
x_426 = l_Lake_DependencySrc_decodeToml(x_425, x_424);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; 
lean_free_object(x_401);
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
lean_dec(x_426);
x_428 = l_Array_append___rarg(x_396, x_427);
lean_dec(x_427);
x_14 = x_402;
x_15 = x_428;
goto block_147;
}
else
{
lean_object* x_429; 
x_429 = lean_ctor_get(x_426, 0);
lean_inc(x_429);
lean_dec(x_426);
lean_ctor_set(x_401, 0, x_429);
x_14 = x_401;
x_15 = x_396;
goto block_147;
}
}
default: 
{
uint8_t x_430; 
lean_free_object(x_401);
x_430 = !lean_is_exclusive(x_411);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; 
x_431 = lean_ctor_get(x_411, 1);
lean_dec(x_431);
x_432 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_411, 0);
lean_ctor_set(x_411, 1, x_432);
x_403 = x_411;
goto block_408;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_411, 0);
lean_inc(x_433);
lean_dec(x_411);
x_434 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_434);
x_403 = x_435;
goto block_408;
}
}
}
}
else
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_401, 0);
lean_inc(x_436);
lean_dec(x_401);
x_437 = lean_ctor_get(x_436, 1);
lean_inc(x_437);
lean_dec(x_436);
switch (lean_obj_tag(x_437)) {
case 0:
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_439 = x_437;
} else {
 lean_dec_ref(x_437);
 x_439 = lean_box(0);
}
x_440 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
if (lean_is_scalar(x_439)) {
 x_441 = lean_alloc_ctor(0, 2, 0);
} else {
 x_441 = x_439;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_440);
x_403 = x_441;
goto block_408;
}
case 2:
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_437, 0);
lean_inc(x_442);
lean_dec(x_437);
x_443 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_442);
lean_ctor_set(x_444, 1, x_443);
x_403 = x_444;
goto block_408;
}
case 3:
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_437, 0);
lean_inc(x_445);
lean_dec(x_437);
x_446 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
x_403 = x_447;
goto block_408;
}
case 6:
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_448 = lean_ctor_get(x_437, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_437, 1);
lean_inc(x_449);
lean_dec(x_437);
x_450 = l_Lake_DependencySrc_decodeToml(x_449, x_448);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
lean_dec(x_450);
x_452 = l_Array_append___rarg(x_396, x_451);
lean_dec(x_451);
x_14 = x_402;
x_15 = x_452;
goto block_147;
}
else
{
lean_object* x_453; lean_object* x_454; 
x_453 = lean_ctor_get(x_450, 0);
lean_inc(x_453);
lean_dec(x_450);
x_454 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_454, 0, x_453);
x_14 = x_454;
x_15 = x_396;
goto block_147;
}
}
default: 
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_455 = lean_ctor_get(x_437, 0);
lean_inc(x_455);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_456 = x_437;
} else {
 lean_dec_ref(x_437);
 x_456 = lean_box(0);
}
x_457 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
if (lean_is_scalar(x_456)) {
 x_458 = lean_alloc_ctor(0, 2, 0);
} else {
 x_458 = x_456;
 lean_ctor_set_tag(x_458, 0);
}
lean_ctor_set(x_458, 0, x_455);
lean_ctor_set(x_458, 1, x_457);
x_403 = x_458;
goto block_408;
}
}
}
}
block_408:
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_404 = lean_box(0);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_array_mk(x_405);
x_407 = l_Array_append___rarg(x_396, x_406);
lean_dec(x_406);
x_14 = x_402;
x_15 = x_407;
goto block_147;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_399, 0);
lean_inc(x_459);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 x_460 = x_399;
} else {
 lean_dec_ref(x_399);
 x_460 = lean_box(0);
}
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
switch (lean_obj_tag(x_461)) {
case 0:
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_462 = lean_ctor_get(x_461, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_463 = x_461;
} else {
 lean_dec_ref(x_461);
 x_463 = lean_box(0);
}
x_464 = l_Lake_DependencySrc_decodeToml___closed__2;
lean_inc(x_1);
x_465 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_397, x_464, x_1);
x_466 = lean_box(0);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_475; lean_object* x_476; 
lean_dec(x_463);
lean_dec(x_460);
lean_inc(x_12);
x_475 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_475, 0, x_462);
lean_ctor_set(x_475, 1, x_12);
lean_ctor_set(x_475, 2, x_466);
x_476 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_476, 0, x_475);
x_14 = x_476;
x_15 = x_396;
goto block_147;
}
else
{
uint8_t x_477; 
x_477 = !lean_is_exclusive(x_465);
if (x_477 == 0)
{
lean_object* x_478; lean_object* x_479; 
x_478 = lean_ctor_get(x_465, 0);
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
lean_dec(x_478);
switch (lean_obj_tag(x_479)) {
case 0:
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_463);
lean_dec(x_460);
x_480 = lean_ctor_get(x_479, 1);
lean_inc(x_480);
lean_dec(x_479);
lean_ctor_set(x_465, 0, x_480);
lean_inc(x_12);
x_481 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_481, 0, x_462);
lean_ctor_set(x_481, 1, x_12);
lean_ctor_set(x_481, 2, x_465);
x_482 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_482, 0, x_481);
x_14 = x_482;
x_15 = x_396;
goto block_147;
}
case 2:
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_free_object(x_465);
x_483 = lean_ctor_get(x_479, 0);
lean_inc(x_483);
lean_dec(x_479);
x_484 = l_Lake_Glob_decodeToml___closed__2;
x_485 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
x_467 = x_485;
goto block_474;
}
case 3:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_free_object(x_465);
x_486 = lean_ctor_get(x_479, 0);
lean_inc(x_486);
lean_dec(x_479);
x_487 = l_Lake_Glob_decodeToml___closed__2;
x_488 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
x_467 = x_488;
goto block_474;
}
default: 
{
uint8_t x_489; 
lean_free_object(x_465);
x_489 = !lean_is_exclusive(x_479);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; 
x_490 = lean_ctor_get(x_479, 1);
lean_dec(x_490);
x_491 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_479, 0);
lean_ctor_set(x_479, 1, x_491);
x_467 = x_479;
goto block_474;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_479, 0);
lean_inc(x_492);
lean_dec(x_479);
x_493 = l_Lake_Glob_decodeToml___closed__2;
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
x_467 = x_494;
goto block_474;
}
}
}
}
else
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_465, 0);
lean_inc(x_495);
lean_dec(x_465);
x_496 = lean_ctor_get(x_495, 1);
lean_inc(x_496);
lean_dec(x_495);
switch (lean_obj_tag(x_496)) {
case 0:
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_463);
lean_dec(x_460);
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
lean_dec(x_496);
x_498 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_498, 0, x_497);
lean_inc(x_12);
x_499 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_499, 0, x_462);
lean_ctor_set(x_499, 1, x_12);
lean_ctor_set(x_499, 2, x_498);
x_500 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_500, 0, x_499);
x_14 = x_500;
x_15 = x_396;
goto block_147;
}
case 2:
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_496, 0);
lean_inc(x_501);
lean_dec(x_496);
x_502 = l_Lake_Glob_decodeToml___closed__2;
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_501);
lean_ctor_set(x_503, 1, x_502);
x_467 = x_503;
goto block_474;
}
case 3:
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_504 = lean_ctor_get(x_496, 0);
lean_inc(x_504);
lean_dec(x_496);
x_505 = l_Lake_Glob_decodeToml___closed__2;
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
x_467 = x_506;
goto block_474;
}
default: 
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_507 = lean_ctor_get(x_496, 0);
lean_inc(x_507);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_508 = x_496;
} else {
 lean_dec_ref(x_496);
 x_508 = lean_box(0);
}
x_509 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(0, 2, 0);
} else {
 x_510 = x_508;
 lean_ctor_set_tag(x_510, 0);
}
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_509);
x_467 = x_510;
goto block_474;
}
}
}
}
block_474:
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_468 = lean_box(0);
if (lean_is_scalar(x_463)) {
 x_469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_469 = x_463;
 lean_ctor_set_tag(x_469, 1);
}
lean_ctor_set(x_469, 0, x_467);
lean_ctor_set(x_469, 1, x_468);
x_470 = lean_array_mk(x_469);
x_471 = l_Array_append___rarg(x_396, x_470);
lean_dec(x_470);
lean_inc(x_12);
x_472 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_472, 0, x_462);
lean_ctor_set(x_472, 1, x_12);
lean_ctor_set(x_472, 2, x_466);
if (lean_is_scalar(x_460)) {
 x_473 = lean_alloc_ctor(1, 1, 0);
} else {
 x_473 = x_460;
}
lean_ctor_set(x_473, 0, x_472);
x_14 = x_473;
x_15 = x_471;
goto block_147;
}
}
case 2:
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_460);
x_511 = lean_ctor_get(x_461, 0);
lean_inc(x_511);
lean_dec(x_461);
x_512 = l_Lake_Dependency_decodeToml___closed__9;
x_513 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
x_514 = lean_array_push(x_396, x_513);
x_515 = lean_box(0);
x_148 = x_515;
x_149 = x_514;
goto block_394;
}
case 3:
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_460);
x_516 = lean_ctor_get(x_461, 0);
lean_inc(x_516);
lean_dec(x_461);
x_517 = l_Lake_Dependency_decodeToml___closed__9;
x_518 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
x_519 = lean_array_push(x_396, x_518);
x_520 = lean_box(0);
x_148 = x_520;
x_149 = x_519;
goto block_394;
}
case 6:
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_775; lean_object* x_776; 
x_521 = lean_ctor_get(x_461, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_461, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 lean_ctor_release(x_461, 1);
 x_523 = x_461;
} else {
 lean_dec_ref(x_461);
 x_523 = lean_box(0);
}
x_775 = l_Lake_DependencySrc_decodeToml___closed__18;
lean_inc(x_522);
x_776 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_522, x_775, x_521);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
lean_dec(x_776);
x_778 = l_Array_append___rarg(x_396, x_777);
lean_dec(x_777);
x_779 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_524 = x_779;
x_525 = x_778;
goto block_774;
}
else
{
lean_object* x_780; 
x_780 = lean_ctor_get(x_776, 0);
lean_inc(x_780);
lean_dec(x_776);
x_524 = x_780;
x_525 = x_396;
goto block_774;
}
block_774:
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = l_Lake_DependencySrc_decodeToml___closed__2;
x_527 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_397, x_526, x_522);
x_528 = lean_box(0);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_627; lean_object* x_634; lean_object* x_635; 
lean_dec(x_523);
lean_dec(x_460);
x_537 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_537, 0, x_524);
lean_ctor_set(x_537, 1, x_12);
lean_ctor_set(x_537, 2, x_528);
x_538 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_538, 0, x_537);
x_634 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_635 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_397, x_634, x_1);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_681; lean_object* x_682; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_688 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_397, x_687, x_1);
if (lean_obj_tag(x_688) == 0)
{
x_636 = x_528;
x_637 = x_525;
goto block_680;
}
else
{
uint8_t x_695; 
x_695 = !lean_is_exclusive(x_688);
if (x_695 == 0)
{
lean_object* x_696; lean_object* x_697; 
x_696 = lean_ctor_get(x_688, 0);
x_697 = lean_ctor_get(x_696, 1);
lean_inc(x_697);
lean_dec(x_696);
switch (lean_obj_tag(x_697)) {
case 0:
{
lean_object* x_698; 
x_698 = lean_ctor_get(x_697, 1);
lean_inc(x_698);
lean_dec(x_697);
lean_ctor_set(x_688, 0, x_698);
x_681 = x_688;
x_682 = x_525;
goto block_686;
}
case 2:
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_free_object(x_688);
x_699 = lean_ctor_get(x_697, 0);
lean_inc(x_699);
lean_dec(x_697);
x_700 = l_Lake_Glob_decodeToml___closed__2;
x_701 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_701, 0, x_699);
lean_ctor_set(x_701, 1, x_700);
x_689 = x_701;
goto block_694;
}
case 3:
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_free_object(x_688);
x_702 = lean_ctor_get(x_697, 0);
lean_inc(x_702);
lean_dec(x_697);
x_703 = l_Lake_Glob_decodeToml___closed__2;
x_704 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_703);
x_689 = x_704;
goto block_694;
}
default: 
{
uint8_t x_705; 
lean_free_object(x_688);
x_705 = !lean_is_exclusive(x_697);
if (x_705 == 0)
{
lean_object* x_706; lean_object* x_707; 
x_706 = lean_ctor_get(x_697, 1);
lean_dec(x_706);
x_707 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_697, 0);
lean_ctor_set(x_697, 1, x_707);
x_689 = x_697;
goto block_694;
}
else
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; 
x_708 = lean_ctor_get(x_697, 0);
lean_inc(x_708);
lean_dec(x_697);
x_709 = l_Lake_Glob_decodeToml___closed__2;
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_708);
lean_ctor_set(x_710, 1, x_709);
x_689 = x_710;
goto block_694;
}
}
}
}
else
{
lean_object* x_711; lean_object* x_712; 
x_711 = lean_ctor_get(x_688, 0);
lean_inc(x_711);
lean_dec(x_688);
x_712 = lean_ctor_get(x_711, 1);
lean_inc(x_712);
lean_dec(x_711);
switch (lean_obj_tag(x_712)) {
case 0:
{
lean_object* x_713; lean_object* x_714; 
x_713 = lean_ctor_get(x_712, 1);
lean_inc(x_713);
lean_dec(x_712);
x_714 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_714, 0, x_713);
x_681 = x_714;
x_682 = x_525;
goto block_686;
}
case 2:
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_712, 0);
lean_inc(x_715);
lean_dec(x_712);
x_716 = l_Lake_Glob_decodeToml___closed__2;
x_717 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
x_689 = x_717;
goto block_694;
}
case 3:
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_712, 0);
lean_inc(x_718);
lean_dec(x_712);
x_719 = l_Lake_Glob_decodeToml___closed__2;
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
x_689 = x_720;
goto block_694;
}
default: 
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_721 = lean_ctor_get(x_712, 0);
lean_inc(x_721);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_722 = x_712;
} else {
 lean_dec_ref(x_712);
 x_722 = lean_box(0);
}
x_723 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_722)) {
 x_724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_724 = x_722;
 lean_ctor_set_tag(x_724, 0);
}
lean_ctor_set(x_724, 0, x_721);
lean_ctor_set(x_724, 1, x_723);
x_689 = x_724;
goto block_694;
}
}
}
}
block_680:
{
lean_object* x_638; lean_object* x_639; lean_object* x_647; lean_object* x_648; 
x_638 = lean_box(0);
x_647 = l_Lake_Dependency_decodeToml___closed__2;
x_648 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_397, x_647, x_1);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; 
x_649 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_650 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_650, 0, x_11);
lean_ctor_set(x_650, 1, x_649);
lean_ctor_set(x_650, 2, x_636);
lean_ctor_set(x_650, 3, x_538);
lean_ctor_set(x_650, 4, x_638);
x_3 = x_650;
x_4 = x_637;
goto block_8;
}
else
{
lean_object* x_651; lean_object* x_652; 
x_651 = lean_ctor_get(x_648, 0);
lean_inc(x_651);
lean_dec(x_648);
x_652 = lean_ctor_get(x_651, 1);
lean_inc(x_652);
lean_dec(x_651);
switch (lean_obj_tag(x_652)) {
case 0:
{
uint8_t x_653; 
x_653 = !lean_is_exclusive(x_652);
if (x_653 == 0)
{
lean_object* x_654; lean_object* x_655; 
x_654 = lean_ctor_get(x_652, 1);
lean_dec(x_654);
x_655 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_652, 1, x_655);
x_639 = x_652;
goto block_646;
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_652, 0);
lean_inc(x_656);
lean_dec(x_652);
x_657 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_658 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_658, 0, x_656);
lean_ctor_set(x_658, 1, x_657);
x_639 = x_658;
goto block_646;
}
}
case 2:
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_652, 0);
lean_inc(x_659);
lean_dec(x_652);
x_660 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
x_639 = x_661;
goto block_646;
}
case 3:
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_652, 0);
lean_inc(x_662);
lean_dec(x_652);
x_663 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_664 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_664, 0, x_662);
lean_ctor_set(x_664, 1, x_663);
x_639 = x_664;
goto block_646;
}
case 6:
{
lean_object* x_665; lean_object* x_666; 
x_665 = lean_ctor_get(x_652, 1);
lean_inc(x_665);
lean_dec(x_652);
x_666 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_665);
lean_dec(x_665);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
lean_dec(x_666);
x_668 = l_Array_append___rarg(x_637, x_667);
lean_dec(x_667);
x_669 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_670 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_670, 0, x_11);
lean_ctor_set(x_670, 1, x_669);
lean_ctor_set(x_670, 2, x_636);
lean_ctor_set(x_670, 3, x_538);
lean_ctor_set(x_670, 4, x_638);
x_3 = x_670;
x_4 = x_668;
goto block_8;
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = lean_ctor_get(x_666, 0);
lean_inc(x_671);
lean_dec(x_666);
x_672 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_673 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_673, 0, x_11);
lean_ctor_set(x_673, 1, x_672);
lean_ctor_set(x_673, 2, x_636);
lean_ctor_set(x_673, 3, x_538);
lean_ctor_set(x_673, 4, x_671);
x_3 = x_673;
x_4 = x_637;
goto block_8;
}
}
default: 
{
uint8_t x_674; 
x_674 = !lean_is_exclusive(x_652);
if (x_674 == 0)
{
lean_object* x_675; lean_object* x_676; 
x_675 = lean_ctor_get(x_652, 1);
lean_dec(x_675);
x_676 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_652, 0);
lean_ctor_set(x_652, 1, x_676);
x_639 = x_652;
goto block_646;
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; 
x_677 = lean_ctor_get(x_652, 0);
lean_inc(x_677);
lean_dec(x_652);
x_678 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
x_639 = x_679;
goto block_646;
}
}
}
}
block_646:
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_640 = lean_box(0);
x_641 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_641, 0, x_639);
lean_ctor_set(x_641, 1, x_640);
x_642 = lean_array_mk(x_641);
x_643 = l_Array_append___rarg(x_637, x_642);
lean_dec(x_642);
x_644 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_645 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_645, 0, x_11);
lean_ctor_set(x_645, 1, x_644);
lean_ctor_set(x_645, 2, x_636);
lean_ctor_set(x_645, 3, x_538);
lean_ctor_set(x_645, 4, x_638);
x_3 = x_645;
x_4 = x_643;
goto block_8;
}
}
block_686:
{
if (lean_obj_tag(x_681) == 0)
{
x_636 = x_528;
x_637 = x_682;
goto block_680;
}
else
{
uint8_t x_683; 
x_683 = !lean_is_exclusive(x_681);
if (x_683 == 0)
{
x_636 = x_681;
x_637 = x_682;
goto block_680;
}
else
{
lean_object* x_684; lean_object* x_685; 
x_684 = lean_ctor_get(x_681, 0);
lean_inc(x_684);
lean_dec(x_681);
x_685 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_685, 0, x_684);
x_636 = x_685;
x_637 = x_682;
goto block_680;
}
}
}
block_694:
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_690 = lean_box(0);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
x_692 = lean_array_mk(x_691);
x_693 = l_Array_append___rarg(x_525, x_692);
lean_dec(x_692);
x_681 = x_528;
x_682 = x_693;
goto block_686;
}
}
else
{
lean_object* x_725; lean_object* x_726; 
x_725 = lean_ctor_get(x_635, 0);
lean_inc(x_725);
lean_dec(x_635);
x_726 = lean_ctor_get(x_725, 1);
lean_inc(x_726);
lean_dec(x_725);
switch (lean_obj_tag(x_726)) {
case 0:
{
lean_object* x_727; 
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
lean_dec(x_726);
x_539 = x_727;
x_540 = x_525;
goto block_626;
}
case 2:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; 
x_728 = lean_ctor_get(x_726, 0);
lean_inc(x_728);
lean_dec(x_726);
x_729 = l_Lake_Glob_decodeToml___closed__2;
x_730 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_730, 0, x_728);
lean_ctor_set(x_730, 1, x_729);
x_627 = x_730;
goto block_633;
}
case 3:
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_731 = lean_ctor_get(x_726, 0);
lean_inc(x_731);
lean_dec(x_726);
x_732 = l_Lake_Glob_decodeToml___closed__2;
x_733 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_733, 0, x_731);
lean_ctor_set(x_733, 1, x_732);
x_627 = x_733;
goto block_633;
}
default: 
{
uint8_t x_734; 
x_734 = !lean_is_exclusive(x_726);
if (x_734 == 0)
{
lean_object* x_735; lean_object* x_736; 
x_735 = lean_ctor_get(x_726, 1);
lean_dec(x_735);
x_736 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_726, 0);
lean_ctor_set(x_726, 1, x_736);
x_627 = x_726;
goto block_633;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_726, 0);
lean_inc(x_737);
lean_dec(x_726);
x_738 = l_Lake_Glob_decodeToml___closed__2;
x_739 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_739, 0, x_737);
lean_ctor_set(x_739, 1, x_738);
x_627 = x_739;
goto block_633;
}
}
}
}
block_626:
{
lean_object* x_541; lean_object* x_542; lean_object* x_582; lean_object* x_583; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_589 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_397, x_588, x_1);
if (lean_obj_tag(x_589) == 0)
{
x_582 = x_528;
x_583 = x_540;
goto block_587;
}
else
{
uint8_t x_596; 
x_596 = !lean_is_exclusive(x_589);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; 
x_597 = lean_ctor_get(x_589, 0);
x_598 = lean_ctor_get(x_597, 1);
lean_inc(x_598);
lean_dec(x_597);
switch (lean_obj_tag(x_598)) {
case 0:
{
lean_object* x_599; 
x_599 = lean_ctor_get(x_598, 1);
lean_inc(x_599);
lean_dec(x_598);
lean_ctor_set(x_589, 0, x_599);
x_582 = x_589;
x_583 = x_540;
goto block_587;
}
case 2:
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
lean_free_object(x_589);
x_600 = lean_ctor_get(x_598, 0);
lean_inc(x_600);
lean_dec(x_598);
x_601 = l_Lake_Glob_decodeToml___closed__2;
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
x_590 = x_602;
goto block_595;
}
case 3:
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_free_object(x_589);
x_603 = lean_ctor_get(x_598, 0);
lean_inc(x_603);
lean_dec(x_598);
x_604 = l_Lake_Glob_decodeToml___closed__2;
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_603);
lean_ctor_set(x_605, 1, x_604);
x_590 = x_605;
goto block_595;
}
default: 
{
uint8_t x_606; 
lean_free_object(x_589);
x_606 = !lean_is_exclusive(x_598);
if (x_606 == 0)
{
lean_object* x_607; lean_object* x_608; 
x_607 = lean_ctor_get(x_598, 1);
lean_dec(x_607);
x_608 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_598, 0);
lean_ctor_set(x_598, 1, x_608);
x_590 = x_598;
goto block_595;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_ctor_get(x_598, 0);
lean_inc(x_609);
lean_dec(x_598);
x_610 = l_Lake_Glob_decodeToml___closed__2;
x_611 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_611, 0, x_609);
lean_ctor_set(x_611, 1, x_610);
x_590 = x_611;
goto block_595;
}
}
}
}
else
{
lean_object* x_612; lean_object* x_613; 
x_612 = lean_ctor_get(x_589, 0);
lean_inc(x_612);
lean_dec(x_589);
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
lean_dec(x_612);
switch (lean_obj_tag(x_613)) {
case 0:
{
lean_object* x_614; lean_object* x_615; 
x_614 = lean_ctor_get(x_613, 1);
lean_inc(x_614);
lean_dec(x_613);
x_615 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_615, 0, x_614);
x_582 = x_615;
x_583 = x_540;
goto block_587;
}
case 2:
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_616 = lean_ctor_get(x_613, 0);
lean_inc(x_616);
lean_dec(x_613);
x_617 = l_Lake_Glob_decodeToml___closed__2;
x_618 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_618, 0, x_616);
lean_ctor_set(x_618, 1, x_617);
x_590 = x_618;
goto block_595;
}
case 3:
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_613, 0);
lean_inc(x_619);
lean_dec(x_613);
x_620 = l_Lake_Glob_decodeToml___closed__2;
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set(x_621, 1, x_620);
x_590 = x_621;
goto block_595;
}
default: 
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_622 = lean_ctor_get(x_613, 0);
lean_inc(x_622);
if (lean_is_exclusive(x_613)) {
 lean_ctor_release(x_613, 0);
 lean_ctor_release(x_613, 1);
 x_623 = x_613;
} else {
 lean_dec_ref(x_613);
 x_623 = lean_box(0);
}
x_624 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_623)) {
 x_625 = lean_alloc_ctor(0, 2, 0);
} else {
 x_625 = x_623;
 lean_ctor_set_tag(x_625, 0);
}
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_624);
x_590 = x_625;
goto block_595;
}
}
}
}
block_581:
{
lean_object* x_543; lean_object* x_544; lean_object* x_551; lean_object* x_552; 
x_543 = lean_box(0);
x_551 = l_Lake_Dependency_decodeToml___closed__2;
x_552 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_397, x_551, x_1);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; 
x_553 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_553, 0, x_11);
lean_ctor_set(x_553, 1, x_539);
lean_ctor_set(x_553, 2, x_541);
lean_ctor_set(x_553, 3, x_538);
lean_ctor_set(x_553, 4, x_543);
x_3 = x_553;
x_4 = x_542;
goto block_8;
}
else
{
lean_object* x_554; lean_object* x_555; 
x_554 = lean_ctor_get(x_552, 0);
lean_inc(x_554);
lean_dec(x_552);
x_555 = lean_ctor_get(x_554, 1);
lean_inc(x_555);
lean_dec(x_554);
switch (lean_obj_tag(x_555)) {
case 0:
{
uint8_t x_556; 
x_556 = !lean_is_exclusive(x_555);
if (x_556 == 0)
{
lean_object* x_557; lean_object* x_558; 
x_557 = lean_ctor_get(x_555, 1);
lean_dec(x_557);
x_558 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_555, 1, x_558);
x_544 = x_555;
goto block_550;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_555, 0);
lean_inc(x_559);
lean_dec(x_555);
x_560 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
x_544 = x_561;
goto block_550;
}
}
case 2:
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_555, 0);
lean_inc(x_562);
lean_dec(x_555);
x_563 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_564 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
x_544 = x_564;
goto block_550;
}
case 3:
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_555, 0);
lean_inc(x_565);
lean_dec(x_555);
x_566 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_567 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
x_544 = x_567;
goto block_550;
}
case 6:
{
lean_object* x_568; lean_object* x_569; 
x_568 = lean_ctor_get(x_555, 1);
lean_inc(x_568);
lean_dec(x_555);
x_569 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_568);
lean_dec(x_568);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
lean_dec(x_569);
x_571 = l_Array_append___rarg(x_542, x_570);
lean_dec(x_570);
x_572 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_572, 0, x_11);
lean_ctor_set(x_572, 1, x_539);
lean_ctor_set(x_572, 2, x_541);
lean_ctor_set(x_572, 3, x_538);
lean_ctor_set(x_572, 4, x_543);
x_3 = x_572;
x_4 = x_571;
goto block_8;
}
else
{
lean_object* x_573; lean_object* x_574; 
x_573 = lean_ctor_get(x_569, 0);
lean_inc(x_573);
lean_dec(x_569);
x_574 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_574, 0, x_11);
lean_ctor_set(x_574, 1, x_539);
lean_ctor_set(x_574, 2, x_541);
lean_ctor_set(x_574, 3, x_538);
lean_ctor_set(x_574, 4, x_573);
x_3 = x_574;
x_4 = x_542;
goto block_8;
}
}
default: 
{
uint8_t x_575; 
x_575 = !lean_is_exclusive(x_555);
if (x_575 == 0)
{
lean_object* x_576; lean_object* x_577; 
x_576 = lean_ctor_get(x_555, 1);
lean_dec(x_576);
x_577 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_555, 0);
lean_ctor_set(x_555, 1, x_577);
x_544 = x_555;
goto block_550;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_555, 0);
lean_inc(x_578);
lean_dec(x_555);
x_579 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_578);
lean_ctor_set(x_580, 1, x_579);
x_544 = x_580;
goto block_550;
}
}
}
}
block_550:
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_545 = lean_box(0);
x_546 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_546, 0, x_544);
lean_ctor_set(x_546, 1, x_545);
x_547 = lean_array_mk(x_546);
x_548 = l_Array_append___rarg(x_542, x_547);
lean_dec(x_547);
x_549 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_549, 0, x_11);
lean_ctor_set(x_549, 1, x_539);
lean_ctor_set(x_549, 2, x_541);
lean_ctor_set(x_549, 3, x_538);
lean_ctor_set(x_549, 4, x_543);
x_3 = x_549;
x_4 = x_548;
goto block_8;
}
}
block_587:
{
if (lean_obj_tag(x_582) == 0)
{
x_541 = x_528;
x_542 = x_583;
goto block_581;
}
else
{
uint8_t x_584; 
x_584 = !lean_is_exclusive(x_582);
if (x_584 == 0)
{
x_541 = x_582;
x_542 = x_583;
goto block_581;
}
else
{
lean_object* x_585; lean_object* x_586; 
x_585 = lean_ctor_get(x_582, 0);
lean_inc(x_585);
lean_dec(x_582);
x_586 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_586, 0, x_585);
x_541 = x_586;
x_542 = x_583;
goto block_581;
}
}
}
block_595:
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_591 = lean_box(0);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
x_593 = lean_array_mk(x_592);
x_594 = l_Array_append___rarg(x_540, x_593);
lean_dec(x_593);
x_582 = x_528;
x_583 = x_594;
goto block_587;
}
}
block_633:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_628 = lean_box(0);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_627);
lean_ctor_set(x_629, 1, x_628);
x_630 = lean_array_mk(x_629);
x_631 = l_Array_append___rarg(x_525, x_630);
lean_dec(x_630);
x_632 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_539 = x_632;
x_540 = x_631;
goto block_626;
}
}
else
{
uint8_t x_740; 
x_740 = !lean_is_exclusive(x_527);
if (x_740 == 0)
{
lean_object* x_741; lean_object* x_742; 
x_741 = lean_ctor_get(x_527, 0);
x_742 = lean_ctor_get(x_741, 1);
lean_inc(x_742);
lean_dec(x_741);
switch (lean_obj_tag(x_742)) {
case 0:
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_523);
lean_dec(x_460);
x_743 = lean_ctor_get(x_742, 1);
lean_inc(x_743);
lean_dec(x_742);
lean_ctor_set(x_527, 0, x_743);
lean_inc(x_12);
x_744 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_744, 0, x_524);
lean_ctor_set(x_744, 1, x_12);
lean_ctor_set(x_744, 2, x_527);
x_745 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_745, 0, x_744);
x_14 = x_745;
x_15 = x_525;
goto block_147;
}
case 2:
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; 
lean_free_object(x_527);
x_746 = lean_ctor_get(x_742, 0);
lean_inc(x_746);
lean_dec(x_742);
x_747 = l_Lake_Glob_decodeToml___closed__2;
x_748 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_748, 0, x_746);
lean_ctor_set(x_748, 1, x_747);
x_529 = x_748;
goto block_536;
}
case 3:
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_free_object(x_527);
x_749 = lean_ctor_get(x_742, 0);
lean_inc(x_749);
lean_dec(x_742);
x_750 = l_Lake_Glob_decodeToml___closed__2;
x_751 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_751, 0, x_749);
lean_ctor_set(x_751, 1, x_750);
x_529 = x_751;
goto block_536;
}
default: 
{
uint8_t x_752; 
lean_free_object(x_527);
x_752 = !lean_is_exclusive(x_742);
if (x_752 == 0)
{
lean_object* x_753; lean_object* x_754; 
x_753 = lean_ctor_get(x_742, 1);
lean_dec(x_753);
x_754 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_742, 0);
lean_ctor_set(x_742, 1, x_754);
x_529 = x_742;
goto block_536;
}
else
{
lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_755 = lean_ctor_get(x_742, 0);
lean_inc(x_755);
lean_dec(x_742);
x_756 = l_Lake_Glob_decodeToml___closed__2;
x_757 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_757, 0, x_755);
lean_ctor_set(x_757, 1, x_756);
x_529 = x_757;
goto block_536;
}
}
}
}
else
{
lean_object* x_758; lean_object* x_759; 
x_758 = lean_ctor_get(x_527, 0);
lean_inc(x_758);
lean_dec(x_527);
x_759 = lean_ctor_get(x_758, 1);
lean_inc(x_759);
lean_dec(x_758);
switch (lean_obj_tag(x_759)) {
case 0:
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_dec(x_523);
lean_dec(x_460);
x_760 = lean_ctor_get(x_759, 1);
lean_inc(x_760);
lean_dec(x_759);
x_761 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_761, 0, x_760);
lean_inc(x_12);
x_762 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_762, 0, x_524);
lean_ctor_set(x_762, 1, x_12);
lean_ctor_set(x_762, 2, x_761);
x_763 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_763, 0, x_762);
x_14 = x_763;
x_15 = x_525;
goto block_147;
}
case 2:
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_764 = lean_ctor_get(x_759, 0);
lean_inc(x_764);
lean_dec(x_759);
x_765 = l_Lake_Glob_decodeToml___closed__2;
x_766 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_766, 0, x_764);
lean_ctor_set(x_766, 1, x_765);
x_529 = x_766;
goto block_536;
}
case 3:
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_759, 0);
lean_inc(x_767);
lean_dec(x_759);
x_768 = l_Lake_Glob_decodeToml___closed__2;
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_768);
x_529 = x_769;
goto block_536;
}
default: 
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_770 = lean_ctor_get(x_759, 0);
lean_inc(x_770);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 x_771 = x_759;
} else {
 lean_dec_ref(x_759);
 x_771 = lean_box(0);
}
x_772 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_771)) {
 x_773 = lean_alloc_ctor(0, 2, 0);
} else {
 x_773 = x_771;
 lean_ctor_set_tag(x_773, 0);
}
lean_ctor_set(x_773, 0, x_770);
lean_ctor_set(x_773, 1, x_772);
x_529 = x_773;
goto block_536;
}
}
}
}
block_536:
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
x_530 = lean_box(0);
if (lean_is_scalar(x_523)) {
 x_531 = lean_alloc_ctor(1, 2, 0);
} else {
 x_531 = x_523;
 lean_ctor_set_tag(x_531, 1);
}
lean_ctor_set(x_531, 0, x_529);
lean_ctor_set(x_531, 1, x_530);
x_532 = lean_array_mk(x_531);
x_533 = l_Array_append___rarg(x_525, x_532);
lean_dec(x_532);
lean_inc(x_12);
x_534 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_534, 0, x_524);
lean_ctor_set(x_534, 1, x_12);
lean_ctor_set(x_534, 2, x_528);
if (lean_is_scalar(x_460)) {
 x_535 = lean_alloc_ctor(1, 1, 0);
} else {
 x_535 = x_460;
}
lean_ctor_set(x_535, 0, x_534);
x_14 = x_535;
x_15 = x_533;
goto block_147;
}
}
}
default: 
{
uint8_t x_781; 
lean_dec(x_460);
x_781 = !lean_is_exclusive(x_461);
if (x_781 == 0)
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_782 = lean_ctor_get(x_461, 1);
lean_dec(x_782);
x_783 = l_Lake_Dependency_decodeToml___closed__9;
lean_ctor_set_tag(x_461, 0);
lean_ctor_set(x_461, 1, x_783);
x_784 = lean_array_push(x_396, x_461);
x_785 = lean_box(0);
x_148 = x_785;
x_149 = x_784;
goto block_394;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_786 = lean_ctor_get(x_461, 0);
lean_inc(x_786);
lean_dec(x_461);
x_787 = l_Lake_Dependency_decodeToml___closed__9;
x_788 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
x_789 = lean_array_push(x_396, x_788);
x_790 = lean_box(0);
x_148 = x_790;
x_149 = x_789;
goto block_394;
}
}
}
}
}
else
{
uint8_t x_791; 
lean_dec(x_12);
x_791 = !lean_is_exclusive(x_395);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_886; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_792 = lean_ctor_get(x_395, 0);
x_793 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set(x_395, 0, x_793);
x_893 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_894 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_895 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_893, x_894, x_1);
if (lean_obj_tag(x_895) == 0)
{
lean_object* x_896; lean_object* x_897; lean_object* x_941; lean_object* x_942; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_948 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_949 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_893, x_948, x_1);
x_950 = lean_box(0);
if (lean_obj_tag(x_949) == 0)
{
x_896 = x_950;
x_897 = x_396;
goto block_940;
}
else
{
uint8_t x_957; 
x_957 = !lean_is_exclusive(x_949);
if (x_957 == 0)
{
lean_object* x_958; lean_object* x_959; 
x_958 = lean_ctor_get(x_949, 0);
x_959 = lean_ctor_get(x_958, 1);
lean_inc(x_959);
lean_dec(x_958);
switch (lean_obj_tag(x_959)) {
case 0:
{
lean_object* x_960; 
x_960 = lean_ctor_get(x_959, 1);
lean_inc(x_960);
lean_dec(x_959);
lean_ctor_set(x_949, 0, x_960);
x_941 = x_949;
x_942 = x_396;
goto block_947;
}
case 2:
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; 
lean_free_object(x_949);
x_961 = lean_ctor_get(x_959, 0);
lean_inc(x_961);
lean_dec(x_959);
x_962 = l_Lake_Glob_decodeToml___closed__2;
x_963 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_963, 0, x_961);
lean_ctor_set(x_963, 1, x_962);
x_951 = x_963;
goto block_956;
}
case 3:
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_free_object(x_949);
x_964 = lean_ctor_get(x_959, 0);
lean_inc(x_964);
lean_dec(x_959);
x_965 = l_Lake_Glob_decodeToml___closed__2;
x_966 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_966, 0, x_964);
lean_ctor_set(x_966, 1, x_965);
x_951 = x_966;
goto block_956;
}
default: 
{
uint8_t x_967; 
lean_free_object(x_949);
x_967 = !lean_is_exclusive(x_959);
if (x_967 == 0)
{
lean_object* x_968; lean_object* x_969; 
x_968 = lean_ctor_get(x_959, 1);
lean_dec(x_968);
x_969 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_959, 0);
lean_ctor_set(x_959, 1, x_969);
x_951 = x_959;
goto block_956;
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; 
x_970 = lean_ctor_get(x_959, 0);
lean_inc(x_970);
lean_dec(x_959);
x_971 = l_Lake_Glob_decodeToml___closed__2;
x_972 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_972, 0, x_970);
lean_ctor_set(x_972, 1, x_971);
x_951 = x_972;
goto block_956;
}
}
}
}
else
{
lean_object* x_973; lean_object* x_974; 
x_973 = lean_ctor_get(x_949, 0);
lean_inc(x_973);
lean_dec(x_949);
x_974 = lean_ctor_get(x_973, 1);
lean_inc(x_974);
lean_dec(x_973);
switch (lean_obj_tag(x_974)) {
case 0:
{
lean_object* x_975; lean_object* x_976; 
x_975 = lean_ctor_get(x_974, 1);
lean_inc(x_975);
lean_dec(x_974);
x_976 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_976, 0, x_975);
x_941 = x_976;
x_942 = x_396;
goto block_947;
}
case 2:
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; 
x_977 = lean_ctor_get(x_974, 0);
lean_inc(x_977);
lean_dec(x_974);
x_978 = l_Lake_Glob_decodeToml___closed__2;
x_979 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_979, 0, x_977);
lean_ctor_set(x_979, 1, x_978);
x_951 = x_979;
goto block_956;
}
case 3:
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_980 = lean_ctor_get(x_974, 0);
lean_inc(x_980);
lean_dec(x_974);
x_981 = l_Lake_Glob_decodeToml___closed__2;
x_982 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_982, 0, x_980);
lean_ctor_set(x_982, 1, x_981);
x_951 = x_982;
goto block_956;
}
default: 
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_983 = lean_ctor_get(x_974, 0);
lean_inc(x_983);
if (lean_is_exclusive(x_974)) {
 lean_ctor_release(x_974, 0);
 lean_ctor_release(x_974, 1);
 x_984 = x_974;
} else {
 lean_dec_ref(x_974);
 x_984 = lean_box(0);
}
x_985 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_984)) {
 x_986 = lean_alloc_ctor(0, 2, 0);
} else {
 x_986 = x_984;
 lean_ctor_set_tag(x_986, 0);
}
lean_ctor_set(x_986, 0, x_983);
lean_ctor_set(x_986, 1, x_985);
x_951 = x_986;
goto block_956;
}
}
}
}
block_940:
{
lean_object* x_898; lean_object* x_899; lean_object* x_907; lean_object* x_908; 
x_898 = lean_box(0);
x_907 = l_Lake_Dependency_decodeToml___closed__2;
x_908 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_893, x_907, x_1);
if (lean_obj_tag(x_908) == 0)
{
lean_object* x_909; lean_object* x_910; 
x_909 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_910 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_910, 0, x_11);
lean_ctor_set(x_910, 1, x_909);
lean_ctor_set(x_910, 2, x_896);
lean_ctor_set(x_910, 3, x_395);
lean_ctor_set(x_910, 4, x_898);
x_3 = x_910;
x_4 = x_897;
goto block_8;
}
else
{
lean_object* x_911; lean_object* x_912; 
x_911 = lean_ctor_get(x_908, 0);
lean_inc(x_911);
lean_dec(x_908);
x_912 = lean_ctor_get(x_911, 1);
lean_inc(x_912);
lean_dec(x_911);
switch (lean_obj_tag(x_912)) {
case 0:
{
uint8_t x_913; 
x_913 = !lean_is_exclusive(x_912);
if (x_913 == 0)
{
lean_object* x_914; lean_object* x_915; 
x_914 = lean_ctor_get(x_912, 1);
lean_dec(x_914);
x_915 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_912, 1, x_915);
x_899 = x_912;
goto block_906;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_912, 0);
lean_inc(x_916);
lean_dec(x_912);
x_917 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_918 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_917);
x_899 = x_918;
goto block_906;
}
}
case 2:
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; 
x_919 = lean_ctor_get(x_912, 0);
lean_inc(x_919);
lean_dec(x_912);
x_920 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_921 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_921, 0, x_919);
lean_ctor_set(x_921, 1, x_920);
x_899 = x_921;
goto block_906;
}
case 3:
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; 
x_922 = lean_ctor_get(x_912, 0);
lean_inc(x_922);
lean_dec(x_912);
x_923 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_924 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_924, 0, x_922);
lean_ctor_set(x_924, 1, x_923);
x_899 = x_924;
goto block_906;
}
case 6:
{
lean_object* x_925; lean_object* x_926; 
x_925 = lean_ctor_get(x_912, 1);
lean_inc(x_925);
lean_dec(x_912);
x_926 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_925);
lean_dec(x_925);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; 
x_927 = lean_ctor_get(x_926, 0);
lean_inc(x_927);
lean_dec(x_926);
x_928 = l_Array_append___rarg(x_897, x_927);
lean_dec(x_927);
x_929 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_930 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_930, 0, x_11);
lean_ctor_set(x_930, 1, x_929);
lean_ctor_set(x_930, 2, x_896);
lean_ctor_set(x_930, 3, x_395);
lean_ctor_set(x_930, 4, x_898);
x_3 = x_930;
x_4 = x_928;
goto block_8;
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; 
x_931 = lean_ctor_get(x_926, 0);
lean_inc(x_931);
lean_dec(x_926);
x_932 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_933 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_933, 0, x_11);
lean_ctor_set(x_933, 1, x_932);
lean_ctor_set(x_933, 2, x_896);
lean_ctor_set(x_933, 3, x_395);
lean_ctor_set(x_933, 4, x_931);
x_3 = x_933;
x_4 = x_897;
goto block_8;
}
}
default: 
{
uint8_t x_934; 
x_934 = !lean_is_exclusive(x_912);
if (x_934 == 0)
{
lean_object* x_935; lean_object* x_936; 
x_935 = lean_ctor_get(x_912, 1);
lean_dec(x_935);
x_936 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_912, 0);
lean_ctor_set(x_912, 1, x_936);
x_899 = x_912;
goto block_906;
}
else
{
lean_object* x_937; lean_object* x_938; lean_object* x_939; 
x_937 = lean_ctor_get(x_912, 0);
lean_inc(x_937);
lean_dec(x_912);
x_938 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_939 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_939, 0, x_937);
lean_ctor_set(x_939, 1, x_938);
x_899 = x_939;
goto block_906;
}
}
}
}
block_906:
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; 
x_900 = lean_box(0);
x_901 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_901, 0, x_899);
lean_ctor_set(x_901, 1, x_900);
x_902 = lean_array_mk(x_901);
x_903 = l_Array_append___rarg(x_897, x_902);
lean_dec(x_902);
x_904 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_905 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_905, 0, x_11);
lean_ctor_set(x_905, 1, x_904);
lean_ctor_set(x_905, 2, x_896);
lean_ctor_set(x_905, 3, x_395);
lean_ctor_set(x_905, 4, x_898);
x_3 = x_905;
x_4 = x_903;
goto block_8;
}
}
block_947:
{
if (lean_obj_tag(x_941) == 0)
{
lean_object* x_943; 
x_943 = lean_box(0);
x_896 = x_943;
x_897 = x_942;
goto block_940;
}
else
{
uint8_t x_944; 
x_944 = !lean_is_exclusive(x_941);
if (x_944 == 0)
{
x_896 = x_941;
x_897 = x_942;
goto block_940;
}
else
{
lean_object* x_945; lean_object* x_946; 
x_945 = lean_ctor_get(x_941, 0);
lean_inc(x_945);
lean_dec(x_941);
x_946 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_946, 0, x_945);
x_896 = x_946;
x_897 = x_942;
goto block_940;
}
}
}
block_956:
{
lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_952 = lean_box(0);
x_953 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_953, 0, x_951);
lean_ctor_set(x_953, 1, x_952);
x_954 = lean_array_mk(x_953);
x_955 = l_Array_append___rarg(x_396, x_954);
lean_dec(x_954);
x_941 = x_950;
x_942 = x_955;
goto block_947;
}
}
else
{
lean_object* x_987; lean_object* x_988; 
x_987 = lean_ctor_get(x_895, 0);
lean_inc(x_987);
lean_dec(x_895);
x_988 = lean_ctor_get(x_987, 1);
lean_inc(x_988);
lean_dec(x_987);
switch (lean_obj_tag(x_988)) {
case 0:
{
lean_object* x_989; 
x_989 = lean_ctor_get(x_988, 1);
lean_inc(x_989);
lean_dec(x_988);
x_794 = x_989;
x_795 = x_396;
goto block_885;
}
case 2:
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; 
x_990 = lean_ctor_get(x_988, 0);
lean_inc(x_990);
lean_dec(x_988);
x_991 = l_Lake_Glob_decodeToml___closed__2;
x_992 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_992, 0, x_990);
lean_ctor_set(x_992, 1, x_991);
x_886 = x_992;
goto block_892;
}
case 3:
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_993 = lean_ctor_get(x_988, 0);
lean_inc(x_993);
lean_dec(x_988);
x_994 = l_Lake_Glob_decodeToml___closed__2;
x_995 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_995, 0, x_993);
lean_ctor_set(x_995, 1, x_994);
x_886 = x_995;
goto block_892;
}
default: 
{
uint8_t x_996; 
x_996 = !lean_is_exclusive(x_988);
if (x_996 == 0)
{
lean_object* x_997; lean_object* x_998; 
x_997 = lean_ctor_get(x_988, 1);
lean_dec(x_997);
x_998 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_988, 0);
lean_ctor_set(x_988, 1, x_998);
x_886 = x_988;
goto block_892;
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_999 = lean_ctor_get(x_988, 0);
lean_inc(x_999);
lean_dec(x_988);
x_1000 = l_Lake_Glob_decodeToml___closed__2;
x_1001 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1001, 0, x_999);
lean_ctor_set(x_1001, 1, x_1000);
x_886 = x_1001;
goto block_892;
}
}
}
}
block_885:
{
lean_object* x_796; lean_object* x_797; lean_object* x_838; lean_object* x_839; lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; 
x_845 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_846 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_847 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_845, x_846, x_1);
x_848 = lean_box(0);
if (lean_obj_tag(x_847) == 0)
{
x_838 = x_848;
x_839 = x_795;
goto block_844;
}
else
{
uint8_t x_855; 
x_855 = !lean_is_exclusive(x_847);
if (x_855 == 0)
{
lean_object* x_856; lean_object* x_857; 
x_856 = lean_ctor_get(x_847, 0);
x_857 = lean_ctor_get(x_856, 1);
lean_inc(x_857);
lean_dec(x_856);
switch (lean_obj_tag(x_857)) {
case 0:
{
lean_object* x_858; 
x_858 = lean_ctor_get(x_857, 1);
lean_inc(x_858);
lean_dec(x_857);
lean_ctor_set(x_847, 0, x_858);
x_838 = x_847;
x_839 = x_795;
goto block_844;
}
case 2:
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; 
lean_free_object(x_847);
x_859 = lean_ctor_get(x_857, 0);
lean_inc(x_859);
lean_dec(x_857);
x_860 = l_Lake_Glob_decodeToml___closed__2;
x_861 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_861, 0, x_859);
lean_ctor_set(x_861, 1, x_860);
x_849 = x_861;
goto block_854;
}
case 3:
{
lean_object* x_862; lean_object* x_863; lean_object* x_864; 
lean_free_object(x_847);
x_862 = lean_ctor_get(x_857, 0);
lean_inc(x_862);
lean_dec(x_857);
x_863 = l_Lake_Glob_decodeToml___closed__2;
x_864 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_864, 0, x_862);
lean_ctor_set(x_864, 1, x_863);
x_849 = x_864;
goto block_854;
}
default: 
{
uint8_t x_865; 
lean_free_object(x_847);
x_865 = !lean_is_exclusive(x_857);
if (x_865 == 0)
{
lean_object* x_866; lean_object* x_867; 
x_866 = lean_ctor_get(x_857, 1);
lean_dec(x_866);
x_867 = l_Lake_Glob_decodeToml___closed__2;
lean_ctor_set_tag(x_857, 0);
lean_ctor_set(x_857, 1, x_867);
x_849 = x_857;
goto block_854;
}
else
{
lean_object* x_868; lean_object* x_869; lean_object* x_870; 
x_868 = lean_ctor_get(x_857, 0);
lean_inc(x_868);
lean_dec(x_857);
x_869 = l_Lake_Glob_decodeToml___closed__2;
x_870 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_870, 0, x_868);
lean_ctor_set(x_870, 1, x_869);
x_849 = x_870;
goto block_854;
}
}
}
}
else
{
lean_object* x_871; lean_object* x_872; 
x_871 = lean_ctor_get(x_847, 0);
lean_inc(x_871);
lean_dec(x_847);
x_872 = lean_ctor_get(x_871, 1);
lean_inc(x_872);
lean_dec(x_871);
switch (lean_obj_tag(x_872)) {
case 0:
{
lean_object* x_873; lean_object* x_874; 
x_873 = lean_ctor_get(x_872, 1);
lean_inc(x_873);
lean_dec(x_872);
x_874 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_874, 0, x_873);
x_838 = x_874;
x_839 = x_795;
goto block_844;
}
case 2:
{
lean_object* x_875; lean_object* x_876; lean_object* x_877; 
x_875 = lean_ctor_get(x_872, 0);
lean_inc(x_875);
lean_dec(x_872);
x_876 = l_Lake_Glob_decodeToml___closed__2;
x_877 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_877, 0, x_875);
lean_ctor_set(x_877, 1, x_876);
x_849 = x_877;
goto block_854;
}
case 3:
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_878 = lean_ctor_get(x_872, 0);
lean_inc(x_878);
lean_dec(x_872);
x_879 = l_Lake_Glob_decodeToml___closed__2;
x_880 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_880, 0, x_878);
lean_ctor_set(x_880, 1, x_879);
x_849 = x_880;
goto block_854;
}
default: 
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_881 = lean_ctor_get(x_872, 0);
lean_inc(x_881);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_882 = x_872;
} else {
 lean_dec_ref(x_872);
 x_882 = lean_box(0);
}
x_883 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_882)) {
 x_884 = lean_alloc_ctor(0, 2, 0);
} else {
 x_884 = x_882;
 lean_ctor_set_tag(x_884, 0);
}
lean_ctor_set(x_884, 0, x_881);
lean_ctor_set(x_884, 1, x_883);
x_849 = x_884;
goto block_854;
}
}
}
}
block_837:
{
lean_object* x_798; lean_object* x_799; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_798 = lean_box(0);
x_806 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_807 = l_Lake_Dependency_decodeToml___closed__2;
x_808 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_806, x_807, x_1);
if (lean_obj_tag(x_808) == 0)
{
lean_object* x_809; 
x_809 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_809, 0, x_11);
lean_ctor_set(x_809, 1, x_794);
lean_ctor_set(x_809, 2, x_796);
lean_ctor_set(x_809, 3, x_395);
lean_ctor_set(x_809, 4, x_798);
x_3 = x_809;
x_4 = x_797;
goto block_8;
}
else
{
lean_object* x_810; lean_object* x_811; 
x_810 = lean_ctor_get(x_808, 0);
lean_inc(x_810);
lean_dec(x_808);
x_811 = lean_ctor_get(x_810, 1);
lean_inc(x_811);
lean_dec(x_810);
switch (lean_obj_tag(x_811)) {
case 0:
{
uint8_t x_812; 
x_812 = !lean_is_exclusive(x_811);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; 
x_813 = lean_ctor_get(x_811, 1);
lean_dec(x_813);
x_814 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_811, 1, x_814);
x_799 = x_811;
goto block_805;
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_815 = lean_ctor_get(x_811, 0);
lean_inc(x_815);
lean_dec(x_811);
x_816 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_817 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_817, 0, x_815);
lean_ctor_set(x_817, 1, x_816);
x_799 = x_817;
goto block_805;
}
}
case 2:
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; 
x_818 = lean_ctor_get(x_811, 0);
lean_inc(x_818);
lean_dec(x_811);
x_819 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_820 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_820, 0, x_818);
lean_ctor_set(x_820, 1, x_819);
x_799 = x_820;
goto block_805;
}
case 3:
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; 
x_821 = lean_ctor_get(x_811, 0);
lean_inc(x_821);
lean_dec(x_811);
x_822 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_823 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_823, 0, x_821);
lean_ctor_set(x_823, 1, x_822);
x_799 = x_823;
goto block_805;
}
case 6:
{
lean_object* x_824; lean_object* x_825; 
x_824 = lean_ctor_get(x_811, 1);
lean_inc(x_824);
lean_dec(x_811);
x_825 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_824);
lean_dec(x_824);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
lean_dec(x_825);
x_827 = l_Array_append___rarg(x_797, x_826);
lean_dec(x_826);
x_828 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_828, 0, x_11);
lean_ctor_set(x_828, 1, x_794);
lean_ctor_set(x_828, 2, x_796);
lean_ctor_set(x_828, 3, x_395);
lean_ctor_set(x_828, 4, x_798);
x_3 = x_828;
x_4 = x_827;
goto block_8;
}
else
{
lean_object* x_829; lean_object* x_830; 
x_829 = lean_ctor_get(x_825, 0);
lean_inc(x_829);
lean_dec(x_825);
x_830 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_830, 0, x_11);
lean_ctor_set(x_830, 1, x_794);
lean_ctor_set(x_830, 2, x_796);
lean_ctor_set(x_830, 3, x_395);
lean_ctor_set(x_830, 4, x_829);
x_3 = x_830;
x_4 = x_797;
goto block_8;
}
}
default: 
{
uint8_t x_831; 
x_831 = !lean_is_exclusive(x_811);
if (x_831 == 0)
{
lean_object* x_832; lean_object* x_833; 
x_832 = lean_ctor_get(x_811, 1);
lean_dec(x_832);
x_833 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_811, 0);
lean_ctor_set(x_811, 1, x_833);
x_799 = x_811;
goto block_805;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_834 = lean_ctor_get(x_811, 0);
lean_inc(x_834);
lean_dec(x_811);
x_835 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_836 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_836, 0, x_834);
lean_ctor_set(x_836, 1, x_835);
x_799 = x_836;
goto block_805;
}
}
}
}
block_805:
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_800 = lean_box(0);
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
x_802 = lean_array_mk(x_801);
x_803 = l_Array_append___rarg(x_797, x_802);
lean_dec(x_802);
x_804 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_804, 0, x_11);
lean_ctor_set(x_804, 1, x_794);
lean_ctor_set(x_804, 2, x_796);
lean_ctor_set(x_804, 3, x_395);
lean_ctor_set(x_804, 4, x_798);
x_3 = x_804;
x_4 = x_803;
goto block_8;
}
}
block_844:
{
if (lean_obj_tag(x_838) == 0)
{
lean_object* x_840; 
x_840 = lean_box(0);
x_796 = x_840;
x_797 = x_839;
goto block_837;
}
else
{
uint8_t x_841; 
x_841 = !lean_is_exclusive(x_838);
if (x_841 == 0)
{
x_796 = x_838;
x_797 = x_839;
goto block_837;
}
else
{
lean_object* x_842; lean_object* x_843; 
x_842 = lean_ctor_get(x_838, 0);
lean_inc(x_842);
lean_dec(x_838);
x_843 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_843, 0, x_842);
x_796 = x_843;
x_797 = x_839;
goto block_837;
}
}
}
block_854:
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_850 = lean_box(0);
x_851 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_851, 0, x_849);
lean_ctor_set(x_851, 1, x_850);
x_852 = lean_array_mk(x_851);
x_853 = l_Array_append___rarg(x_795, x_852);
lean_dec(x_852);
x_838 = x_848;
x_839 = x_853;
goto block_844;
}
}
block_892:
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_887 = lean_box(0);
x_888 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_888, 0, x_886);
lean_ctor_set(x_888, 1, x_887);
x_889 = lean_array_mk(x_888);
x_890 = l_Array_append___rarg(x_396, x_889);
lean_dec(x_889);
x_891 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_794 = x_891;
x_795 = x_890;
goto block_885;
}
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1078; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1002 = lean_ctor_get(x_395, 0);
lean_inc(x_1002);
lean_dec(x_395);
x_1003 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1003, 0, x_1002);
x_1004 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1004, 0, x_1003);
x_1085 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_1086 = l_Lake_Dependency_decodeToml___closed__5;
lean_inc(x_1);
x_1087 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1085, x_1086, x_1);
if (lean_obj_tag(x_1087) == 0)
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1129; lean_object* x_1130; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; 
x_1136 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_1137 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1085, x_1136, x_1);
x_1138 = lean_box(0);
if (lean_obj_tag(x_1137) == 0)
{
x_1088 = x_1138;
x_1089 = x_396;
goto block_1128;
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1145 = lean_ctor_get(x_1137, 0);
lean_inc(x_1145);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 x_1146 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1146 = lean_box(0);
}
x_1147 = lean_ctor_get(x_1145, 1);
lean_inc(x_1147);
lean_dec(x_1145);
switch (lean_obj_tag(x_1147)) {
case 0:
{
lean_object* x_1148; lean_object* x_1149; 
x_1148 = lean_ctor_get(x_1147, 1);
lean_inc(x_1148);
lean_dec(x_1147);
if (lean_is_scalar(x_1146)) {
 x_1149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1149 = x_1146;
}
lean_ctor_set(x_1149, 0, x_1148);
x_1129 = x_1149;
x_1130 = x_396;
goto block_1135;
}
case 2:
{
lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; 
lean_dec(x_1146);
x_1150 = lean_ctor_get(x_1147, 0);
lean_inc(x_1150);
lean_dec(x_1147);
x_1151 = l_Lake_Glob_decodeToml___closed__2;
x_1152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1152, 0, x_1150);
lean_ctor_set(x_1152, 1, x_1151);
x_1139 = x_1152;
goto block_1144;
}
case 3:
{
lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
lean_dec(x_1146);
x_1153 = lean_ctor_get(x_1147, 0);
lean_inc(x_1153);
lean_dec(x_1147);
x_1154 = l_Lake_Glob_decodeToml___closed__2;
x_1155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1155, 0, x_1153);
lean_ctor_set(x_1155, 1, x_1154);
x_1139 = x_1155;
goto block_1144;
}
default: 
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
lean_dec(x_1146);
x_1156 = lean_ctor_get(x_1147, 0);
lean_inc(x_1156);
if (lean_is_exclusive(x_1147)) {
 lean_ctor_release(x_1147, 0);
 lean_ctor_release(x_1147, 1);
 x_1157 = x_1147;
} else {
 lean_dec_ref(x_1147);
 x_1157 = lean_box(0);
}
x_1158 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_1157)) {
 x_1159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1159 = x_1157;
 lean_ctor_set_tag(x_1159, 0);
}
lean_ctor_set(x_1159, 0, x_1156);
lean_ctor_set(x_1159, 1, x_1158);
x_1139 = x_1159;
goto block_1144;
}
}
}
block_1128:
{
lean_object* x_1090; lean_object* x_1091; lean_object* x_1099; lean_object* x_1100; 
x_1090 = lean_box(0);
x_1099 = l_Lake_Dependency_decodeToml___closed__2;
x_1100 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1085, x_1099, x_1);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; 
x_1101 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1102 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1102, 0, x_11);
lean_ctor_set(x_1102, 1, x_1101);
lean_ctor_set(x_1102, 2, x_1088);
lean_ctor_set(x_1102, 3, x_1004);
lean_ctor_set(x_1102, 4, x_1090);
x_3 = x_1102;
x_4 = x_1089;
goto block_8;
}
else
{
lean_object* x_1103; lean_object* x_1104; 
x_1103 = lean_ctor_get(x_1100, 0);
lean_inc(x_1103);
lean_dec(x_1100);
x_1104 = lean_ctor_get(x_1103, 1);
lean_inc(x_1104);
lean_dec(x_1103);
switch (lean_obj_tag(x_1104)) {
case 0:
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 x_1106 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1106 = lean_box(0);
}
x_1107 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
if (lean_is_scalar(x_1106)) {
 x_1108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1108 = x_1106;
}
lean_ctor_set(x_1108, 0, x_1105);
lean_ctor_set(x_1108, 1, x_1107);
x_1091 = x_1108;
goto block_1098;
}
case 2:
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
x_1109 = lean_ctor_get(x_1104, 0);
lean_inc(x_1109);
lean_dec(x_1104);
x_1110 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1111, 0, x_1109);
lean_ctor_set(x_1111, 1, x_1110);
x_1091 = x_1111;
goto block_1098;
}
case 3:
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1112 = lean_ctor_get(x_1104, 0);
lean_inc(x_1112);
lean_dec(x_1104);
x_1113 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1114, 0, x_1112);
lean_ctor_set(x_1114, 1, x_1113);
x_1091 = x_1114;
goto block_1098;
}
case 6:
{
lean_object* x_1115; lean_object* x_1116; 
x_1115 = lean_ctor_get(x_1104, 1);
lean_inc(x_1115);
lean_dec(x_1104);
x_1116 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_1115);
lean_dec(x_1115);
if (lean_obj_tag(x_1116) == 0)
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc(x_1117);
lean_dec(x_1116);
x_1118 = l_Array_append___rarg(x_1089, x_1117);
lean_dec(x_1117);
x_1119 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1120 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1120, 0, x_11);
lean_ctor_set(x_1120, 1, x_1119);
lean_ctor_set(x_1120, 2, x_1088);
lean_ctor_set(x_1120, 3, x_1004);
lean_ctor_set(x_1120, 4, x_1090);
x_3 = x_1120;
x_4 = x_1118;
goto block_8;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1116, 0);
lean_inc(x_1121);
lean_dec(x_1116);
x_1122 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1123 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1123, 0, x_11);
lean_ctor_set(x_1123, 1, x_1122);
lean_ctor_set(x_1123, 2, x_1088);
lean_ctor_set(x_1123, 3, x_1004);
lean_ctor_set(x_1123, 4, x_1121);
x_3 = x_1123;
x_4 = x_1089;
goto block_8;
}
}
default: 
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1124 = lean_ctor_get(x_1104, 0);
lean_inc(x_1124);
if (lean_is_exclusive(x_1104)) {
 lean_ctor_release(x_1104, 0);
 lean_ctor_release(x_1104, 1);
 x_1125 = x_1104;
} else {
 lean_dec_ref(x_1104);
 x_1125 = lean_box(0);
}
x_1126 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
if (lean_is_scalar(x_1125)) {
 x_1127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1127 = x_1125;
 lean_ctor_set_tag(x_1127, 0);
}
lean_ctor_set(x_1127, 0, x_1124);
lean_ctor_set(x_1127, 1, x_1126);
x_1091 = x_1127;
goto block_1098;
}
}
}
block_1098:
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1092 = lean_box(0);
x_1093 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1093, 0, x_1091);
lean_ctor_set(x_1093, 1, x_1092);
x_1094 = lean_array_mk(x_1093);
x_1095 = l_Array_append___rarg(x_1089, x_1094);
lean_dec(x_1094);
x_1096 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1097 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1097, 0, x_11);
lean_ctor_set(x_1097, 1, x_1096);
lean_ctor_set(x_1097, 2, x_1088);
lean_ctor_set(x_1097, 3, x_1004);
lean_ctor_set(x_1097, 4, x_1090);
x_3 = x_1097;
x_4 = x_1095;
goto block_8;
}
}
block_1135:
{
if (lean_obj_tag(x_1129) == 0)
{
lean_object* x_1131; 
x_1131 = lean_box(0);
x_1088 = x_1131;
x_1089 = x_1130;
goto block_1128;
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
x_1132 = lean_ctor_get(x_1129, 0);
lean_inc(x_1132);
if (lean_is_exclusive(x_1129)) {
 lean_ctor_release(x_1129, 0);
 x_1133 = x_1129;
} else {
 lean_dec_ref(x_1129);
 x_1133 = lean_box(0);
}
if (lean_is_scalar(x_1133)) {
 x_1134 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1134 = x_1133;
}
lean_ctor_set(x_1134, 0, x_1132);
x_1088 = x_1134;
x_1089 = x_1130;
goto block_1128;
}
}
block_1144:
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1140 = lean_box(0);
x_1141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1141, 0, x_1139);
lean_ctor_set(x_1141, 1, x_1140);
x_1142 = lean_array_mk(x_1141);
x_1143 = l_Array_append___rarg(x_396, x_1142);
lean_dec(x_1142);
x_1129 = x_1138;
x_1130 = x_1143;
goto block_1135;
}
}
else
{
lean_object* x_1160; lean_object* x_1161; 
x_1160 = lean_ctor_get(x_1087, 0);
lean_inc(x_1160);
lean_dec(x_1087);
x_1161 = lean_ctor_get(x_1160, 1);
lean_inc(x_1161);
lean_dec(x_1160);
switch (lean_obj_tag(x_1161)) {
case 0:
{
lean_object* x_1162; 
x_1162 = lean_ctor_get(x_1161, 1);
lean_inc(x_1162);
lean_dec(x_1161);
x_1005 = x_1162;
x_1006 = x_396;
goto block_1077;
}
case 2:
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
x_1163 = lean_ctor_get(x_1161, 0);
lean_inc(x_1163);
lean_dec(x_1161);
x_1164 = l_Lake_Glob_decodeToml___closed__2;
x_1165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1165, 0, x_1163);
lean_ctor_set(x_1165, 1, x_1164);
x_1078 = x_1165;
goto block_1084;
}
case 3:
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1166 = lean_ctor_get(x_1161, 0);
lean_inc(x_1166);
lean_dec(x_1161);
x_1167 = l_Lake_Glob_decodeToml___closed__2;
x_1168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1168, 0, x_1166);
lean_ctor_set(x_1168, 1, x_1167);
x_1078 = x_1168;
goto block_1084;
}
default: 
{
lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1169 = lean_ctor_get(x_1161, 0);
lean_inc(x_1169);
if (lean_is_exclusive(x_1161)) {
 lean_ctor_release(x_1161, 0);
 lean_ctor_release(x_1161, 1);
 x_1170 = x_1161;
} else {
 lean_dec_ref(x_1161);
 x_1170 = lean_box(0);
}
x_1171 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_1170)) {
 x_1172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1172 = x_1170;
 lean_ctor_set_tag(x_1172, 0);
}
lean_ctor_set(x_1172, 0, x_1169);
lean_ctor_set(x_1172, 1, x_1171);
x_1078 = x_1172;
goto block_1084;
}
}
}
block_1077:
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1045; lean_object* x_1046; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; 
x_1052 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_1053 = l_Lake_PackageConfig_decodeToml___closed__29;
lean_inc(x_1);
x_1054 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1052, x_1053, x_1);
x_1055 = lean_box(0);
if (lean_obj_tag(x_1054) == 0)
{
x_1045 = x_1055;
x_1046 = x_1006;
goto block_1051;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1062 = lean_ctor_get(x_1054, 0);
lean_inc(x_1062);
if (lean_is_exclusive(x_1054)) {
 lean_ctor_release(x_1054, 0);
 x_1063 = x_1054;
} else {
 lean_dec_ref(x_1054);
 x_1063 = lean_box(0);
}
x_1064 = lean_ctor_get(x_1062, 1);
lean_inc(x_1064);
lean_dec(x_1062);
switch (lean_obj_tag(x_1064)) {
case 0:
{
lean_object* x_1065; lean_object* x_1066; 
x_1065 = lean_ctor_get(x_1064, 1);
lean_inc(x_1065);
lean_dec(x_1064);
if (lean_is_scalar(x_1063)) {
 x_1066 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1066 = x_1063;
}
lean_ctor_set(x_1066, 0, x_1065);
x_1045 = x_1066;
x_1046 = x_1006;
goto block_1051;
}
case 2:
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
lean_dec(x_1063);
x_1067 = lean_ctor_get(x_1064, 0);
lean_inc(x_1067);
lean_dec(x_1064);
x_1068 = l_Lake_Glob_decodeToml___closed__2;
x_1069 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1069, 0, x_1067);
lean_ctor_set(x_1069, 1, x_1068);
x_1056 = x_1069;
goto block_1061;
}
case 3:
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; 
lean_dec(x_1063);
x_1070 = lean_ctor_get(x_1064, 0);
lean_inc(x_1070);
lean_dec(x_1064);
x_1071 = l_Lake_Glob_decodeToml___closed__2;
x_1072 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1072, 0, x_1070);
lean_ctor_set(x_1072, 1, x_1071);
x_1056 = x_1072;
goto block_1061;
}
default: 
{
lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
lean_dec(x_1063);
x_1073 = lean_ctor_get(x_1064, 0);
lean_inc(x_1073);
if (lean_is_exclusive(x_1064)) {
 lean_ctor_release(x_1064, 0);
 lean_ctor_release(x_1064, 1);
 x_1074 = x_1064;
} else {
 lean_dec_ref(x_1064);
 x_1074 = lean_box(0);
}
x_1075 = l_Lake_Glob_decodeToml___closed__2;
if (lean_is_scalar(x_1074)) {
 x_1076 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1076 = x_1074;
 lean_ctor_set_tag(x_1076, 0);
}
lean_ctor_set(x_1076, 0, x_1073);
lean_ctor_set(x_1076, 1, x_1075);
x_1056 = x_1076;
goto block_1061;
}
}
}
block_1044:
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1009 = lean_box(0);
x_1017 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_1018 = l_Lake_Dependency_decodeToml___closed__2;
x_1019 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_1017, x_1018, x_1);
if (lean_obj_tag(x_1019) == 0)
{
lean_object* x_1020; 
x_1020 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1020, 0, x_11);
lean_ctor_set(x_1020, 1, x_1005);
lean_ctor_set(x_1020, 2, x_1007);
lean_ctor_set(x_1020, 3, x_1004);
lean_ctor_set(x_1020, 4, x_1009);
x_3 = x_1020;
x_4 = x_1008;
goto block_8;
}
else
{
lean_object* x_1021; lean_object* x_1022; 
x_1021 = lean_ctor_get(x_1019, 0);
lean_inc(x_1021);
lean_dec(x_1019);
x_1022 = lean_ctor_get(x_1021, 1);
lean_inc(x_1022);
lean_dec(x_1021);
switch (lean_obj_tag(x_1022)) {
case 0:
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1023 = lean_ctor_get(x_1022, 0);
lean_inc(x_1023);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1024 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1024 = lean_box(0);
}
x_1025 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
if (lean_is_scalar(x_1024)) {
 x_1026 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1026 = x_1024;
}
lean_ctor_set(x_1026, 0, x_1023);
lean_ctor_set(x_1026, 1, x_1025);
x_1010 = x_1026;
goto block_1016;
}
case 2:
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; 
x_1027 = lean_ctor_get(x_1022, 0);
lean_inc(x_1027);
lean_dec(x_1022);
x_1028 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1029 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1029, 0, x_1027);
lean_ctor_set(x_1029, 1, x_1028);
x_1010 = x_1029;
goto block_1016;
}
case 3:
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_1022, 0);
lean_inc(x_1030);
lean_dec(x_1022);
x_1031 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_1032 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1032, 0, x_1030);
lean_ctor_set(x_1032, 1, x_1031);
x_1010 = x_1032;
goto block_1016;
}
case 6:
{
lean_object* x_1033; lean_object* x_1034; 
x_1033 = lean_ctor_get(x_1022, 1);
lean_inc(x_1033);
lean_dec(x_1022);
x_1034 = l_Lake_Toml_Table_decodeNameMap___at_Lake_Dependency_decodeToml___spec__1(x_1033);
lean_dec(x_1033);
if (lean_obj_tag(x_1034) == 0)
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
x_1035 = lean_ctor_get(x_1034, 0);
lean_inc(x_1035);
lean_dec(x_1034);
x_1036 = l_Array_append___rarg(x_1008, x_1035);
lean_dec(x_1035);
x_1037 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1037, 0, x_11);
lean_ctor_set(x_1037, 1, x_1005);
lean_ctor_set(x_1037, 2, x_1007);
lean_ctor_set(x_1037, 3, x_1004);
lean_ctor_set(x_1037, 4, x_1009);
x_3 = x_1037;
x_4 = x_1036;
goto block_8;
}
else
{
lean_object* x_1038; lean_object* x_1039; 
x_1038 = lean_ctor_get(x_1034, 0);
lean_inc(x_1038);
lean_dec(x_1034);
x_1039 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1039, 0, x_11);
lean_ctor_set(x_1039, 1, x_1005);
lean_ctor_set(x_1039, 2, x_1007);
lean_ctor_set(x_1039, 3, x_1004);
lean_ctor_set(x_1039, 4, x_1038);
x_3 = x_1039;
x_4 = x_1008;
goto block_8;
}
}
default: 
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; 
x_1040 = lean_ctor_get(x_1022, 0);
lean_inc(x_1040);
if (lean_is_exclusive(x_1022)) {
 lean_ctor_release(x_1022, 0);
 lean_ctor_release(x_1022, 1);
 x_1041 = x_1022;
} else {
 lean_dec_ref(x_1022);
 x_1041 = lean_box(0);
}
x_1042 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
if (lean_is_scalar(x_1041)) {
 x_1043 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1043 = x_1041;
 lean_ctor_set_tag(x_1043, 0);
}
lean_ctor_set(x_1043, 0, x_1040);
lean_ctor_set(x_1043, 1, x_1042);
x_1010 = x_1043;
goto block_1016;
}
}
}
block_1016:
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1011 = lean_box(0);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
x_1013 = lean_array_mk(x_1012);
x_1014 = l_Array_append___rarg(x_1008, x_1013);
lean_dec(x_1013);
x_1015 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_1015, 0, x_11);
lean_ctor_set(x_1015, 1, x_1005);
lean_ctor_set(x_1015, 2, x_1007);
lean_ctor_set(x_1015, 3, x_1004);
lean_ctor_set(x_1015, 4, x_1009);
x_3 = x_1015;
x_4 = x_1014;
goto block_8;
}
}
block_1051:
{
if (lean_obj_tag(x_1045) == 0)
{
lean_object* x_1047; 
x_1047 = lean_box(0);
x_1007 = x_1047;
x_1008 = x_1046;
goto block_1044;
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; 
x_1048 = lean_ctor_get(x_1045, 0);
lean_inc(x_1048);
if (lean_is_exclusive(x_1045)) {
 lean_ctor_release(x_1045, 0);
 x_1049 = x_1045;
} else {
 lean_dec_ref(x_1045);
 x_1049 = lean_box(0);
}
if (lean_is_scalar(x_1049)) {
 x_1050 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1050 = x_1049;
}
lean_ctor_set(x_1050, 0, x_1048);
x_1007 = x_1050;
x_1008 = x_1046;
goto block_1044;
}
}
block_1061:
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1057 = lean_box(0);
x_1058 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1058, 0, x_1056);
lean_ctor_set(x_1058, 1, x_1057);
x_1059 = lean_array_mk(x_1058);
x_1060 = l_Array_append___rarg(x_1006, x_1059);
lean_dec(x_1059);
x_1045 = x_1055;
x_1046 = x_1060;
goto block_1051;
}
}
block_1084:
{
lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1079 = lean_box(0);
x_1080 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1080, 0, x_1078);
lean_ctor_set(x_1080, 1, x_1079);
x_1081 = lean_array_mk(x_1080);
x_1082 = l_Array_append___rarg(x_396, x_1081);
lean_dec(x_1081);
x_1083 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_1005 = x_1083;
x_1006 = x_1082;
goto block_1077;
}
}
}
}
block_1183:
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1179 = lean_box(0);
x_1180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1180, 0, x_1178);
lean_ctor_set(x_1180, 1, x_1179);
x_1181 = lean_array_mk(x_1180);
x_1182 = l_Array_append___rarg(x_13, x_1181);
lean_dec(x_1181);
x_395 = x_1177;
x_396 = x_1182;
goto block_1173;
}
}
block_1610:
{
lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; 
x_1606 = lean_box(0);
x_1607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1607, 0, x_1605);
lean_ctor_set(x_1607, 1, x_1606);
x_1608 = lean_array_mk(x_1607);
x_1609 = l_Array_append___rarg(x_10, x_1608);
lean_dec(x_1608);
x_12 = x_1604;
x_13 = x_1609;
goto block_1600;
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
LEAN_EXPORT lean_object* l_Lake_instDecodeTomlDependency___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_1, 1, x_10);
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_2 = x_13;
goto block_7;
}
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_2 = x_16;
goto block_7;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_2 = x_19;
goto block_7;
}
case 6:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = l_Lake_Dependency_decodeToml(x_21, x_20);
return x_22;
}
default: 
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 1);
lean_dec(x_24);
x_25 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_25);
x_2 = x_1;
goto block_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_2 = x_28;
goto block_7;
}
}
}
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_mk(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lake_instDecodeTomlDependency___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instDecodeTomlDependency___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instDecodeTomlDependency() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instDecodeTomlDependency___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_RBNode_dFind___at_Lake_decodeTargetDecls_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_ctor_get(x_2, 3);
x_9 = l_Lean_Name_quickCmp(x_3, x_6);
switch (x_9) {
case 0:
{
x_2 = x_5;
goto _start;
}
case 1:
{
lean_object* x_11; 
lean_inc(x_7);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
default: 
{
x_2 = x_8;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = 0;
x_7 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = l_Lean_Name_quickCmp(x_3, x_11);
switch (x_14) {
case 0:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_10, x_3, x_4);
x_16 = 0;
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_16);
return x_2;
}
case 1:
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = 0;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_17);
return x_2;
}
default: 
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_13, x_3, x_4);
x_19 = 0;
lean_ctor_set(x_2, 3, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_24 = l_Lean_Name_quickCmp(x_3, x_21);
switch (x_24) {
case 0:
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_20, x_3, x_4);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
case 1:
{
uint8_t x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_4);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
default: 
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_23, x_3, x_4);
x_31 = 0;
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = l_Lean_Name_quickCmp(x_3, x_35);
switch (x_38) {
case 0:
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_34, x_3, x_4);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*4);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_39, 3);
lean_dec(x_44);
x_45 = lean_ctor_get(x_39, 0);
lean_dec(x_45);
lean_ctor_set(x_39, 0, x_42);
x_46 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_46);
return x_2;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_39, 1);
x_48 = lean_ctor_get(x_39, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_42);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_40);
x_50 = 1;
lean_ctor_set(x_2, 0, x_49);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_50);
return x_2;
}
}
else
{
uint8_t x_51; 
x_51 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_39, 1);
x_54 = lean_ctor_get(x_39, 2);
x_55 = lean_ctor_get(x_39, 3);
lean_dec(x_55);
x_56 = lean_ctor_get(x_39, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
x_60 = lean_ctor_get(x_42, 2);
x_61 = lean_ctor_get(x_42, 3);
x_62 = 1;
lean_ctor_set(x_42, 3, x_58);
lean_ctor_set(x_42, 2, x_54);
lean_ctor_set(x_42, 1, x_53);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_62);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_61);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_62);
x_63 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_60);
lean_ctor_set(x_2, 1, x_59);
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_63);
return x_2;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_42, 0);
x_65 = lean_ctor_get(x_42, 1);
x_66 = lean_ctor_get(x_42, 2);
x_67 = lean_ctor_get(x_42, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_42);
x_68 = 1;
x_69 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_69, 0, x_41);
lean_ctor_set(x_69, 1, x_53);
lean_ctor_set(x_69, 2, x_54);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_68);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_67);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_68);
x_70 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_66);
lean_ctor_set(x_2, 1, x_65);
lean_ctor_set(x_2, 0, x_69);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_70);
return x_2;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_71 = lean_ctor_get(x_39, 1);
x_72 = lean_ctor_get(x_39, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_39);
x_73 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_42, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_42, 3);
lean_inc(x_76);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_77 = x_42;
} else {
 lean_dec_ref(x_42);
 x_77 = lean_box(0);
}
x_78 = 1;
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(1, 4, 1);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_72);
lean_ctor_set(x_79, 3, x_73);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_78);
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_35);
lean_ctor_set(x_80, 2, x_36);
lean_ctor_set(x_80, 3, x_37);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_78);
x_81 = 0;
lean_ctor_set(x_2, 3, x_80);
lean_ctor_set(x_2, 2, x_75);
lean_ctor_set(x_2, 1, x_74);
lean_ctor_set(x_2, 0, x_79);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_81);
return x_2;
}
}
else
{
uint8_t x_82; 
lean_free_object(x_2);
x_82 = !lean_is_exclusive(x_42);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_42, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_42, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_42, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_42, 0);
lean_dec(x_86);
x_87 = 1;
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_87);
return x_42;
}
else
{
uint8_t x_88; lean_object* x_89; 
lean_dec(x_42);
x_88 = 1;
x_89 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_89, 0, x_39);
lean_ctor_set(x_89, 1, x_35);
lean_ctor_set(x_89, 2, x_36);
lean_ctor_set(x_89, 3, x_37);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_39);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_39, 1);
x_93 = lean_ctor_get(x_39, 2);
x_94 = lean_ctor_get(x_39, 3);
x_95 = lean_ctor_get(x_39, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
uint8_t x_97; uint8_t x_98; 
x_97 = 1;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_97);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_94);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_97);
x_98 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_93);
lean_ctor_set(x_2, 1, x_92);
lean_ctor_set(x_2, 0, x_41);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_98);
return x_2;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; uint8_t x_105; 
x_99 = lean_ctor_get(x_41, 0);
x_100 = lean_ctor_get(x_41, 1);
x_101 = lean_ctor_get(x_41, 2);
x_102 = lean_ctor_get(x_41, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_41);
x_103 = 1;
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_100);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_94);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_103);
x_105 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_93);
lean_ctor_set(x_2, 1, x_92);
lean_ctor_set(x_2, 0, x_104);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_105);
return x_2;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_106 = lean_ctor_get(x_39, 1);
x_107 = lean_ctor_get(x_39, 2);
x_108 = lean_ctor_get(x_39, 3);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_39);
x_109 = lean_ctor_get(x_41, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_41, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_41, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_41, 3);
lean_inc(x_112);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_113 = x_41;
} else {
 lean_dec_ref(x_41);
 x_113 = lean_box(0);
}
x_114 = 1;
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(1, 4, 1);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_110);
lean_ctor_set(x_115, 2, x_111);
lean_ctor_set(x_115, 3, x_112);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_114);
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_108);
lean_ctor_set(x_116, 1, x_35);
lean_ctor_set(x_116, 2, x_36);
lean_ctor_set(x_116, 3, x_37);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_114);
x_117 = 0;
lean_ctor_set(x_2, 3, x_116);
lean_ctor_set(x_2, 2, x_107);
lean_ctor_set(x_2, 1, x_106);
lean_ctor_set(x_2, 0, x_115);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_117);
return x_2;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_39, 3);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
lean_free_object(x_2);
x_119 = !lean_is_exclusive(x_41);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_41, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_41, 2);
lean_dec(x_121);
x_122 = lean_ctor_get(x_41, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_41, 0);
lean_dec(x_123);
x_124 = 1;
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_124);
return x_41;
}
else
{
uint8_t x_125; lean_object* x_126; 
lean_dec(x_41);
x_125 = 1;
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_39);
lean_ctor_set(x_126, 1, x_35);
lean_ctor_set(x_126, 2, x_36);
lean_ctor_set(x_126, 3, x_37);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
if (x_127 == 0)
{
uint8_t x_128; 
lean_free_object(x_2);
x_128 = !lean_is_exclusive(x_39);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_39, 1);
x_130 = lean_ctor_get(x_39, 2);
x_131 = lean_ctor_get(x_39, 3);
lean_dec(x_131);
x_132 = lean_ctor_get(x_39, 0);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_118);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_118, 0);
x_135 = lean_ctor_get(x_118, 1);
x_136 = lean_ctor_get(x_118, 2);
x_137 = lean_ctor_get(x_118, 3);
x_138 = 1;
lean_inc(x_41);
lean_ctor_set(x_118, 3, x_134);
lean_ctor_set(x_118, 2, x_130);
lean_ctor_set(x_118, 1, x_129);
lean_ctor_set(x_118, 0, x_41);
x_139 = !lean_is_exclusive(x_41);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_ctor_get(x_41, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_41, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_41, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_41, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_138);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 0, x_137);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_138);
x_144 = 0;
lean_ctor_set(x_39, 3, x_41);
lean_ctor_set(x_39, 2, x_136);
lean_ctor_set(x_39, 1, x_135);
lean_ctor_set(x_39, 0, x_118);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_144);
return x_39;
}
else
{
lean_object* x_145; uint8_t x_146; 
lean_dec(x_41);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_138);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_137);
lean_ctor_set(x_145, 1, x_35);
lean_ctor_set(x_145, 2, x_36);
lean_ctor_set(x_145, 3, x_37);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_138);
x_146 = 0;
lean_ctor_set(x_39, 3, x_145);
lean_ctor_set(x_39, 2, x_136);
lean_ctor_set(x_39, 1, x_135);
lean_ctor_set(x_39, 0, x_118);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_146);
return x_39;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_147 = lean_ctor_get(x_118, 0);
x_148 = lean_ctor_get(x_118, 1);
x_149 = lean_ctor_get(x_118, 2);
x_150 = lean_ctor_get(x_118, 3);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_118);
x_151 = 1;
lean_inc(x_41);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_41);
lean_ctor_set(x_152, 1, x_129);
lean_ctor_set(x_152, 2, x_130);
lean_ctor_set(x_152, 3, x_147);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_153 = x_41;
} else {
 lean_dec_ref(x_41);
 x_153 = lean_box(0);
}
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_151);
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 4, 1);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_35);
lean_ctor_set(x_154, 2, x_36);
lean_ctor_set(x_154, 3, x_37);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_151);
x_155 = 0;
lean_ctor_set(x_39, 3, x_154);
lean_ctor_set(x_39, 2, x_149);
lean_ctor_set(x_39, 1, x_148);
lean_ctor_set(x_39, 0, x_152);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_155);
return x_39;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_156 = lean_ctor_get(x_39, 1);
x_157 = lean_ctor_get(x_39, 2);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_39);
x_158 = lean_ctor_get(x_118, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_118, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_118, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_118, 3);
lean_inc(x_161);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 x_162 = x_118;
} else {
 lean_dec_ref(x_118);
 x_162 = lean_box(0);
}
x_163 = 1;
lean_inc(x_41);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_41);
lean_ctor_set(x_164, 1, x_156);
lean_ctor_set(x_164, 2, x_157);
lean_ctor_set(x_164, 3, x_158);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_165 = x_41;
} else {
 lean_dec_ref(x_41);
 x_165 = lean_box(0);
}
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_163);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_35);
lean_ctor_set(x_166, 2, x_36);
lean_ctor_set(x_166, 3, x_37);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_163);
x_167 = 0;
x_168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_159);
lean_ctor_set(x_168, 2, x_160);
lean_ctor_set(x_168, 3, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_167);
return x_168;
}
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_39);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_39, 3);
lean_dec(x_170);
x_171 = lean_ctor_get(x_39, 0);
lean_dec(x_171);
x_172 = !lean_is_exclusive(x_41);
if (x_172 == 0)
{
uint8_t x_173; 
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_173 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_173);
return x_2;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_174 = lean_ctor_get(x_41, 0);
x_175 = lean_ctor_get(x_41, 1);
x_176 = lean_ctor_get(x_41, 2);
x_177 = lean_ctor_get(x_41, 3);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_41);
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_178, 2, x_176);
lean_ctor_set(x_178, 3, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_127);
lean_ctor_set(x_39, 0, x_178);
x_179 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_179);
return x_2;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_180 = lean_ctor_get(x_39, 1);
x_181 = lean_ctor_get(x_39, 2);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_39);
x_182 = lean_ctor_get(x_41, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_41, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_41, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_41, 3);
lean_inc(x_185);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_186 = x_41;
} else {
 lean_dec_ref(x_41);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 4, 1);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_183);
lean_ctor_set(x_187, 2, x_184);
lean_ctor_set(x_187, 3, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_127);
x_188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_180);
lean_ctor_set(x_188, 2, x_181);
lean_ctor_set(x_188, 3, x_118);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_40);
x_189 = 1;
lean_ctor_set(x_2, 0, x_188);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_189);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_190; 
x_190 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_190);
return x_2;
}
}
case 1:
{
uint8_t x_191; 
lean_dec(x_36);
lean_dec(x_35);
x_191 = 1;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_191);
return x_2;
}
default: 
{
lean_object* x_192; uint8_t x_193; 
x_192 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_37, x_3, x_4);
x_193 = lean_ctor_get_uint8(x_192, sizeof(void*)*4);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_192, 3);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_192);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = lean_ctor_get(x_192, 3);
lean_dec(x_197);
x_198 = lean_ctor_get(x_192, 0);
lean_dec(x_198);
lean_ctor_set(x_192, 0, x_195);
x_199 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_199);
return x_2;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_200 = lean_ctor_get(x_192, 1);
x_201 = lean_ctor_get(x_192, 2);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_192);
x_202 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_202, 0, x_195);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_201);
lean_ctor_set(x_202, 3, x_195);
lean_ctor_set_uint8(x_202, sizeof(void*)*4, x_193);
x_203 = 1;
lean_ctor_set(x_2, 3, x_202);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_203);
return x_2;
}
}
else
{
uint8_t x_204; 
x_204 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_204 == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_192);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_192, 1);
x_207 = lean_ctor_get(x_192, 2);
x_208 = lean_ctor_get(x_192, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_192, 0);
lean_dec(x_209);
x_210 = !lean_is_exclusive(x_195);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_216; 
x_211 = lean_ctor_get(x_195, 0);
x_212 = lean_ctor_get(x_195, 1);
x_213 = lean_ctor_get(x_195, 2);
x_214 = lean_ctor_get(x_195, 3);
x_215 = 1;
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 2, x_36);
lean_ctor_set(x_195, 1, x_35);
lean_ctor_set(x_195, 0, x_34);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_215);
lean_ctor_set(x_192, 3, x_214);
lean_ctor_set(x_192, 2, x_213);
lean_ctor_set(x_192, 1, x_212);
lean_ctor_set(x_192, 0, x_211);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_215);
x_216 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_207);
lean_ctor_set(x_2, 1, x_206);
lean_ctor_set(x_2, 0, x_195);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_216);
return x_2;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; uint8_t x_223; 
x_217 = lean_ctor_get(x_195, 0);
x_218 = lean_ctor_get(x_195, 1);
x_219 = lean_ctor_get(x_195, 2);
x_220 = lean_ctor_get(x_195, 3);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_195);
x_221 = 1;
x_222 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_222, 0, x_34);
lean_ctor_set(x_222, 1, x_35);
lean_ctor_set(x_222, 2, x_36);
lean_ctor_set(x_222, 3, x_194);
lean_ctor_set_uint8(x_222, sizeof(void*)*4, x_221);
lean_ctor_set(x_192, 3, x_220);
lean_ctor_set(x_192, 2, x_219);
lean_ctor_set(x_192, 1, x_218);
lean_ctor_set(x_192, 0, x_217);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_221);
x_223 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_207);
lean_ctor_set(x_2, 1, x_206);
lean_ctor_set(x_2, 0, x_222);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_223);
return x_2;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_224 = lean_ctor_get(x_192, 1);
x_225 = lean_ctor_get(x_192, 2);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_192);
x_226 = lean_ctor_get(x_195, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_195, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_195, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_195, 3);
lean_inc(x_229);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_230 = x_195;
} else {
 lean_dec_ref(x_195);
 x_230 = lean_box(0);
}
x_231 = 1;
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(1, 4, 1);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_34);
lean_ctor_set(x_232, 1, x_35);
lean_ctor_set(x_232, 2, x_36);
lean_ctor_set(x_232, 3, x_194);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_231);
x_233 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_233, 0, x_226);
lean_ctor_set(x_233, 1, x_227);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_229);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_231);
x_234 = 0;
lean_ctor_set(x_2, 3, x_233);
lean_ctor_set(x_2, 2, x_225);
lean_ctor_set(x_2, 1, x_224);
lean_ctor_set(x_2, 0, x_232);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_234);
return x_2;
}
}
else
{
uint8_t x_235; 
lean_free_object(x_2);
x_235 = !lean_is_exclusive(x_195);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_195, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_195, 2);
lean_dec(x_237);
x_238 = lean_ctor_get(x_195, 1);
lean_dec(x_238);
x_239 = lean_ctor_get(x_195, 0);
lean_dec(x_239);
x_240 = 1;
lean_ctor_set(x_195, 3, x_192);
lean_ctor_set(x_195, 2, x_36);
lean_ctor_set(x_195, 1, x_35);
lean_ctor_set(x_195, 0, x_34);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_240);
return x_195;
}
else
{
uint8_t x_241; lean_object* x_242; 
lean_dec(x_195);
x_241 = 1;
x_242 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_242, 0, x_34);
lean_ctor_set(x_242, 1, x_35);
lean_ctor_set(x_242, 2, x_36);
lean_ctor_set(x_242, 3, x_192);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_241);
return x_242;
}
}
}
}
else
{
uint8_t x_243; 
x_243 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_192);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_192, 0);
lean_dec(x_245);
x_246 = !lean_is_exclusive(x_194);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_247 = lean_ctor_get(x_194, 0);
x_248 = lean_ctor_get(x_194, 1);
x_249 = lean_ctor_get(x_194, 2);
x_250 = lean_ctor_get(x_194, 3);
x_251 = 1;
lean_ctor_set(x_194, 3, x_247);
lean_ctor_set(x_194, 2, x_36);
lean_ctor_set(x_194, 1, x_35);
lean_ctor_set(x_194, 0, x_34);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_251);
lean_ctor_set(x_192, 0, x_250);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_251);
x_252 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_249);
lean_ctor_set(x_2, 1, x_248);
lean_ctor_set(x_2, 0, x_194);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_252);
return x_2;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_253 = lean_ctor_get(x_194, 0);
x_254 = lean_ctor_get(x_194, 1);
x_255 = lean_ctor_get(x_194, 2);
x_256 = lean_ctor_get(x_194, 3);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_194);
x_257 = 1;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_34);
lean_ctor_set(x_258, 1, x_35);
lean_ctor_set(x_258, 2, x_36);
lean_ctor_set(x_258, 3, x_253);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_192, 0, x_256);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_257);
x_259 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_255);
lean_ctor_set(x_2, 1, x_254);
lean_ctor_set(x_2, 0, x_258);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_259);
return x_2;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_260 = lean_ctor_get(x_192, 1);
x_261 = lean_ctor_get(x_192, 2);
x_262 = lean_ctor_get(x_192, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_192);
x_263 = lean_ctor_get(x_194, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_194, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_194, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_194, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_267 = x_194;
} else {
 lean_dec_ref(x_194);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_34);
lean_ctor_set(x_269, 1, x_35);
lean_ctor_set(x_269, 2, x_36);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_260);
lean_ctor_set(x_270, 2, x_261);
lean_ctor_set(x_270, 3, x_262);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
x_271 = 0;
lean_ctor_set(x_2, 3, x_270);
lean_ctor_set(x_2, 2, x_265);
lean_ctor_set(x_2, 1, x_264);
lean_ctor_set(x_2, 0, x_269);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_271);
return x_2;
}
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_192, 3);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
lean_free_object(x_2);
x_273 = !lean_is_exclusive(x_194);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_194, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_194, 2);
lean_dec(x_275);
x_276 = lean_ctor_get(x_194, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_194, 0);
lean_dec(x_277);
x_278 = 1;
lean_ctor_set(x_194, 3, x_192);
lean_ctor_set(x_194, 2, x_36);
lean_ctor_set(x_194, 1, x_35);
lean_ctor_set(x_194, 0, x_34);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_278);
return x_194;
}
else
{
uint8_t x_279; lean_object* x_280; 
lean_dec(x_194);
x_279 = 1;
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_34);
lean_ctor_set(x_280, 1, x_35);
lean_ctor_set(x_280, 2, x_36);
lean_ctor_set(x_280, 3, x_192);
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_279);
return x_280;
}
}
else
{
uint8_t x_281; 
x_281 = lean_ctor_get_uint8(x_272, sizeof(void*)*4);
if (x_281 == 0)
{
uint8_t x_282; 
lean_free_object(x_2);
x_282 = !lean_is_exclusive(x_192);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_192, 3);
lean_dec(x_283);
x_284 = lean_ctor_get(x_192, 0);
lean_dec(x_284);
x_285 = !lean_is_exclusive(x_272);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_291; 
x_286 = lean_ctor_get(x_272, 0);
x_287 = lean_ctor_get(x_272, 1);
x_288 = lean_ctor_get(x_272, 2);
x_289 = lean_ctor_get(x_272, 3);
x_290 = 1;
lean_inc(x_194);
lean_ctor_set(x_272, 3, x_194);
lean_ctor_set(x_272, 2, x_36);
lean_ctor_set(x_272, 1, x_35);
lean_ctor_set(x_272, 0, x_34);
x_291 = !lean_is_exclusive(x_194);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_292 = lean_ctor_get(x_194, 3);
lean_dec(x_292);
x_293 = lean_ctor_get(x_194, 2);
lean_dec(x_293);
x_294 = lean_ctor_get(x_194, 1);
lean_dec(x_294);
x_295 = lean_ctor_get(x_194, 0);
lean_dec(x_295);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_290);
lean_ctor_set(x_194, 3, x_289);
lean_ctor_set(x_194, 2, x_288);
lean_ctor_set(x_194, 1, x_287);
lean_ctor_set(x_194, 0, x_286);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_290);
x_296 = 0;
lean_ctor_set(x_192, 3, x_194);
lean_ctor_set(x_192, 0, x_272);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_296);
return x_192;
}
else
{
lean_object* x_297; uint8_t x_298; 
lean_dec(x_194);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_290);
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_286);
lean_ctor_set(x_297, 1, x_287);
lean_ctor_set(x_297, 2, x_288);
lean_ctor_set(x_297, 3, x_289);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_290);
x_298 = 0;
lean_ctor_set(x_192, 3, x_297);
lean_ctor_set(x_192, 0, x_272);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_298);
return x_192;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_299 = lean_ctor_get(x_272, 0);
x_300 = lean_ctor_get(x_272, 1);
x_301 = lean_ctor_get(x_272, 2);
x_302 = lean_ctor_get(x_272, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_272);
x_303 = 1;
lean_inc(x_194);
x_304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_304, 0, x_34);
lean_ctor_set(x_304, 1, x_35);
lean_ctor_set(x_304, 2, x_36);
lean_ctor_set(x_304, 3, x_194);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_305 = x_194;
} else {
 lean_dec_ref(x_194);
 x_305 = lean_box(0);
}
lean_ctor_set_uint8(x_304, sizeof(void*)*4, x_303);
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 4, 1);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_299);
lean_ctor_set(x_306, 1, x_300);
lean_ctor_set(x_306, 2, x_301);
lean_ctor_set(x_306, 3, x_302);
lean_ctor_set_uint8(x_306, sizeof(void*)*4, x_303);
x_307 = 0;
lean_ctor_set(x_192, 3, x_306);
lean_ctor_set(x_192, 0, x_304);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_307);
return x_192;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; 
x_308 = lean_ctor_get(x_192, 1);
x_309 = lean_ctor_get(x_192, 2);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_192);
x_310 = lean_ctor_get(x_272, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_272, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_272, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_272, 3);
lean_inc(x_313);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_314 = x_272;
} else {
 lean_dec_ref(x_272);
 x_314 = lean_box(0);
}
x_315 = 1;
lean_inc(x_194);
if (lean_is_scalar(x_314)) {
 x_316 = lean_alloc_ctor(1, 4, 1);
} else {
 x_316 = x_314;
}
lean_ctor_set(x_316, 0, x_34);
lean_ctor_set(x_316, 1, x_35);
lean_ctor_set(x_316, 2, x_36);
lean_ctor_set(x_316, 3, x_194);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_317 = x_194;
} else {
 lean_dec_ref(x_194);
 x_317 = lean_box(0);
}
lean_ctor_set_uint8(x_316, sizeof(void*)*4, x_315);
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 4, 1);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_310);
lean_ctor_set(x_318, 1, x_311);
lean_ctor_set(x_318, 2, x_312);
lean_ctor_set(x_318, 3, x_313);
lean_ctor_set_uint8(x_318, sizeof(void*)*4, x_315);
x_319 = 0;
x_320 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_320, 0, x_316);
lean_ctor_set(x_320, 1, x_308);
lean_ctor_set(x_320, 2, x_309);
lean_ctor_set(x_320, 3, x_318);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_319);
return x_320;
}
}
else
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_192);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_322 = lean_ctor_get(x_192, 3);
lean_dec(x_322);
x_323 = lean_ctor_get(x_192, 0);
lean_dec(x_323);
x_324 = !lean_is_exclusive(x_194);
if (x_324 == 0)
{
uint8_t x_325; 
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_281);
x_325 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_325);
return x_2;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_326 = lean_ctor_get(x_194, 0);
x_327 = lean_ctor_get(x_194, 1);
x_328 = lean_ctor_get(x_194, 2);
x_329 = lean_ctor_get(x_194, 3);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_194);
x_330 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_330, 0, x_326);
lean_ctor_set(x_330, 1, x_327);
lean_ctor_set(x_330, 2, x_328);
lean_ctor_set(x_330, 3, x_329);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_281);
lean_ctor_set(x_192, 0, x_330);
x_331 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_331);
return x_2;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_332 = lean_ctor_get(x_192, 1);
x_333 = lean_ctor_get(x_192, 2);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_192);
x_334 = lean_ctor_get(x_194, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_194, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_194, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_194, 3);
lean_inc(x_337);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_338 = x_194;
} else {
 lean_dec_ref(x_194);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 4, 1);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_334);
lean_ctor_set(x_339, 1, x_335);
lean_ctor_set(x_339, 2, x_336);
lean_ctor_set(x_339, 3, x_337);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_281);
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_332);
lean_ctor_set(x_340, 2, x_333);
lean_ctor_set(x_340, 3, x_272);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_193);
x_341 = 1;
lean_ctor_set(x_2, 3, x_340);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_341);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_342; 
x_342 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_342);
return x_2;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_343 = lean_ctor_get(x_2, 0);
x_344 = lean_ctor_get(x_2, 1);
x_345 = lean_ctor_get(x_2, 2);
x_346 = lean_ctor_get(x_2, 3);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_2);
x_347 = l_Lean_Name_quickCmp(x_3, x_344);
switch (x_347) {
case 0:
{
lean_object* x_348; uint8_t x_349; 
x_348 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_343, x_3, x_4);
x_349 = lean_ctor_get_uint8(x_348, sizeof(void*)*4);
if (x_349 == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_348, 3);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; 
x_352 = lean_ctor_get(x_348, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_348, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_354 = x_348;
} else {
 lean_dec_ref(x_348);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 4, 1);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_352);
lean_ctor_set(x_355, 2, x_353);
lean_ctor_set(x_355, 3, x_351);
lean_ctor_set_uint8(x_355, sizeof(void*)*4, x_349);
x_356 = 1;
x_357 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_344);
lean_ctor_set(x_357, 2, x_345);
lean_ctor_set(x_357, 3, x_346);
lean_ctor_set_uint8(x_357, sizeof(void*)*4, x_356);
return x_357;
}
else
{
uint8_t x_358; 
x_358 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; 
x_359 = lean_ctor_get(x_348, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_348, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_361 = x_348;
} else {
 lean_dec_ref(x_348);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_351, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_351, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_351, 3);
lean_inc(x_365);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_366 = x_351;
} else {
 lean_dec_ref(x_351);
 x_366 = lean_box(0);
}
x_367 = 1;
if (lean_is_scalar(x_366)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_366;
}
lean_ctor_set(x_368, 0, x_350);
lean_ctor_set(x_368, 1, x_359);
lean_ctor_set(x_368, 2, x_360);
lean_ctor_set(x_368, 3, x_362);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_361)) {
 x_369 = lean_alloc_ctor(1, 4, 1);
} else {
 x_369 = x_361;
}
lean_ctor_set(x_369, 0, x_365);
lean_ctor_set(x_369, 1, x_344);
lean_ctor_set(x_369, 2, x_345);
lean_ctor_set(x_369, 3, x_346);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_367);
x_370 = 0;
x_371 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_363);
lean_ctor_set(x_371, 2, x_364);
lean_ctor_set(x_371, 3, x_369);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_370);
return x_371;
}
else
{
lean_object* x_372; uint8_t x_373; lean_object* x_374; 
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_372 = x_351;
} else {
 lean_dec_ref(x_351);
 x_372 = lean_box(0);
}
x_373 = 1;
if (lean_is_scalar(x_372)) {
 x_374 = lean_alloc_ctor(1, 4, 1);
} else {
 x_374 = x_372;
}
lean_ctor_set(x_374, 0, x_348);
lean_ctor_set(x_374, 1, x_344);
lean_ctor_set(x_374, 2, x_345);
lean_ctor_set(x_374, 3, x_346);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; 
x_376 = lean_ctor_get(x_348, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_348, 2);
lean_inc(x_377);
x_378 = lean_ctor_get(x_348, 3);
lean_inc(x_378);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_379 = x_348;
} else {
 lean_dec_ref(x_348);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_350, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_350, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_350, 2);
lean_inc(x_382);
x_383 = lean_ctor_get(x_350, 3);
lean_inc(x_383);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_384 = x_350;
} else {
 lean_dec_ref(x_350);
 x_384 = lean_box(0);
}
x_385 = 1;
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_380);
lean_ctor_set(x_386, 1, x_381);
lean_ctor_set(x_386, 2, x_382);
lean_ctor_set(x_386, 3, x_383);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
if (lean_is_scalar(x_379)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_379;
}
lean_ctor_set(x_387, 0, x_378);
lean_ctor_set(x_387, 1, x_344);
lean_ctor_set(x_387, 2, x_345);
lean_ctor_set(x_387, 3, x_346);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_385);
x_388 = 0;
x_389 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_376);
lean_ctor_set(x_389, 2, x_377);
lean_ctor_set(x_389, 3, x_387);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
return x_389;
}
else
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_348, 3);
lean_inc(x_390);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; uint8_t x_392; lean_object* x_393; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_391 = x_350;
} else {
 lean_dec_ref(x_350);
 x_391 = lean_box(0);
}
x_392 = 1;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_348);
lean_ctor_set(x_393, 1, x_344);
lean_ctor_set(x_393, 2, x_345);
lean_ctor_set(x_393, 3, x_346);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
return x_393;
}
else
{
uint8_t x_394; 
x_394 = lean_ctor_get_uint8(x_390, sizeof(void*)*4);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; 
x_395 = lean_ctor_get(x_348, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_348, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_397 = x_348;
} else {
 lean_dec_ref(x_348);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_390, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_390, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_390, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_390, 3);
lean_inc(x_401);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 lean_ctor_release(x_390, 2);
 lean_ctor_release(x_390, 3);
 x_402 = x_390;
} else {
 lean_dec_ref(x_390);
 x_402 = lean_box(0);
}
x_403 = 1;
lean_inc(x_350);
if (lean_is_scalar(x_402)) {
 x_404 = lean_alloc_ctor(1, 4, 1);
} else {
 x_404 = x_402;
}
lean_ctor_set(x_404, 0, x_350);
lean_ctor_set(x_404, 1, x_395);
lean_ctor_set(x_404, 2, x_396);
lean_ctor_set(x_404, 3, x_398);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_405 = x_350;
} else {
 lean_dec_ref(x_350);
 x_405 = lean_box(0);
}
lean_ctor_set_uint8(x_404, sizeof(void*)*4, x_403);
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 4, 1);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_401);
lean_ctor_set(x_406, 1, x_344);
lean_ctor_set(x_406, 2, x_345);
lean_ctor_set(x_406, 3, x_346);
lean_ctor_set_uint8(x_406, sizeof(void*)*4, x_403);
x_407 = 0;
if (lean_is_scalar(x_397)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_397;
}
lean_ctor_set(x_408, 0, x_404);
lean_ctor_set(x_408, 1, x_399);
lean_ctor_set(x_408, 2, x_400);
lean_ctor_set(x_408, 3, x_406);
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_407);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_409 = lean_ctor_get(x_348, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_348, 2);
lean_inc(x_410);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_411 = x_348;
} else {
 lean_dec_ref(x_348);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_350, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_350, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_350, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_350, 3);
lean_inc(x_415);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_416 = x_350;
} else {
 lean_dec_ref(x_350);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_412);
lean_ctor_set(x_417, 1, x_413);
lean_ctor_set(x_417, 2, x_414);
lean_ctor_set(x_417, 3, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_394);
if (lean_is_scalar(x_411)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_411;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_409);
lean_ctor_set(x_418, 2, x_410);
lean_ctor_set(x_418, 3, x_390);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_349);
x_419 = 1;
x_420 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_344);
lean_ctor_set(x_420, 2, x_345);
lean_ctor_set(x_420, 3, x_346);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_419);
return x_420;
}
}
}
}
}
else
{
uint8_t x_421; lean_object* x_422; 
x_421 = 1;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_348);
lean_ctor_set(x_422, 1, x_344);
lean_ctor_set(x_422, 2, x_345);
lean_ctor_set(x_422, 3, x_346);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
}
case 1:
{
uint8_t x_423; lean_object* x_424; 
lean_dec(x_345);
lean_dec(x_344);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_343);
lean_ctor_set(x_424, 1, x_3);
lean_ctor_set(x_424, 2, x_4);
lean_ctor_set(x_424, 3, x_346);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
default: 
{
lean_object* x_425; uint8_t x_426; 
x_425 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_346, x_3, x_4);
x_426 = lean_ctor_get_uint8(x_425, sizeof(void*)*4);
if (x_426 == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_425, 0);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_425, 3);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; 
x_429 = lean_ctor_get(x_425, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_425, 2);
lean_inc(x_430);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_431 = x_425;
} else {
 lean_dec_ref(x_425);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 4, 1);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_428);
lean_ctor_set(x_432, 1, x_429);
lean_ctor_set(x_432, 2, x_430);
lean_ctor_set(x_432, 3, x_428);
lean_ctor_set_uint8(x_432, sizeof(void*)*4, x_426);
x_433 = 1;
x_434 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_434, 0, x_343);
lean_ctor_set(x_434, 1, x_344);
lean_ctor_set(x_434, 2, x_345);
lean_ctor_set(x_434, 3, x_432);
lean_ctor_set_uint8(x_434, sizeof(void*)*4, x_433);
return x_434;
}
else
{
uint8_t x_435; 
x_435 = lean_ctor_get_uint8(x_428, sizeof(void*)*4);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; 
x_436 = lean_ctor_get(x_425, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_425, 2);
lean_inc(x_437);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_438 = x_425;
} else {
 lean_dec_ref(x_425);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_428, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_428, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_428, 3);
lean_inc(x_442);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_443 = x_428;
} else {
 lean_dec_ref(x_428);
 x_443 = lean_box(0);
}
x_444 = 1;
if (lean_is_scalar(x_443)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_443;
}
lean_ctor_set(x_445, 0, x_343);
lean_ctor_set(x_445, 1, x_344);
lean_ctor_set(x_445, 2, x_345);
lean_ctor_set(x_445, 3, x_427);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_438)) {
 x_446 = lean_alloc_ctor(1, 4, 1);
} else {
 x_446 = x_438;
}
lean_ctor_set(x_446, 0, x_439);
lean_ctor_set(x_446, 1, x_440);
lean_ctor_set(x_446, 2, x_441);
lean_ctor_set(x_446, 3, x_442);
lean_ctor_set_uint8(x_446, sizeof(void*)*4, x_444);
x_447 = 0;
x_448 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_436);
lean_ctor_set(x_448, 2, x_437);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
return x_448;
}
else
{
lean_object* x_449; uint8_t x_450; lean_object* x_451; 
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_449 = x_428;
} else {
 lean_dec_ref(x_428);
 x_449 = lean_box(0);
}
x_450 = 1;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_343);
lean_ctor_set(x_451, 1, x_344);
lean_ctor_set(x_451, 2, x_345);
lean_ctor_set(x_451, 3, x_425);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
return x_451;
}
}
}
else
{
uint8_t x_452; 
x_452 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; 
x_453 = lean_ctor_get(x_425, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_425, 2);
lean_inc(x_454);
x_455 = lean_ctor_get(x_425, 3);
lean_inc(x_455);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_456 = x_425;
} else {
 lean_dec_ref(x_425);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_427, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_427, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_427, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_427, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_461 = x_427;
} else {
 lean_dec_ref(x_427);
 x_461 = lean_box(0);
}
x_462 = 1;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_343);
lean_ctor_set(x_463, 1, x_344);
lean_ctor_set(x_463, 2, x_345);
lean_ctor_set(x_463, 3, x_457);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_462);
if (lean_is_scalar(x_456)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_456;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_453);
lean_ctor_set(x_464, 2, x_454);
lean_ctor_set(x_464, 3, x_455);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_462);
x_465 = 0;
x_466 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_466, 0, x_463);
lean_ctor_set(x_466, 1, x_458);
lean_ctor_set(x_466, 2, x_459);
lean_ctor_set(x_466, 3, x_464);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
return x_466;
}
else
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_425, 3);
lean_inc(x_467);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; uint8_t x_469; lean_object* x_470; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_468 = x_427;
} else {
 lean_dec_ref(x_427);
 x_468 = lean_box(0);
}
x_469 = 1;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_343);
lean_ctor_set(x_470, 1, x_344);
lean_ctor_set(x_470, 2, x_345);
lean_ctor_set(x_470, 3, x_425);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
return x_470;
}
else
{
uint8_t x_471; 
x_471 = lean_ctor_get_uint8(x_467, sizeof(void*)*4);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; lean_object* x_485; 
x_472 = lean_ctor_get(x_425, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_425, 2);
lean_inc(x_473);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_474 = x_425;
} else {
 lean_dec_ref(x_425);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_467, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_467, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_467, 2);
lean_inc(x_477);
x_478 = lean_ctor_get(x_467, 3);
lean_inc(x_478);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 x_479 = x_467;
} else {
 lean_dec_ref(x_467);
 x_479 = lean_box(0);
}
x_480 = 1;
lean_inc(x_427);
if (lean_is_scalar(x_479)) {
 x_481 = lean_alloc_ctor(1, 4, 1);
} else {
 x_481 = x_479;
}
lean_ctor_set(x_481, 0, x_343);
lean_ctor_set(x_481, 1, x_344);
lean_ctor_set(x_481, 2, x_345);
lean_ctor_set(x_481, 3, x_427);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_482 = x_427;
} else {
 lean_dec_ref(x_427);
 x_482 = lean_box(0);
}
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_480);
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_475);
lean_ctor_set(x_483, 1, x_476);
lean_ctor_set(x_483, 2, x_477);
lean_ctor_set(x_483, 3, x_478);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_480);
x_484 = 0;
if (lean_is_scalar(x_474)) {
 x_485 = lean_alloc_ctor(1, 4, 1);
} else {
 x_485 = x_474;
}
lean_ctor_set(x_485, 0, x_481);
lean_ctor_set(x_485, 1, x_472);
lean_ctor_set(x_485, 2, x_473);
lean_ctor_set(x_485, 3, x_483);
lean_ctor_set_uint8(x_485, sizeof(void*)*4, x_484);
return x_485;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; 
x_486 = lean_ctor_get(x_425, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_425, 2);
lean_inc(x_487);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_488 = x_425;
} else {
 lean_dec_ref(x_425);
 x_488 = lean_box(0);
}
x_489 = lean_ctor_get(x_427, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_427, 1);
lean_inc(x_490);
x_491 = lean_ctor_get(x_427, 2);
lean_inc(x_491);
x_492 = lean_ctor_get(x_427, 3);
lean_inc(x_492);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_493 = x_427;
} else {
 lean_dec_ref(x_427);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_489);
lean_ctor_set(x_494, 1, x_490);
lean_ctor_set(x_494, 2, x_491);
lean_ctor_set(x_494, 3, x_492);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_471);
if (lean_is_scalar(x_488)) {
 x_495 = lean_alloc_ctor(1, 4, 1);
} else {
 x_495 = x_488;
}
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_486);
lean_ctor_set(x_495, 2, x_487);
lean_ctor_set(x_495, 3, x_467);
lean_ctor_set_uint8(x_495, sizeof(void*)*4, x_426);
x_496 = 1;
x_497 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_497, 0, x_343);
lean_ctor_set(x_497, 1, x_344);
lean_ctor_set(x_497, 2, x_345);
lean_ctor_set(x_497, 3, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_496);
return x_497;
}
}
}
}
}
else
{
uint8_t x_498; lean_object* x_499; 
x_498 = 1;
x_499 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_499, 0, x_343);
lean_ctor_set(x_499, 1, x_344);
lean_ctor_set(x_499, 2, x_345);
lean_ctor_set(x_499, 3, x_425);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_498);
return x_499;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = 0;
x_7 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*4, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*4);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = l_Lean_Name_quickCmp(x_3, x_11);
switch (x_14) {
case 0:
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_10, x_3, x_4);
x_16 = 0;
lean_ctor_set(x_2, 0, x_15);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_16);
return x_2;
}
case 1:
{
uint8_t x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = 0;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_17);
return x_2;
}
default: 
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_13, x_3, x_4);
x_19 = 0;
lean_ctor_set(x_2, 3, x_18);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_19);
return x_2;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_24 = l_Lean_Name_quickCmp(x_3, x_21);
switch (x_24) {
case 0:
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_20, x_3, x_4);
x_26 = 0;
x_27 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_21);
lean_ctor_set(x_27, 2, x_22);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*4, x_26);
return x_27;
}
case 1:
{
uint8_t x_28; lean_object* x_29; 
lean_dec(x_22);
lean_dec(x_21);
x_28 = 0;
x_29 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_4);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*4, x_28);
return x_29;
}
default: 
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_23, x_3, x_4);
x_31 = 0;
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_21);
lean_ctor_set(x_32, 2, x_22);
lean_ctor_set(x_32, 3, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_31);
return x_32;
}
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = l_Lean_Name_quickCmp(x_3, x_35);
switch (x_38) {
case 0:
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_34, x_3, x_4);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*4);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_39, 3);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_39);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_39, 3);
lean_dec(x_44);
x_45 = lean_ctor_get(x_39, 0);
lean_dec(x_45);
lean_ctor_set(x_39, 0, x_42);
x_46 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_46);
return x_2;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_39, 1);
x_48 = lean_ctor_get(x_39, 2);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_42);
lean_ctor_set_uint8(x_49, sizeof(void*)*4, x_40);
x_50 = 1;
lean_ctor_set(x_2, 0, x_49);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_50);
return x_2;
}
}
else
{
uint8_t x_51; 
x_51 = lean_ctor_get_uint8(x_42, sizeof(void*)*4);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_39);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_39, 1);
x_54 = lean_ctor_get(x_39, 2);
x_55 = lean_ctor_get(x_39, 3);
lean_dec(x_55);
x_56 = lean_ctor_get(x_39, 0);
lean_dec(x_56);
x_57 = !lean_is_exclusive(x_42);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_42, 0);
x_59 = lean_ctor_get(x_42, 1);
x_60 = lean_ctor_get(x_42, 2);
x_61 = lean_ctor_get(x_42, 3);
x_62 = 1;
lean_ctor_set(x_42, 3, x_58);
lean_ctor_set(x_42, 2, x_54);
lean_ctor_set(x_42, 1, x_53);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_62);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_61);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_62);
x_63 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_60);
lean_ctor_set(x_2, 1, x_59);
lean_ctor_set(x_2, 0, x_42);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_63);
return x_2;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_42, 0);
x_65 = lean_ctor_get(x_42, 1);
x_66 = lean_ctor_get(x_42, 2);
x_67 = lean_ctor_get(x_42, 3);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_42);
x_68 = 1;
x_69 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_69, 0, x_41);
lean_ctor_set(x_69, 1, x_53);
lean_ctor_set(x_69, 2, x_54);
lean_ctor_set(x_69, 3, x_64);
lean_ctor_set_uint8(x_69, sizeof(void*)*4, x_68);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_67);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_68);
x_70 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_66);
lean_ctor_set(x_2, 1, x_65);
lean_ctor_set(x_2, 0, x_69);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_70);
return x_2;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_71 = lean_ctor_get(x_39, 1);
x_72 = lean_ctor_get(x_39, 2);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_39);
x_73 = lean_ctor_get(x_42, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_42, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_42, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_42, 3);
lean_inc(x_76);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 lean_ctor_release(x_42, 3);
 x_77 = x_42;
} else {
 lean_dec_ref(x_42);
 x_77 = lean_box(0);
}
x_78 = 1;
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(1, 4, 1);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_41);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_72);
lean_ctor_set(x_79, 3, x_73);
lean_ctor_set_uint8(x_79, sizeof(void*)*4, x_78);
x_80 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_80, 0, x_76);
lean_ctor_set(x_80, 1, x_35);
lean_ctor_set(x_80, 2, x_36);
lean_ctor_set(x_80, 3, x_37);
lean_ctor_set_uint8(x_80, sizeof(void*)*4, x_78);
x_81 = 0;
lean_ctor_set(x_2, 3, x_80);
lean_ctor_set(x_2, 2, x_75);
lean_ctor_set(x_2, 1, x_74);
lean_ctor_set(x_2, 0, x_79);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_81);
return x_2;
}
}
else
{
uint8_t x_82; 
lean_free_object(x_2);
x_82 = !lean_is_exclusive(x_42);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_42, 3);
lean_dec(x_83);
x_84 = lean_ctor_get(x_42, 2);
lean_dec(x_84);
x_85 = lean_ctor_get(x_42, 1);
lean_dec(x_85);
x_86 = lean_ctor_get(x_42, 0);
lean_dec(x_86);
x_87 = 1;
lean_ctor_set(x_42, 3, x_37);
lean_ctor_set(x_42, 2, x_36);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_87);
return x_42;
}
else
{
uint8_t x_88; lean_object* x_89; 
lean_dec(x_42);
x_88 = 1;
x_89 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_89, 0, x_39);
lean_ctor_set(x_89, 1, x_35);
lean_ctor_set(x_89, 2, x_36);
lean_ctor_set(x_89, 3, x_37);
lean_ctor_set_uint8(x_89, sizeof(void*)*4, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
x_90 = lean_ctor_get_uint8(x_41, sizeof(void*)*4);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_39);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_39, 1);
x_93 = lean_ctor_get(x_39, 2);
x_94 = lean_ctor_get(x_39, 3);
x_95 = lean_ctor_get(x_39, 0);
lean_dec(x_95);
x_96 = !lean_is_exclusive(x_41);
if (x_96 == 0)
{
uint8_t x_97; uint8_t x_98; 
x_97 = 1;
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_97);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_94);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_97);
x_98 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_93);
lean_ctor_set(x_2, 1, x_92);
lean_ctor_set(x_2, 0, x_41);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_98);
return x_2;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; uint8_t x_105; 
x_99 = lean_ctor_get(x_41, 0);
x_100 = lean_ctor_get(x_41, 1);
x_101 = lean_ctor_get(x_41, 2);
x_102 = lean_ctor_get(x_41, 3);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_41);
x_103 = 1;
x_104 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_100);
lean_ctor_set(x_104, 2, x_101);
lean_ctor_set(x_104, 3, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*4, x_103);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 0, x_94);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_103);
x_105 = 0;
lean_ctor_set(x_2, 3, x_39);
lean_ctor_set(x_2, 2, x_93);
lean_ctor_set(x_2, 1, x_92);
lean_ctor_set(x_2, 0, x_104);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_105);
return x_2;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_106 = lean_ctor_get(x_39, 1);
x_107 = lean_ctor_get(x_39, 2);
x_108 = lean_ctor_get(x_39, 3);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_39);
x_109 = lean_ctor_get(x_41, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_41, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_41, 2);
lean_inc(x_111);
x_112 = lean_ctor_get(x_41, 3);
lean_inc(x_112);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_113 = x_41;
} else {
 lean_dec_ref(x_41);
 x_113 = lean_box(0);
}
x_114 = 1;
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(1, 4, 1);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_110);
lean_ctor_set(x_115, 2, x_111);
lean_ctor_set(x_115, 3, x_112);
lean_ctor_set_uint8(x_115, sizeof(void*)*4, x_114);
x_116 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_116, 0, x_108);
lean_ctor_set(x_116, 1, x_35);
lean_ctor_set(x_116, 2, x_36);
lean_ctor_set(x_116, 3, x_37);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_114);
x_117 = 0;
lean_ctor_set(x_2, 3, x_116);
lean_ctor_set(x_2, 2, x_107);
lean_ctor_set(x_2, 1, x_106);
lean_ctor_set(x_2, 0, x_115);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_117);
return x_2;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_39, 3);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
lean_free_object(x_2);
x_119 = !lean_is_exclusive(x_41);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_120 = lean_ctor_get(x_41, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_41, 2);
lean_dec(x_121);
x_122 = lean_ctor_get(x_41, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_41, 0);
lean_dec(x_123);
x_124 = 1;
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_124);
return x_41;
}
else
{
uint8_t x_125; lean_object* x_126; 
lean_dec(x_41);
x_125 = 1;
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_39);
lean_ctor_set(x_126, 1, x_35);
lean_ctor_set(x_126, 2, x_36);
lean_ctor_set(x_126, 3, x_37);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
return x_126;
}
}
else
{
uint8_t x_127; 
x_127 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
if (x_127 == 0)
{
uint8_t x_128; 
lean_free_object(x_2);
x_128 = !lean_is_exclusive(x_39);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_39, 1);
x_130 = lean_ctor_get(x_39, 2);
x_131 = lean_ctor_get(x_39, 3);
lean_dec(x_131);
x_132 = lean_ctor_get(x_39, 0);
lean_dec(x_132);
x_133 = !lean_is_exclusive(x_118);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; 
x_134 = lean_ctor_get(x_118, 0);
x_135 = lean_ctor_get(x_118, 1);
x_136 = lean_ctor_get(x_118, 2);
x_137 = lean_ctor_get(x_118, 3);
x_138 = 1;
lean_inc(x_41);
lean_ctor_set(x_118, 3, x_134);
lean_ctor_set(x_118, 2, x_130);
lean_ctor_set(x_118, 1, x_129);
lean_ctor_set(x_118, 0, x_41);
x_139 = !lean_is_exclusive(x_41);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_ctor_get(x_41, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_41, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_41, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_41, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_138);
lean_ctor_set(x_41, 3, x_37);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 0, x_137);
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_138);
x_144 = 0;
lean_ctor_set(x_39, 3, x_41);
lean_ctor_set(x_39, 2, x_136);
lean_ctor_set(x_39, 1, x_135);
lean_ctor_set(x_39, 0, x_118);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_144);
return x_39;
}
else
{
lean_object* x_145; uint8_t x_146; 
lean_dec(x_41);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_138);
x_145 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_145, 0, x_137);
lean_ctor_set(x_145, 1, x_35);
lean_ctor_set(x_145, 2, x_36);
lean_ctor_set(x_145, 3, x_37);
lean_ctor_set_uint8(x_145, sizeof(void*)*4, x_138);
x_146 = 0;
lean_ctor_set(x_39, 3, x_145);
lean_ctor_set(x_39, 2, x_136);
lean_ctor_set(x_39, 1, x_135);
lean_ctor_set(x_39, 0, x_118);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_146);
return x_39;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_147 = lean_ctor_get(x_118, 0);
x_148 = lean_ctor_get(x_118, 1);
x_149 = lean_ctor_get(x_118, 2);
x_150 = lean_ctor_get(x_118, 3);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_118);
x_151 = 1;
lean_inc(x_41);
x_152 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_152, 0, x_41);
lean_ctor_set(x_152, 1, x_129);
lean_ctor_set(x_152, 2, x_130);
lean_ctor_set(x_152, 3, x_147);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_153 = x_41;
} else {
 lean_dec_ref(x_41);
 x_153 = lean_box(0);
}
lean_ctor_set_uint8(x_152, sizeof(void*)*4, x_151);
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 4, 1);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_150);
lean_ctor_set(x_154, 1, x_35);
lean_ctor_set(x_154, 2, x_36);
lean_ctor_set(x_154, 3, x_37);
lean_ctor_set_uint8(x_154, sizeof(void*)*4, x_151);
x_155 = 0;
lean_ctor_set(x_39, 3, x_154);
lean_ctor_set(x_39, 2, x_149);
lean_ctor_set(x_39, 1, x_148);
lean_ctor_set(x_39, 0, x_152);
lean_ctor_set_uint8(x_39, sizeof(void*)*4, x_155);
return x_39;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
x_156 = lean_ctor_get(x_39, 1);
x_157 = lean_ctor_get(x_39, 2);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_39);
x_158 = lean_ctor_get(x_118, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_118, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_118, 2);
lean_inc(x_160);
x_161 = lean_ctor_get(x_118, 3);
lean_inc(x_161);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 x_162 = x_118;
} else {
 lean_dec_ref(x_118);
 x_162 = lean_box(0);
}
x_163 = 1;
lean_inc(x_41);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(1, 4, 1);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_41);
lean_ctor_set(x_164, 1, x_156);
lean_ctor_set(x_164, 2, x_157);
lean_ctor_set(x_164, 3, x_158);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_165 = x_41;
} else {
 lean_dec_ref(x_41);
 x_165 = lean_box(0);
}
lean_ctor_set_uint8(x_164, sizeof(void*)*4, x_163);
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(1, 4, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_161);
lean_ctor_set(x_166, 1, x_35);
lean_ctor_set(x_166, 2, x_36);
lean_ctor_set(x_166, 3, x_37);
lean_ctor_set_uint8(x_166, sizeof(void*)*4, x_163);
x_167 = 0;
x_168 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_159);
lean_ctor_set(x_168, 2, x_160);
lean_ctor_set(x_168, 3, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*4, x_167);
return x_168;
}
}
else
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_39);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = lean_ctor_get(x_39, 3);
lean_dec(x_170);
x_171 = lean_ctor_get(x_39, 0);
lean_dec(x_171);
x_172 = !lean_is_exclusive(x_41);
if (x_172 == 0)
{
uint8_t x_173; 
lean_ctor_set_uint8(x_41, sizeof(void*)*4, x_127);
x_173 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_173);
return x_2;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_174 = lean_ctor_get(x_41, 0);
x_175 = lean_ctor_get(x_41, 1);
x_176 = lean_ctor_get(x_41, 2);
x_177 = lean_ctor_get(x_41, 3);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_41);
x_178 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_175);
lean_ctor_set(x_178, 2, x_176);
lean_ctor_set(x_178, 3, x_177);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_127);
lean_ctor_set(x_39, 0, x_178);
x_179 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_179);
return x_2;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; 
x_180 = lean_ctor_get(x_39, 1);
x_181 = lean_ctor_get(x_39, 2);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_39);
x_182 = lean_ctor_get(x_41, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_41, 1);
lean_inc(x_183);
x_184 = lean_ctor_get(x_41, 2);
lean_inc(x_184);
x_185 = lean_ctor_get(x_41, 3);
lean_inc(x_185);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 lean_ctor_release(x_41, 2);
 lean_ctor_release(x_41, 3);
 x_186 = x_41;
} else {
 lean_dec_ref(x_41);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 4, 1);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_182);
lean_ctor_set(x_187, 1, x_183);
lean_ctor_set(x_187, 2, x_184);
lean_ctor_set(x_187, 3, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_127);
x_188 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_180);
lean_ctor_set(x_188, 2, x_181);
lean_ctor_set(x_188, 3, x_118);
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_40);
x_189 = 1;
lean_ctor_set(x_2, 0, x_188);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_189);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_190; 
x_190 = 1;
lean_ctor_set(x_2, 0, x_39);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_190);
return x_2;
}
}
case 1:
{
uint8_t x_191; 
lean_dec(x_36);
lean_dec(x_35);
x_191 = 1;
lean_ctor_set(x_2, 2, x_4);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_191);
return x_2;
}
default: 
{
lean_object* x_192; uint8_t x_193; 
x_192 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_37, x_3, x_4);
x_193 = lean_ctor_get_uint8(x_192, sizeof(void*)*4);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_192, 3);
lean_inc(x_195);
if (lean_obj_tag(x_195) == 0)
{
uint8_t x_196; 
x_196 = !lean_is_exclusive(x_192);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_197 = lean_ctor_get(x_192, 3);
lean_dec(x_197);
x_198 = lean_ctor_get(x_192, 0);
lean_dec(x_198);
lean_ctor_set(x_192, 0, x_195);
x_199 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_199);
return x_2;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_200 = lean_ctor_get(x_192, 1);
x_201 = lean_ctor_get(x_192, 2);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_192);
x_202 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_202, 0, x_195);
lean_ctor_set(x_202, 1, x_200);
lean_ctor_set(x_202, 2, x_201);
lean_ctor_set(x_202, 3, x_195);
lean_ctor_set_uint8(x_202, sizeof(void*)*4, x_193);
x_203 = 1;
lean_ctor_set(x_2, 3, x_202);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_203);
return x_2;
}
}
else
{
uint8_t x_204; 
x_204 = lean_ctor_get_uint8(x_195, sizeof(void*)*4);
if (x_204 == 0)
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_192);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
x_206 = lean_ctor_get(x_192, 1);
x_207 = lean_ctor_get(x_192, 2);
x_208 = lean_ctor_get(x_192, 3);
lean_dec(x_208);
x_209 = lean_ctor_get(x_192, 0);
lean_dec(x_209);
x_210 = !lean_is_exclusive(x_195);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_216; 
x_211 = lean_ctor_get(x_195, 0);
x_212 = lean_ctor_get(x_195, 1);
x_213 = lean_ctor_get(x_195, 2);
x_214 = lean_ctor_get(x_195, 3);
x_215 = 1;
lean_ctor_set(x_195, 3, x_194);
lean_ctor_set(x_195, 2, x_36);
lean_ctor_set(x_195, 1, x_35);
lean_ctor_set(x_195, 0, x_34);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_215);
lean_ctor_set(x_192, 3, x_214);
lean_ctor_set(x_192, 2, x_213);
lean_ctor_set(x_192, 1, x_212);
lean_ctor_set(x_192, 0, x_211);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_215);
x_216 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_207);
lean_ctor_set(x_2, 1, x_206);
lean_ctor_set(x_2, 0, x_195);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_216);
return x_2;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; uint8_t x_223; 
x_217 = lean_ctor_get(x_195, 0);
x_218 = lean_ctor_get(x_195, 1);
x_219 = lean_ctor_get(x_195, 2);
x_220 = lean_ctor_get(x_195, 3);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_195);
x_221 = 1;
x_222 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_222, 0, x_34);
lean_ctor_set(x_222, 1, x_35);
lean_ctor_set(x_222, 2, x_36);
lean_ctor_set(x_222, 3, x_194);
lean_ctor_set_uint8(x_222, sizeof(void*)*4, x_221);
lean_ctor_set(x_192, 3, x_220);
lean_ctor_set(x_192, 2, x_219);
lean_ctor_set(x_192, 1, x_218);
lean_ctor_set(x_192, 0, x_217);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_221);
x_223 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_207);
lean_ctor_set(x_2, 1, x_206);
lean_ctor_set(x_2, 0, x_222);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_223);
return x_2;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_224 = lean_ctor_get(x_192, 1);
x_225 = lean_ctor_get(x_192, 2);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_192);
x_226 = lean_ctor_get(x_195, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_195, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_195, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_195, 3);
lean_inc(x_229);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 x_230 = x_195;
} else {
 lean_dec_ref(x_195);
 x_230 = lean_box(0);
}
x_231 = 1;
if (lean_is_scalar(x_230)) {
 x_232 = lean_alloc_ctor(1, 4, 1);
} else {
 x_232 = x_230;
}
lean_ctor_set(x_232, 0, x_34);
lean_ctor_set(x_232, 1, x_35);
lean_ctor_set(x_232, 2, x_36);
lean_ctor_set(x_232, 3, x_194);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_231);
x_233 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_233, 0, x_226);
lean_ctor_set(x_233, 1, x_227);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_229);
lean_ctor_set_uint8(x_233, sizeof(void*)*4, x_231);
x_234 = 0;
lean_ctor_set(x_2, 3, x_233);
lean_ctor_set(x_2, 2, x_225);
lean_ctor_set(x_2, 1, x_224);
lean_ctor_set(x_2, 0, x_232);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_234);
return x_2;
}
}
else
{
uint8_t x_235; 
lean_free_object(x_2);
x_235 = !lean_is_exclusive(x_195);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_195, 3);
lean_dec(x_236);
x_237 = lean_ctor_get(x_195, 2);
lean_dec(x_237);
x_238 = lean_ctor_get(x_195, 1);
lean_dec(x_238);
x_239 = lean_ctor_get(x_195, 0);
lean_dec(x_239);
x_240 = 1;
lean_ctor_set(x_195, 3, x_192);
lean_ctor_set(x_195, 2, x_36);
lean_ctor_set(x_195, 1, x_35);
lean_ctor_set(x_195, 0, x_34);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_240);
return x_195;
}
else
{
uint8_t x_241; lean_object* x_242; 
lean_dec(x_195);
x_241 = 1;
x_242 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_242, 0, x_34);
lean_ctor_set(x_242, 1, x_35);
lean_ctor_set(x_242, 2, x_36);
lean_ctor_set(x_242, 3, x_192);
lean_ctor_set_uint8(x_242, sizeof(void*)*4, x_241);
return x_242;
}
}
}
}
else
{
uint8_t x_243; 
x_243 = lean_ctor_get_uint8(x_194, sizeof(void*)*4);
if (x_243 == 0)
{
uint8_t x_244; 
x_244 = !lean_is_exclusive(x_192);
if (x_244 == 0)
{
lean_object* x_245; uint8_t x_246; 
x_245 = lean_ctor_get(x_192, 0);
lean_dec(x_245);
x_246 = !lean_is_exclusive(x_194);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; 
x_247 = lean_ctor_get(x_194, 0);
x_248 = lean_ctor_get(x_194, 1);
x_249 = lean_ctor_get(x_194, 2);
x_250 = lean_ctor_get(x_194, 3);
x_251 = 1;
lean_ctor_set(x_194, 3, x_247);
lean_ctor_set(x_194, 2, x_36);
lean_ctor_set(x_194, 1, x_35);
lean_ctor_set(x_194, 0, x_34);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_251);
lean_ctor_set(x_192, 0, x_250);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_251);
x_252 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_249);
lean_ctor_set(x_2, 1, x_248);
lean_ctor_set(x_2, 0, x_194);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_252);
return x_2;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; lean_object* x_258; uint8_t x_259; 
x_253 = lean_ctor_get(x_194, 0);
x_254 = lean_ctor_get(x_194, 1);
x_255 = lean_ctor_get(x_194, 2);
x_256 = lean_ctor_get(x_194, 3);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_194);
x_257 = 1;
x_258 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_258, 0, x_34);
lean_ctor_set(x_258, 1, x_35);
lean_ctor_set(x_258, 2, x_36);
lean_ctor_set(x_258, 3, x_253);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_257);
lean_ctor_set(x_192, 0, x_256);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_257);
x_259 = 0;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set(x_2, 2, x_255);
lean_ctor_set(x_2, 1, x_254);
lean_ctor_set(x_2, 0, x_258);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_259);
return x_2;
}
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_260 = lean_ctor_get(x_192, 1);
x_261 = lean_ctor_get(x_192, 2);
x_262 = lean_ctor_get(x_192, 3);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_192);
x_263 = lean_ctor_get(x_194, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_194, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_194, 2);
lean_inc(x_265);
x_266 = lean_ctor_get(x_194, 3);
lean_inc(x_266);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_267 = x_194;
} else {
 lean_dec_ref(x_194);
 x_267 = lean_box(0);
}
x_268 = 1;
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(1, 4, 1);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_34);
lean_ctor_set(x_269, 1, x_35);
lean_ctor_set(x_269, 2, x_36);
lean_ctor_set(x_269, 3, x_263);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
x_270 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_270, 0, x_266);
lean_ctor_set(x_270, 1, x_260);
lean_ctor_set(x_270, 2, x_261);
lean_ctor_set(x_270, 3, x_262);
lean_ctor_set_uint8(x_270, sizeof(void*)*4, x_268);
x_271 = 0;
lean_ctor_set(x_2, 3, x_270);
lean_ctor_set(x_2, 2, x_265);
lean_ctor_set(x_2, 1, x_264);
lean_ctor_set(x_2, 0, x_269);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_271);
return x_2;
}
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_192, 3);
lean_inc(x_272);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
lean_free_object(x_2);
x_273 = !lean_is_exclusive(x_194);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_194, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_194, 2);
lean_dec(x_275);
x_276 = lean_ctor_get(x_194, 1);
lean_dec(x_276);
x_277 = lean_ctor_get(x_194, 0);
lean_dec(x_277);
x_278 = 1;
lean_ctor_set(x_194, 3, x_192);
lean_ctor_set(x_194, 2, x_36);
lean_ctor_set(x_194, 1, x_35);
lean_ctor_set(x_194, 0, x_34);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_278);
return x_194;
}
else
{
uint8_t x_279; lean_object* x_280; 
lean_dec(x_194);
x_279 = 1;
x_280 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_280, 0, x_34);
lean_ctor_set(x_280, 1, x_35);
lean_ctor_set(x_280, 2, x_36);
lean_ctor_set(x_280, 3, x_192);
lean_ctor_set_uint8(x_280, sizeof(void*)*4, x_279);
return x_280;
}
}
else
{
uint8_t x_281; 
x_281 = lean_ctor_get_uint8(x_272, sizeof(void*)*4);
if (x_281 == 0)
{
uint8_t x_282; 
lean_free_object(x_2);
x_282 = !lean_is_exclusive(x_192);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_283 = lean_ctor_get(x_192, 3);
lean_dec(x_283);
x_284 = lean_ctor_get(x_192, 0);
lean_dec(x_284);
x_285 = !lean_is_exclusive(x_272);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint8_t x_290; uint8_t x_291; 
x_286 = lean_ctor_get(x_272, 0);
x_287 = lean_ctor_get(x_272, 1);
x_288 = lean_ctor_get(x_272, 2);
x_289 = lean_ctor_get(x_272, 3);
x_290 = 1;
lean_inc(x_194);
lean_ctor_set(x_272, 3, x_194);
lean_ctor_set(x_272, 2, x_36);
lean_ctor_set(x_272, 1, x_35);
lean_ctor_set(x_272, 0, x_34);
x_291 = !lean_is_exclusive(x_194);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_292 = lean_ctor_get(x_194, 3);
lean_dec(x_292);
x_293 = lean_ctor_get(x_194, 2);
lean_dec(x_293);
x_294 = lean_ctor_get(x_194, 1);
lean_dec(x_294);
x_295 = lean_ctor_get(x_194, 0);
lean_dec(x_295);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_290);
lean_ctor_set(x_194, 3, x_289);
lean_ctor_set(x_194, 2, x_288);
lean_ctor_set(x_194, 1, x_287);
lean_ctor_set(x_194, 0, x_286);
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_290);
x_296 = 0;
lean_ctor_set(x_192, 3, x_194);
lean_ctor_set(x_192, 0, x_272);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_296);
return x_192;
}
else
{
lean_object* x_297; uint8_t x_298; 
lean_dec(x_194);
lean_ctor_set_uint8(x_272, sizeof(void*)*4, x_290);
x_297 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_297, 0, x_286);
lean_ctor_set(x_297, 1, x_287);
lean_ctor_set(x_297, 2, x_288);
lean_ctor_set(x_297, 3, x_289);
lean_ctor_set_uint8(x_297, sizeof(void*)*4, x_290);
x_298 = 0;
lean_ctor_set(x_192, 3, x_297);
lean_ctor_set(x_192, 0, x_272);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_298);
return x_192;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; 
x_299 = lean_ctor_get(x_272, 0);
x_300 = lean_ctor_get(x_272, 1);
x_301 = lean_ctor_get(x_272, 2);
x_302 = lean_ctor_get(x_272, 3);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_272);
x_303 = 1;
lean_inc(x_194);
x_304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_304, 0, x_34);
lean_ctor_set(x_304, 1, x_35);
lean_ctor_set(x_304, 2, x_36);
lean_ctor_set(x_304, 3, x_194);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_305 = x_194;
} else {
 lean_dec_ref(x_194);
 x_305 = lean_box(0);
}
lean_ctor_set_uint8(x_304, sizeof(void*)*4, x_303);
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(1, 4, 1);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_299);
lean_ctor_set(x_306, 1, x_300);
lean_ctor_set(x_306, 2, x_301);
lean_ctor_set(x_306, 3, x_302);
lean_ctor_set_uint8(x_306, sizeof(void*)*4, x_303);
x_307 = 0;
lean_ctor_set(x_192, 3, x_306);
lean_ctor_set(x_192, 0, x_304);
lean_ctor_set_uint8(x_192, sizeof(void*)*4, x_307);
return x_192;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; lean_object* x_320; 
x_308 = lean_ctor_get(x_192, 1);
x_309 = lean_ctor_get(x_192, 2);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_192);
x_310 = lean_ctor_get(x_272, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_272, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_272, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_272, 3);
lean_inc(x_313);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 lean_ctor_release(x_272, 2);
 lean_ctor_release(x_272, 3);
 x_314 = x_272;
} else {
 lean_dec_ref(x_272);
 x_314 = lean_box(0);
}
x_315 = 1;
lean_inc(x_194);
if (lean_is_scalar(x_314)) {
 x_316 = lean_alloc_ctor(1, 4, 1);
} else {
 x_316 = x_314;
}
lean_ctor_set(x_316, 0, x_34);
lean_ctor_set(x_316, 1, x_35);
lean_ctor_set(x_316, 2, x_36);
lean_ctor_set(x_316, 3, x_194);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_317 = x_194;
} else {
 lean_dec_ref(x_194);
 x_317 = lean_box(0);
}
lean_ctor_set_uint8(x_316, sizeof(void*)*4, x_315);
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 4, 1);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_310);
lean_ctor_set(x_318, 1, x_311);
lean_ctor_set(x_318, 2, x_312);
lean_ctor_set(x_318, 3, x_313);
lean_ctor_set_uint8(x_318, sizeof(void*)*4, x_315);
x_319 = 0;
x_320 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_320, 0, x_316);
lean_ctor_set(x_320, 1, x_308);
lean_ctor_set(x_320, 2, x_309);
lean_ctor_set(x_320, 3, x_318);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_319);
return x_320;
}
}
else
{
uint8_t x_321; 
x_321 = !lean_is_exclusive(x_192);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_322 = lean_ctor_get(x_192, 3);
lean_dec(x_322);
x_323 = lean_ctor_get(x_192, 0);
lean_dec(x_323);
x_324 = !lean_is_exclusive(x_194);
if (x_324 == 0)
{
uint8_t x_325; 
lean_ctor_set_uint8(x_194, sizeof(void*)*4, x_281);
x_325 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_325);
return x_2;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_326 = lean_ctor_get(x_194, 0);
x_327 = lean_ctor_get(x_194, 1);
x_328 = lean_ctor_get(x_194, 2);
x_329 = lean_ctor_get(x_194, 3);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_194);
x_330 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_330, 0, x_326);
lean_ctor_set(x_330, 1, x_327);
lean_ctor_set(x_330, 2, x_328);
lean_ctor_set(x_330, 3, x_329);
lean_ctor_set_uint8(x_330, sizeof(void*)*4, x_281);
lean_ctor_set(x_192, 0, x_330);
x_331 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_331);
return x_2;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_341; 
x_332 = lean_ctor_get(x_192, 1);
x_333 = lean_ctor_get(x_192, 2);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_192);
x_334 = lean_ctor_get(x_194, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_194, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_194, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_194, 3);
lean_inc(x_337);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 lean_ctor_release(x_194, 3);
 x_338 = x_194;
} else {
 lean_dec_ref(x_194);
 x_338 = lean_box(0);
}
if (lean_is_scalar(x_338)) {
 x_339 = lean_alloc_ctor(1, 4, 1);
} else {
 x_339 = x_338;
}
lean_ctor_set(x_339, 0, x_334);
lean_ctor_set(x_339, 1, x_335);
lean_ctor_set(x_339, 2, x_336);
lean_ctor_set(x_339, 3, x_337);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_281);
x_340 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_332);
lean_ctor_set(x_340, 2, x_333);
lean_ctor_set(x_340, 3, x_272);
lean_ctor_set_uint8(x_340, sizeof(void*)*4, x_193);
x_341 = 1;
lean_ctor_set(x_2, 3, x_340);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_341);
return x_2;
}
}
}
}
}
}
else
{
uint8_t x_342; 
x_342 = 1;
lean_ctor_set(x_2, 3, x_192);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_342);
return x_2;
}
}
}
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_347; 
x_343 = lean_ctor_get(x_2, 0);
x_344 = lean_ctor_get(x_2, 1);
x_345 = lean_ctor_get(x_2, 2);
x_346 = lean_ctor_get(x_2, 3);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_2);
x_347 = l_Lean_Name_quickCmp(x_3, x_344);
switch (x_347) {
case 0:
{
lean_object* x_348; uint8_t x_349; 
x_348 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_343, x_3, x_4);
x_349 = lean_ctor_get_uint8(x_348, sizeof(void*)*4);
if (x_349 == 0)
{
lean_object* x_350; 
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; 
x_351 = lean_ctor_get(x_348, 3);
lean_inc(x_351);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; 
x_352 = lean_ctor_get(x_348, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_348, 2);
lean_inc(x_353);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_354 = x_348;
} else {
 lean_dec_ref(x_348);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 4, 1);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_351);
lean_ctor_set(x_355, 1, x_352);
lean_ctor_set(x_355, 2, x_353);
lean_ctor_set(x_355, 3, x_351);
lean_ctor_set_uint8(x_355, sizeof(void*)*4, x_349);
x_356 = 1;
x_357 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_344);
lean_ctor_set(x_357, 2, x_345);
lean_ctor_set(x_357, 3, x_346);
lean_ctor_set_uint8(x_357, sizeof(void*)*4, x_356);
return x_357;
}
else
{
uint8_t x_358; 
x_358 = lean_ctor_get_uint8(x_351, sizeof(void*)*4);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; uint8_t x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; 
x_359 = lean_ctor_get(x_348, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_348, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_361 = x_348;
} else {
 lean_dec_ref(x_348);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_351, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_351, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_351, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_351, 3);
lean_inc(x_365);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_366 = x_351;
} else {
 lean_dec_ref(x_351);
 x_366 = lean_box(0);
}
x_367 = 1;
if (lean_is_scalar(x_366)) {
 x_368 = lean_alloc_ctor(1, 4, 1);
} else {
 x_368 = x_366;
}
lean_ctor_set(x_368, 0, x_350);
lean_ctor_set(x_368, 1, x_359);
lean_ctor_set(x_368, 2, x_360);
lean_ctor_set(x_368, 3, x_362);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_367);
if (lean_is_scalar(x_361)) {
 x_369 = lean_alloc_ctor(1, 4, 1);
} else {
 x_369 = x_361;
}
lean_ctor_set(x_369, 0, x_365);
lean_ctor_set(x_369, 1, x_344);
lean_ctor_set(x_369, 2, x_345);
lean_ctor_set(x_369, 3, x_346);
lean_ctor_set_uint8(x_369, sizeof(void*)*4, x_367);
x_370 = 0;
x_371 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_371, 0, x_368);
lean_ctor_set(x_371, 1, x_363);
lean_ctor_set(x_371, 2, x_364);
lean_ctor_set(x_371, 3, x_369);
lean_ctor_set_uint8(x_371, sizeof(void*)*4, x_370);
return x_371;
}
else
{
lean_object* x_372; uint8_t x_373; lean_object* x_374; 
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 lean_ctor_release(x_351, 2);
 lean_ctor_release(x_351, 3);
 x_372 = x_351;
} else {
 lean_dec_ref(x_351);
 x_372 = lean_box(0);
}
x_373 = 1;
if (lean_is_scalar(x_372)) {
 x_374 = lean_alloc_ctor(1, 4, 1);
} else {
 x_374 = x_372;
}
lean_ctor_set(x_374, 0, x_348);
lean_ctor_set(x_374, 1, x_344);
lean_ctor_set(x_374, 2, x_345);
lean_ctor_set(x_374, 3, x_346);
lean_ctor_set_uint8(x_374, sizeof(void*)*4, x_373);
return x_374;
}
}
}
else
{
uint8_t x_375; 
x_375 = lean_ctor_get_uint8(x_350, sizeof(void*)*4);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; 
x_376 = lean_ctor_get(x_348, 1);
lean_inc(x_376);
x_377 = lean_ctor_get(x_348, 2);
lean_inc(x_377);
x_378 = lean_ctor_get(x_348, 3);
lean_inc(x_378);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_379 = x_348;
} else {
 lean_dec_ref(x_348);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_350, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_350, 1);
lean_inc(x_381);
x_382 = lean_ctor_get(x_350, 2);
lean_inc(x_382);
x_383 = lean_ctor_get(x_350, 3);
lean_inc(x_383);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_384 = x_350;
} else {
 lean_dec_ref(x_350);
 x_384 = lean_box(0);
}
x_385 = 1;
if (lean_is_scalar(x_384)) {
 x_386 = lean_alloc_ctor(1, 4, 1);
} else {
 x_386 = x_384;
}
lean_ctor_set(x_386, 0, x_380);
lean_ctor_set(x_386, 1, x_381);
lean_ctor_set(x_386, 2, x_382);
lean_ctor_set(x_386, 3, x_383);
lean_ctor_set_uint8(x_386, sizeof(void*)*4, x_385);
if (lean_is_scalar(x_379)) {
 x_387 = lean_alloc_ctor(1, 4, 1);
} else {
 x_387 = x_379;
}
lean_ctor_set(x_387, 0, x_378);
lean_ctor_set(x_387, 1, x_344);
lean_ctor_set(x_387, 2, x_345);
lean_ctor_set(x_387, 3, x_346);
lean_ctor_set_uint8(x_387, sizeof(void*)*4, x_385);
x_388 = 0;
x_389 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_376);
lean_ctor_set(x_389, 2, x_377);
lean_ctor_set(x_389, 3, x_387);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_388);
return x_389;
}
else
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_348, 3);
lean_inc(x_390);
if (lean_obj_tag(x_390) == 0)
{
lean_object* x_391; uint8_t x_392; lean_object* x_393; 
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_391 = x_350;
} else {
 lean_dec_ref(x_350);
 x_391 = lean_box(0);
}
x_392 = 1;
if (lean_is_scalar(x_391)) {
 x_393 = lean_alloc_ctor(1, 4, 1);
} else {
 x_393 = x_391;
}
lean_ctor_set(x_393, 0, x_348);
lean_ctor_set(x_393, 1, x_344);
lean_ctor_set(x_393, 2, x_345);
lean_ctor_set(x_393, 3, x_346);
lean_ctor_set_uint8(x_393, sizeof(void*)*4, x_392);
return x_393;
}
else
{
uint8_t x_394; 
x_394 = lean_ctor_get_uint8(x_390, sizeof(void*)*4);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; 
x_395 = lean_ctor_get(x_348, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_348, 2);
lean_inc(x_396);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_397 = x_348;
} else {
 lean_dec_ref(x_348);
 x_397 = lean_box(0);
}
x_398 = lean_ctor_get(x_390, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_390, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_390, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_390, 3);
lean_inc(x_401);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 lean_ctor_release(x_390, 2);
 lean_ctor_release(x_390, 3);
 x_402 = x_390;
} else {
 lean_dec_ref(x_390);
 x_402 = lean_box(0);
}
x_403 = 1;
lean_inc(x_350);
if (lean_is_scalar(x_402)) {
 x_404 = lean_alloc_ctor(1, 4, 1);
} else {
 x_404 = x_402;
}
lean_ctor_set(x_404, 0, x_350);
lean_ctor_set(x_404, 1, x_395);
lean_ctor_set(x_404, 2, x_396);
lean_ctor_set(x_404, 3, x_398);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_405 = x_350;
} else {
 lean_dec_ref(x_350);
 x_405 = lean_box(0);
}
lean_ctor_set_uint8(x_404, sizeof(void*)*4, x_403);
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 4, 1);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_401);
lean_ctor_set(x_406, 1, x_344);
lean_ctor_set(x_406, 2, x_345);
lean_ctor_set(x_406, 3, x_346);
lean_ctor_set_uint8(x_406, sizeof(void*)*4, x_403);
x_407 = 0;
if (lean_is_scalar(x_397)) {
 x_408 = lean_alloc_ctor(1, 4, 1);
} else {
 x_408 = x_397;
}
lean_ctor_set(x_408, 0, x_404);
lean_ctor_set(x_408, 1, x_399);
lean_ctor_set(x_408, 2, x_400);
lean_ctor_set(x_408, 3, x_406);
lean_ctor_set_uint8(x_408, sizeof(void*)*4, x_407);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_409 = lean_ctor_get(x_348, 1);
lean_inc(x_409);
x_410 = lean_ctor_get(x_348, 2);
lean_inc(x_410);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 x_411 = x_348;
} else {
 lean_dec_ref(x_348);
 x_411 = lean_box(0);
}
x_412 = lean_ctor_get(x_350, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_350, 1);
lean_inc(x_413);
x_414 = lean_ctor_get(x_350, 2);
lean_inc(x_414);
x_415 = lean_ctor_get(x_350, 3);
lean_inc(x_415);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 x_416 = x_350;
} else {
 lean_dec_ref(x_350);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 4, 1);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_412);
lean_ctor_set(x_417, 1, x_413);
lean_ctor_set(x_417, 2, x_414);
lean_ctor_set(x_417, 3, x_415);
lean_ctor_set_uint8(x_417, sizeof(void*)*4, x_394);
if (lean_is_scalar(x_411)) {
 x_418 = lean_alloc_ctor(1, 4, 1);
} else {
 x_418 = x_411;
}
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_409);
lean_ctor_set(x_418, 2, x_410);
lean_ctor_set(x_418, 3, x_390);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_349);
x_419 = 1;
x_420 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_344);
lean_ctor_set(x_420, 2, x_345);
lean_ctor_set(x_420, 3, x_346);
lean_ctor_set_uint8(x_420, sizeof(void*)*4, x_419);
return x_420;
}
}
}
}
}
else
{
uint8_t x_421; lean_object* x_422; 
x_421 = 1;
x_422 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_422, 0, x_348);
lean_ctor_set(x_422, 1, x_344);
lean_ctor_set(x_422, 2, x_345);
lean_ctor_set(x_422, 3, x_346);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
return x_422;
}
}
case 1:
{
uint8_t x_423; lean_object* x_424; 
lean_dec(x_345);
lean_dec(x_344);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_343);
lean_ctor_set(x_424, 1, x_3);
lean_ctor_set(x_424, 2, x_4);
lean_ctor_set(x_424, 3, x_346);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
default: 
{
lean_object* x_425; uint8_t x_426; 
x_425 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_346, x_3, x_4);
x_426 = lean_ctor_get_uint8(x_425, sizeof(void*)*4);
if (x_426 == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_425, 0);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; 
x_428 = lean_ctor_get(x_425, 3);
lean_inc(x_428);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; uint8_t x_433; lean_object* x_434; 
x_429 = lean_ctor_get(x_425, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_425, 2);
lean_inc(x_430);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_431 = x_425;
} else {
 lean_dec_ref(x_425);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 4, 1);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_428);
lean_ctor_set(x_432, 1, x_429);
lean_ctor_set(x_432, 2, x_430);
lean_ctor_set(x_432, 3, x_428);
lean_ctor_set_uint8(x_432, sizeof(void*)*4, x_426);
x_433 = 1;
x_434 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_434, 0, x_343);
lean_ctor_set(x_434, 1, x_344);
lean_ctor_set(x_434, 2, x_345);
lean_ctor_set(x_434, 3, x_432);
lean_ctor_set_uint8(x_434, sizeof(void*)*4, x_433);
return x_434;
}
else
{
uint8_t x_435; 
x_435 = lean_ctor_get_uint8(x_428, sizeof(void*)*4);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; lean_object* x_448; 
x_436 = lean_ctor_get(x_425, 1);
lean_inc(x_436);
x_437 = lean_ctor_get(x_425, 2);
lean_inc(x_437);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_438 = x_425;
} else {
 lean_dec_ref(x_425);
 x_438 = lean_box(0);
}
x_439 = lean_ctor_get(x_428, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_428, 1);
lean_inc(x_440);
x_441 = lean_ctor_get(x_428, 2);
lean_inc(x_441);
x_442 = lean_ctor_get(x_428, 3);
lean_inc(x_442);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_443 = x_428;
} else {
 lean_dec_ref(x_428);
 x_443 = lean_box(0);
}
x_444 = 1;
if (lean_is_scalar(x_443)) {
 x_445 = lean_alloc_ctor(1, 4, 1);
} else {
 x_445 = x_443;
}
lean_ctor_set(x_445, 0, x_343);
lean_ctor_set(x_445, 1, x_344);
lean_ctor_set(x_445, 2, x_345);
lean_ctor_set(x_445, 3, x_427);
lean_ctor_set_uint8(x_445, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_438)) {
 x_446 = lean_alloc_ctor(1, 4, 1);
} else {
 x_446 = x_438;
}
lean_ctor_set(x_446, 0, x_439);
lean_ctor_set(x_446, 1, x_440);
lean_ctor_set(x_446, 2, x_441);
lean_ctor_set(x_446, 3, x_442);
lean_ctor_set_uint8(x_446, sizeof(void*)*4, x_444);
x_447 = 0;
x_448 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_436);
lean_ctor_set(x_448, 2, x_437);
lean_ctor_set(x_448, 3, x_446);
lean_ctor_set_uint8(x_448, sizeof(void*)*4, x_447);
return x_448;
}
else
{
lean_object* x_449; uint8_t x_450; lean_object* x_451; 
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 x_449 = x_428;
} else {
 lean_dec_ref(x_428);
 x_449 = lean_box(0);
}
x_450 = 1;
if (lean_is_scalar(x_449)) {
 x_451 = lean_alloc_ctor(1, 4, 1);
} else {
 x_451 = x_449;
}
lean_ctor_set(x_451, 0, x_343);
lean_ctor_set(x_451, 1, x_344);
lean_ctor_set(x_451, 2, x_345);
lean_ctor_set(x_451, 3, x_425);
lean_ctor_set_uint8(x_451, sizeof(void*)*4, x_450);
return x_451;
}
}
}
else
{
uint8_t x_452; 
x_452 = lean_ctor_get_uint8(x_427, sizeof(void*)*4);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; 
x_453 = lean_ctor_get(x_425, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_425, 2);
lean_inc(x_454);
x_455 = lean_ctor_get(x_425, 3);
lean_inc(x_455);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_456 = x_425;
} else {
 lean_dec_ref(x_425);
 x_456 = lean_box(0);
}
x_457 = lean_ctor_get(x_427, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_427, 1);
lean_inc(x_458);
x_459 = lean_ctor_get(x_427, 2);
lean_inc(x_459);
x_460 = lean_ctor_get(x_427, 3);
lean_inc(x_460);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_461 = x_427;
} else {
 lean_dec_ref(x_427);
 x_461 = lean_box(0);
}
x_462 = 1;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_343);
lean_ctor_set(x_463, 1, x_344);
lean_ctor_set(x_463, 2, x_345);
lean_ctor_set(x_463, 3, x_457);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_462);
if (lean_is_scalar(x_456)) {
 x_464 = lean_alloc_ctor(1, 4, 1);
} else {
 x_464 = x_456;
}
lean_ctor_set(x_464, 0, x_460);
lean_ctor_set(x_464, 1, x_453);
lean_ctor_set(x_464, 2, x_454);
lean_ctor_set(x_464, 3, x_455);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_462);
x_465 = 0;
x_466 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_466, 0, x_463);
lean_ctor_set(x_466, 1, x_458);
lean_ctor_set(x_466, 2, x_459);
lean_ctor_set(x_466, 3, x_464);
lean_ctor_set_uint8(x_466, sizeof(void*)*4, x_465);
return x_466;
}
else
{
lean_object* x_467; 
x_467 = lean_ctor_get(x_425, 3);
lean_inc(x_467);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; uint8_t x_469; lean_object* x_470; 
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_468 = x_427;
} else {
 lean_dec_ref(x_427);
 x_468 = lean_box(0);
}
x_469 = 1;
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 4, 1);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_343);
lean_ctor_set(x_470, 1, x_344);
lean_ctor_set(x_470, 2, x_345);
lean_ctor_set(x_470, 3, x_425);
lean_ctor_set_uint8(x_470, sizeof(void*)*4, x_469);
return x_470;
}
else
{
uint8_t x_471; 
x_471 = lean_ctor_get_uint8(x_467, sizeof(void*)*4);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; uint8_t x_484; lean_object* x_485; 
x_472 = lean_ctor_get(x_425, 1);
lean_inc(x_472);
x_473 = lean_ctor_get(x_425, 2);
lean_inc(x_473);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_474 = x_425;
} else {
 lean_dec_ref(x_425);
 x_474 = lean_box(0);
}
x_475 = lean_ctor_get(x_467, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_467, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_467, 2);
lean_inc(x_477);
x_478 = lean_ctor_get(x_467, 3);
lean_inc(x_478);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 x_479 = x_467;
} else {
 lean_dec_ref(x_467);
 x_479 = lean_box(0);
}
x_480 = 1;
lean_inc(x_427);
if (lean_is_scalar(x_479)) {
 x_481 = lean_alloc_ctor(1, 4, 1);
} else {
 x_481 = x_479;
}
lean_ctor_set(x_481, 0, x_343);
lean_ctor_set(x_481, 1, x_344);
lean_ctor_set(x_481, 2, x_345);
lean_ctor_set(x_481, 3, x_427);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_482 = x_427;
} else {
 lean_dec_ref(x_427);
 x_482 = lean_box(0);
}
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_480);
if (lean_is_scalar(x_482)) {
 x_483 = lean_alloc_ctor(1, 4, 1);
} else {
 x_483 = x_482;
}
lean_ctor_set(x_483, 0, x_475);
lean_ctor_set(x_483, 1, x_476);
lean_ctor_set(x_483, 2, x_477);
lean_ctor_set(x_483, 3, x_478);
lean_ctor_set_uint8(x_483, sizeof(void*)*4, x_480);
x_484 = 0;
if (lean_is_scalar(x_474)) {
 x_485 = lean_alloc_ctor(1, 4, 1);
} else {
 x_485 = x_474;
}
lean_ctor_set(x_485, 0, x_481);
lean_ctor_set(x_485, 1, x_472);
lean_ctor_set(x_485, 2, x_473);
lean_ctor_set(x_485, 3, x_483);
lean_ctor_set_uint8(x_485, sizeof(void*)*4, x_484);
return x_485;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; lean_object* x_497; 
x_486 = lean_ctor_get(x_425, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_425, 2);
lean_inc(x_487);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_488 = x_425;
} else {
 lean_dec_ref(x_425);
 x_488 = lean_box(0);
}
x_489 = lean_ctor_get(x_427, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_427, 1);
lean_inc(x_490);
x_491 = lean_ctor_get(x_427, 2);
lean_inc(x_491);
x_492 = lean_ctor_get(x_427, 3);
lean_inc(x_492);
if (lean_is_exclusive(x_427)) {
 lean_ctor_release(x_427, 0);
 lean_ctor_release(x_427, 1);
 lean_ctor_release(x_427, 2);
 lean_ctor_release(x_427, 3);
 x_493 = x_427;
} else {
 lean_dec_ref(x_427);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 4, 1);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_489);
lean_ctor_set(x_494, 1, x_490);
lean_ctor_set(x_494, 2, x_491);
lean_ctor_set(x_494, 3, x_492);
lean_ctor_set_uint8(x_494, sizeof(void*)*4, x_471);
if (lean_is_scalar(x_488)) {
 x_495 = lean_alloc_ctor(1, 4, 1);
} else {
 x_495 = x_488;
}
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_486);
lean_ctor_set(x_495, 2, x_487);
lean_ctor_set(x_495, 3, x_467);
lean_ctor_set_uint8(x_495, sizeof(void*)*4, x_426);
x_496 = 1;
x_497 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_497, 0, x_343);
lean_ctor_set(x_497, 1, x_344);
lean_ctor_set(x_497, 2, x_345);
lean_ctor_set(x_497, 3, x_495);
lean_ctor_set_uint8(x_497, sizeof(void*)*4, x_496);
return x_497;
}
}
}
}
}
else
{
uint8_t x_498; lean_object* x_499; 
x_498 = 1;
x_499 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_499, 0, x_343);
lean_ctor_set(x_499, 1, x_344);
lean_ctor_set(x_499, 2, x_345);
lean_ctor_set(x_499, 3, x_425);
lean_ctor_set_uint8(x_499, sizeof(void*)*4, x_498);
return x_499;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_decodeTargetDecls_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_RBNode_isRed___rarg(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_2, x_3, x_4);
x_8 = l_Lean_RBNode_setBlack___rarg(x_7);
return x_8;
}
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": target '", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' was already defined as a '", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("', but then redefined as a '", 28, 28);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_15; 
x_15 = lean_usize_dec_eq(x_5, x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_129; 
x_16 = lean_array_uget(x_4, x_5);
if (lean_obj_tag(x_16) == 6)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_16, 1);
lean_inc(x_136);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_17 = x_137;
x_18 = x_8;
goto block_128;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_16, 0);
lean_inc(x_138);
x_139 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_129 = x_140;
goto block_135;
}
block_128:
{
if (lean_obj_tag(x_17) == 0)
{
lean_dec(x_16);
x_9 = x_7;
x_10 = x_18;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lake_LeanOption_decodeToml___closed__10;
x_21 = lean_box(0);
lean_inc(x_19);
x_22 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Array_append___rarg(x_18, x_23);
lean_dec(x_23);
x_9 = x_7;
x_10 = x_24;
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
x_26 = l_Lake_stringToLegalOrSimpleName(x_25);
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
x_30 = l_Lake_RBNode_dFind___at_Lake_decodeTargetDecls_go___spec__1(x_1, x_29, x_26);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_26);
x_31 = lean_apply_2(x_3, x_26, x_19);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_26);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Array_append___rarg(x_18, x_32);
lean_dec(x_32);
x_9 = x_7;
x_10 = x_33;
goto block_14;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
lean_inc(x_2);
lean_inc(x_26);
lean_inc(x_1);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_26);
lean_ctor_set(x_35, 2, x_2);
lean_ctor_set(x_35, 3, x_34);
lean_inc(x_35);
x_36 = lean_array_push(x_28, x_35);
x_37 = l_Lean_RBNode_insert___at_Lake_decodeTargetDecls_go___spec__2(x_1, x_29, x_26, x_35);
lean_ctor_set(x_7, 1, x_37);
lean_ctor_set(x_7, 0, x_36);
x_9 = x_7;
x_10 = x_18;
goto block_14;
}
}
else
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_19);
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
x_39 = 1;
x_40 = l_Lake_StrPat_decodeToml___closed__6;
lean_inc(x_1);
x_41 = l_Lean_Name_toString(x_1, x_39, x_40);
x_42 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_43 = lean_string_append(x_42, x_41);
lean_dec(x_41);
x_44 = l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__1;
x_45 = lean_string_append(x_43, x_44);
x_46 = l_Lean_Name_toString(x_26, x_39, x_40);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
x_48 = l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__2;
x_49 = lean_string_append(x_47, x_48);
x_50 = lean_ctor_get(x_38, 2);
lean_inc(x_50);
lean_dec(x_38);
x_51 = l_Lean_Name_toString(x_50, x_39, x_40);
x_52 = lean_string_append(x_49, x_51);
lean_dec(x_51);
x_53 = l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__3;
x_54 = lean_string_append(x_52, x_53);
lean_inc(x_2);
x_55 = l_Lean_Name_toString(x_2, x_39, x_40);
x_56 = lean_string_append(x_54, x_55);
lean_dec(x_55);
x_57 = l_Lake_StrPat_decodeToml___closed__8;
x_58 = lean_string_append(x_56, x_57);
switch (lean_obj_tag(x_16)) {
case 0:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_16);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_16, 1);
lean_dec(x_60);
lean_ctor_set(x_16, 1, x_58);
x_61 = lean_array_push(x_18, x_16);
x_9 = x_7;
x_10 = x_61;
goto block_14;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_16, 0);
lean_inc(x_62);
lean_dec(x_16);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_58);
x_64 = lean_array_push(x_18, x_63);
x_9 = x_7;
x_10 = x_64;
goto block_14;
}
}
case 2:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_16, 0);
lean_inc(x_65);
lean_dec(x_16);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_58);
x_67 = lean_array_push(x_18, x_66);
x_9 = x_7;
x_10 = x_67;
goto block_14;
}
case 3:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_16, 0);
lean_inc(x_68);
lean_dec(x_16);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_58);
x_70 = lean_array_push(x_18, x_69);
x_9 = x_7;
x_10 = x_70;
goto block_14;
}
default: 
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_16);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_16, 1);
lean_dec(x_72);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 1, x_58);
x_73 = lean_array_push(x_18, x_16);
x_9 = x_7;
x_10 = x_73;
goto block_14;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_16, 0);
lean_inc(x_74);
lean_dec(x_16);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_58);
x_76 = lean_array_push(x_18, x_75);
x_9 = x_7;
x_10 = x_76;
goto block_14;
}
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_7, 0);
x_78 = lean_ctor_get(x_7, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_7);
x_79 = l_Lake_RBNode_dFind___at_Lake_decodeTargetDecls_go___spec__1(x_1, x_78, x_26);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
lean_dec(x_16);
lean_inc(x_3);
lean_inc(x_26);
x_80 = lean_apply_2(x_3, x_26, x_19);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_26);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Array_append___rarg(x_18, x_81);
lean_dec(x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_77);
lean_ctor_set(x_83, 1, x_78);
x_9 = x_83;
x_10 = x_82;
goto block_14;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_80, 0);
lean_inc(x_84);
lean_dec(x_80);
lean_inc(x_2);
lean_inc(x_26);
lean_inc(x_1);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_1);
lean_ctor_set(x_85, 1, x_26);
lean_ctor_set(x_85, 2, x_2);
lean_ctor_set(x_85, 3, x_84);
lean_inc(x_85);
x_86 = lean_array_push(x_77, x_85);
x_87 = l_Lean_RBNode_insert___at_Lake_decodeTargetDecls_go___spec__2(x_1, x_78, x_26, x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_9 = x_88;
x_10 = x_18;
goto block_14;
}
}
else
{
lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_19);
x_89 = lean_ctor_get(x_79, 0);
lean_inc(x_89);
lean_dec(x_79);
x_90 = 1;
x_91 = l_Lake_StrPat_decodeToml___closed__6;
lean_inc(x_1);
x_92 = l_Lean_Name_toString(x_1, x_90, x_91);
x_93 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_94 = lean_string_append(x_93, x_92);
lean_dec(x_92);
x_95 = l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__1;
x_96 = lean_string_append(x_94, x_95);
x_97 = l_Lean_Name_toString(x_26, x_90, x_91);
x_98 = lean_string_append(x_96, x_97);
lean_dec(x_97);
x_99 = l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__2;
x_100 = lean_string_append(x_98, x_99);
x_101 = lean_ctor_get(x_89, 2);
lean_inc(x_101);
lean_dec(x_89);
x_102 = l_Lean_Name_toString(x_101, x_90, x_91);
x_103 = lean_string_append(x_100, x_102);
lean_dec(x_102);
x_104 = l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__3;
x_105 = lean_string_append(x_103, x_104);
lean_inc(x_2);
x_106 = l_Lean_Name_toString(x_2, x_90, x_91);
x_107 = lean_string_append(x_105, x_106);
lean_dec(x_106);
x_108 = l_Lake_StrPat_decodeToml___closed__8;
x_109 = lean_string_append(x_107, x_108);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_16, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_111 = x_16;
} else {
 lean_dec_ref(x_16);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_109);
x_113 = lean_array_push(x_18, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_77);
lean_ctor_set(x_114, 1, x_78);
x_9 = x_114;
x_10 = x_113;
goto block_14;
}
case 2:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_16, 0);
lean_inc(x_115);
lean_dec(x_16);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_109);
x_117 = lean_array_push(x_18, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_77);
lean_ctor_set(x_118, 1, x_78);
x_9 = x_118;
x_10 = x_117;
goto block_14;
}
case 3:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_16, 0);
lean_inc(x_119);
lean_dec(x_16);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_109);
x_121 = lean_array_push(x_18, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_77);
lean_ctor_set(x_122, 1, x_78);
x_9 = x_122;
x_10 = x_121;
goto block_14;
}
default: 
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_123 = lean_ctor_get(x_16, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_124 = x_16;
} else {
 lean_dec_ref(x_16);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_124;
 lean_ctor_set_tag(x_125, 0);
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_109);
x_126 = lean_array_push(x_18, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_77);
lean_ctor_set(x_127, 1, x_78);
x_9 = x_127;
x_10 = x_126;
goto block_14;
}
}
}
}
}
}
}
block_135:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_array_mk(x_131);
x_133 = l_Array_append___rarg(x_8, x_132);
lean_dec(x_132);
x_134 = lean_box(0);
x_17 = x_134;
x_18 = x_133;
goto block_128;
}
}
else
{
lean_object* x_141; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_7);
lean_ctor_set(x_141, 1, x_8);
return x_141;
}
block_14:
{
size_t x_11; size_t x_12; 
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_7 = x_9;
x_8 = x_10;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_decodeTargetDecls_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_14; lean_object* x_15; 
x_14 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
lean_inc(x_4);
x_15 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_14, x_4, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
switch (lean_obj_tag(x_18)) {
case 0:
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_dec(x_20);
x_21 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_18, 1, x_21);
x_7 = x_18;
goto block_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = l_Lake_LeanConfig_decodeToml___closed__5;
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_7 = x_24;
goto block_13;
}
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
x_26 = l_Lake_LeanConfig_decodeToml___closed__5;
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_7 = x_27;
goto block_13;
}
case 3:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = l_Lake_LeanConfig_decodeToml___closed__5;
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_7 = x_30;
goto block_13;
}
case 5:
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_18, 1);
x_33 = lean_ctor_get(x_18, 0);
lean_dec(x_33);
x_34 = lean_array_get_size(x_32);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_nat_dec_lt(x_35, x_34);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_34, x_34);
if (x_37 == 0)
{
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 0, x_3);
return x_18;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; 
lean_free_object(x_18);
x_38 = 0;
x_39 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_40 = l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5(x_1, x_4, x_5, x_32, x_38, x_39, x_3, x_6);
lean_dec(x_32);
return x_40;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_array_get_size(x_41);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_nat_dec_lt(x_43, x_42);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set(x_45, 1, x_6);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_42, x_42);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_6);
return x_47;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = 0;
x_49 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_50 = l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5(x_1, x_4, x_5, x_41, x_48, x_49, x_3, x_6);
lean_dec(x_41);
return x_50;
}
}
}
}
default: 
{
uint8_t x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_18, 1);
lean_dec(x_52);
x_53 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 1, x_53);
x_7 = x_18;
goto block_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_18, 0);
lean_inc(x_54);
lean_dec(x_18);
x_55 = l_Lake_LeanConfig_decodeToml___closed__5;
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_7 = x_56;
goto block_13;
}
}
}
}
block_13:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_array_mk(x_9);
x_11 = l_Array_append___rarg(x_6, x_10);
lean_dec(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_RBNode_dFind___at_Lake_decodeTargetDecls_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_RBNode_dFind___at_Lake_decodeTargetDecls_go___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_ins___at_Lake_decodeTargetDecls_go___spec__4(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_insert___at_Lake_decodeTargetDecls_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_RBNode_insert___at_Lake_decodeTargetDecls_go___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
static lean_object* _init_l_Lake_decodeTargetDecls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_decodeLeanOptions___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_decodeTargetDecls___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_decodeTargetDecls___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_decodeTargetDecls___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_decodeTargetDecls___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanLibConfig_decodeToml), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_decodeTargetDecls___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_exe", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_decodeTargetDecls___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_decodeTargetDecls___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_decodeTargetDecls___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_LeanExeConfig_decodeToml), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_decodeTargetDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_4 = l_Lake_decodeTargetDecls___closed__1;
x_5 = l_Lake_decodeTargetDecls___closed__3;
x_6 = l_Lake_decodeTargetDecls___closed__4;
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lake_decodeTargetDecls_go(x_1, x_2, x_4, x_5, x_6, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lake_decodeTargetDecls___closed__6;
x_11 = l_Lake_decodeTargetDecls___closed__7;
x_12 = l_Lake_decodeTargetDecls_go(x_1, x_2, x_8, x_10, x_11, x_9);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
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
x_5 = lean_ctor_get(x_1, 1);
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
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_6);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_6, 1);
lean_dec(x_19);
x_20 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set(x_6, 1, x_20);
x_9 = x_6;
goto block_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_6, 0);
lean_inc(x_21);
lean_dec(x_6);
x_22 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_9 = x_23;
goto block_17;
}
}
case 2:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
lean_inc(x_24);
lean_dec(x_6);
x_25 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_9 = x_26;
goto block_17;
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_9 = x_29;
goto block_17;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_6, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_dec(x_6);
x_32 = l_Lake_Dependency_decodeToml(x_31, x_30);
x_33 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_34 = l_Lake_mergeErrors___rarg(x_4, x_32, x_33);
x_2 = x_8;
x_4 = x_34;
goto _start;
}
default: 
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_6);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_6, 1);
lean_dec(x_37);
x_38 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_38);
x_9 = x_6;
goto block_17;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_6, 0);
lean_inc(x_39);
lean_dec(x_6);
x_40 = l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1;
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_9 = x_41;
goto block_17;
}
}
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_array_mk(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Array_foldlMUnsafe_fold___at_Lake_decodeLeanOptions___spec__2___closed__1;
x_15 = l_Lake_mergeErrors___rarg(x_4, x_13, x_14);
x_2 = x_8;
x_4 = x_15;
goto _start;
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
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_5);
if (x_21 == 0)
{
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_5, 0);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_StrPat_decodeToml___closed__6;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_loadTomlConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_ctor_get(x_1, 2);
lean_inc(x_424);
x_425 = lean_ctor_get(x_1, 3);
lean_inc(x_425);
x_426 = lean_ctor_get(x_1, 4);
lean_inc(x_426);
x_427 = l_System_FilePath_join(x_424, x_425);
lean_dec(x_425);
x_428 = l_System_FilePath_join(x_427, x_426);
lean_dec(x_426);
x_429 = l_IO_FS_readFile(x_428, x_3);
lean_dec(x_428);
if (lean_obj_tag(x_429) == 0)
{
uint8_t x_430; 
x_430 = !lean_is_exclusive(x_429);
if (x_430 == 0)
{
lean_object* x_431; 
x_431 = lean_ctor_get(x_429, 1);
lean_ctor_set(x_429, 1, x_2);
x_4 = x_429;
x_5 = x_431;
goto block_423;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_429, 0);
x_433 = lean_ctor_get(x_429, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_429);
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_2);
x_4 = x_434;
x_5 = x_433;
goto block_423;
}
}
else
{
uint8_t x_435; 
x_435 = !lean_is_exclusive(x_429);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_436 = lean_ctor_get(x_429, 0);
x_437 = lean_ctor_get(x_429, 1);
x_438 = lean_io_error_to_string(x_436);
x_439 = 3;
x_440 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_440, 0, x_438);
lean_ctor_set_uint8(x_440, sizeof(void*)*1, x_439);
x_441 = lean_array_get_size(x_2);
x_442 = lean_array_push(x_2, x_440);
lean_ctor_set(x_429, 1, x_442);
lean_ctor_set(x_429, 0, x_441);
x_4 = x_429;
x_5 = x_437;
goto block_423;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_443 = lean_ctor_get(x_429, 0);
x_444 = lean_ctor_get(x_429, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_429);
x_445 = lean_io_error_to_string(x_443);
x_446 = 3;
x_447 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set_uint8(x_447, sizeof(void*)*1, x_446);
x_448 = lean_array_get_size(x_2);
x_449 = lean_array_push(x_2, x_447);
x_450 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_450, 0, x_448);
lean_ctor_set(x_450, 1, x_449);
x_4 = x_450;
x_5 = x_444;
goto block_423;
}
}
block_423:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_215; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = 1;
lean_inc(x_8);
x_10 = l_Lean_Parser_mkInputContext(x_7, x_8, x_9);
lean_inc(x_10);
x_215 = l_Lake_Toml_loadToml(x_10, x_5);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_4, 0, x_218);
x_11 = x_4;
x_12 = x_217;
goto block_214;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_215, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_215, 1);
lean_inc(x_220);
lean_dec(x_215);
x_221 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_4, 0, x_221);
x_11 = x_4;
x_12 = x_220;
goto block_214;
}
block_214:
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
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_78 = lean_ctor_get(x_13, 0);
lean_inc(x_78);
lean_dec(x_13);
x_205 = l_Lake_LeanOption_decodeToml___closed__10;
x_206 = lean_box(0);
lean_inc(x_78);
x_207 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_78, x_205, x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec(x_207);
x_209 = l_Lake_decodeLeanOptions___closed__1;
x_210 = l_Array_append___rarg(x_209, x_208);
lean_dec(x_208);
x_211 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_79 = x_211;
x_80 = x_210;
goto block_204;
}
else
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_207, 0);
lean_inc(x_212);
lean_dec(x_207);
x_213 = l_Lake_decodeLeanOptions___closed__1;
x_79 = x_212;
x_80 = x_213;
goto block_204;
}
block_204:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_192; 
x_81 = l_Lake_stringToLegalOrSimpleName(x_79);
lean_inc(x_78);
lean_inc(x_81);
x_192 = l_Lake_PackageConfig_decodeToml(x_81, x_78);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_box(0);
x_195 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_196 = l_Lake_PackageConfig_decodeToml___closed__7;
x_197 = l_Lake_LeanOption_decodeToml___closed__3;
x_198 = 0;
x_199 = l_Lake_PackageConfig_decodeToml___closed__31;
x_200 = l_Lake_loadTomlConfig___closed__6;
x_201 = lean_alloc_ctor(0, 28, 3);
lean_ctor_set(x_201, 0, x_195);
lean_ctor_set(x_201, 1, x_196);
lean_ctor_set(x_201, 2, x_194);
lean_ctor_set(x_201, 3, x_197);
lean_ctor_set(x_201, 4, x_197);
lean_ctor_set(x_201, 5, x_197);
lean_ctor_set(x_201, 6, x_195);
lean_ctor_set(x_201, 7, x_195);
lean_ctor_set(x_201, 8, x_195);
lean_ctor_set(x_201, 9, x_195);
lean_ctor_set(x_201, 10, x_195);
lean_ctor_set(x_201, 11, x_195);
lean_ctor_set(x_201, 12, x_194);
lean_ctor_set(x_201, 13, x_194);
lean_ctor_set(x_201, 14, x_194);
lean_ctor_set(x_201, 15, x_195);
lean_ctor_set(x_201, 16, x_195);
lean_ctor_set(x_201, 17, x_197);
lean_ctor_set(x_201, 18, x_195);
lean_ctor_set(x_201, 19, x_197);
lean_ctor_set(x_201, 20, x_199);
lean_ctor_set(x_201, 21, x_200);
lean_ctor_set(x_201, 22, x_195);
lean_ctor_set(x_201, 23, x_197);
lean_ctor_set(x_201, 24, x_195);
lean_ctor_set(x_201, 25, x_195);
lean_ctor_set(x_201, 26, x_197);
lean_ctor_set(x_201, 27, x_195);
lean_ctor_set_uint8(x_201, sizeof(void*)*28, x_198);
lean_ctor_set_uint8(x_201, sizeof(void*)*28 + 1, x_198);
lean_ctor_set_uint8(x_201, sizeof(void*)*28 + 2, x_198);
x_202 = l_Array_append___rarg(x_80, x_193);
lean_dec(x_193);
x_82 = x_201;
x_83 = x_202;
goto block_191;
}
else
{
lean_object* x_203; 
x_203 = lean_ctor_get(x_192, 0);
lean_inc(x_203);
lean_dec(x_192);
x_82 = x_203;
x_83 = x_80;
goto block_191;
}
block_191:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_154; lean_object* x_155; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_inc(x_78);
lean_inc(x_81);
x_84 = l_Lake_decodeTargetDecls(x_81, x_78, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_90 = x_85;
} else {
 lean_dec_ref(x_85);
 x_90 = lean_box(0);
}
x_154 = lean_box(0);
x_161 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_162 = l_Lake_loadTomlConfig___closed__5;
lean_inc(x_78);
x_163 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_161, x_162, x_78);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; 
x_164 = l_Lake_decodeLeanOptions___closed__1;
x_91 = x_164;
x_92 = x_86;
goto block_153;
}
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_165, 1);
lean_inc(x_166);
lean_dec(x_165);
switch (lean_obj_tag(x_166)) {
case 0:
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_166, 1);
lean_dec(x_168);
x_169 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_166, 1, x_169);
x_155 = x_166;
goto block_160;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_166, 0);
lean_inc(x_170);
lean_dec(x_166);
x_171 = l_Lake_LeanConfig_decodeToml___closed__5;
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
x_155 = x_172;
goto block_160;
}
}
case 2:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_166, 0);
lean_inc(x_173);
lean_dec(x_166);
x_174 = l_Lake_LeanConfig_decodeToml___closed__5;
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_155 = x_175;
goto block_160;
}
case 3:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_166, 0);
lean_inc(x_176);
lean_dec(x_166);
x_177 = l_Lake_LeanConfig_decodeToml___closed__5;
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
x_155 = x_178;
goto block_160;
}
case 5:
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_166, 1);
lean_inc(x_179);
lean_dec(x_166);
x_180 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_179);
lean_dec(x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec(x_180);
x_182 = l_Array_append___rarg(x_86, x_181);
lean_dec(x_181);
x_183 = l_Lake_decodeLeanOptions___closed__1;
x_91 = x_183;
x_92 = x_182;
goto block_153;
}
else
{
lean_object* x_184; 
x_184 = lean_ctor_get(x_180, 0);
lean_inc(x_184);
lean_dec(x_180);
x_91 = x_184;
x_92 = x_86;
goto block_153;
}
}
default: 
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_166);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_166, 1);
lean_dec(x_186);
x_187 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_166, 0);
lean_ctor_set(x_166, 1, x_187);
x_155 = x_166;
goto block_160;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_166, 0);
lean_inc(x_188);
lean_dec(x_166);
x_189 = l_Lake_LeanConfig_decodeToml___closed__5;
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_155 = x_190;
goto block_160;
}
}
}
}
block_153:
{
size_t x_93; size_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_116; lean_object* x_117; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_93 = lean_array_size(x_91);
x_94 = 0;
x_95 = l_Array_mapMUnsafe_map___at_Lake_loadTomlConfig___spec__8(x_93, x_94, x_91);
x_116 = lean_box(0);
x_123 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_124 = l_Lake_loadTomlConfig___closed__3;
x_125 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_123, x_124, x_78);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
lean_dec(x_90);
lean_dec(x_87);
x_126 = l_Lake_decodeLeanOptions___closed__1;
x_96 = x_126;
x_97 = x_92;
goto block_115;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
switch (lean_obj_tag(x_128)) {
case 0:
{
uint8_t x_129; 
lean_dec(x_87);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 1);
lean_dec(x_130);
x_131 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set(x_128, 1, x_131);
x_117 = x_128;
goto block_122;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_128, 0);
lean_inc(x_132);
lean_dec(x_128);
x_133 = l_Lake_LeanConfig_decodeToml___closed__5;
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_117 = x_134;
goto block_122;
}
}
case 2:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_128, 0);
lean_inc(x_135);
lean_dec(x_128);
x_136 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_87)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_87;
}
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_117 = x_137;
goto block_122;
}
case 3:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_128, 0);
lean_inc(x_138);
lean_dec(x_128);
x_139 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_87)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_87;
}
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
x_117 = x_140;
goto block_122;
}
case 5:
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_90);
lean_dec(x_87);
x_141 = lean_ctor_get(x_128, 1);
lean_inc(x_141);
lean_dec(x_128);
x_142 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9(x_141);
lean_dec(x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec(x_142);
x_144 = l_Array_append___rarg(x_92, x_143);
lean_dec(x_143);
x_145 = l_Lake_decodeLeanOptions___closed__1;
x_96 = x_145;
x_97 = x_144;
goto block_115;
}
else
{
lean_object* x_146; 
x_146 = lean_ctor_get(x_142, 0);
lean_inc(x_146);
lean_dec(x_142);
x_96 = x_146;
x_97 = x_92;
goto block_115;
}
}
default: 
{
uint8_t x_147; 
lean_dec(x_87);
x_147 = !lean_is_exclusive(x_128);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_128, 1);
lean_dec(x_148);
x_149 = l_Lake_LeanConfig_decodeToml___closed__5;
lean_ctor_set_tag(x_128, 0);
lean_ctor_set(x_128, 1, x_149);
x_117 = x_128;
goto block_122;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_128, 0);
lean_inc(x_150);
lean_dec(x_128);
x_151 = l_Lake_LeanConfig_decodeToml___closed__5;
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
x_117 = x_152;
goto block_122;
}
}
}
}
block_115:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_1, 2);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 3);
lean_inc(x_99);
x_100 = l_System_FilePath_join(x_98, x_99);
x_101 = lean_ctor_get(x_82, 2);
lean_inc(x_101);
x_102 = lean_ctor_get(x_1, 8);
lean_inc(x_102);
x_103 = lean_ctor_get(x_1, 9);
lean_inc(x_103);
lean_dec(x_1);
x_104 = lean_box(0);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_82, 16);
lean_inc(x_105);
x_106 = lean_ctor_get(x_82, 18);
lean_inc(x_106);
x_107 = l_Lake_defaultManifestFile;
x_108 = l_Lake_decodeLeanOptions___closed__1;
x_109 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_109, 0, x_81);
lean_ctor_set(x_109, 1, x_100);
lean_ctor_set(x_109, 2, x_99);
lean_ctor_set(x_109, 3, x_82);
lean_ctor_set(x_109, 4, x_8);
lean_ctor_set(x_109, 5, x_107);
lean_ctor_set(x_109, 6, x_102);
lean_ctor_set(x_109, 7, x_103);
lean_ctor_set(x_109, 8, x_96);
lean_ctor_set(x_109, 9, x_88);
lean_ctor_set(x_109, 10, x_89);
lean_ctor_set(x_109, 11, x_95);
lean_ctor_set(x_109, 12, x_104);
lean_ctor_set(x_109, 13, x_108);
lean_ctor_set(x_109, 14, x_108);
lean_ctor_set(x_109, 15, x_105);
lean_ctor_set(x_109, 16, x_106);
x_16 = x_109;
x_17 = x_97;
goto block_46;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_82, 16);
lean_inc(x_110);
x_111 = lean_ctor_get(x_82, 18);
lean_inc(x_111);
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
lean_dec(x_101);
x_113 = l_Lake_decodeLeanOptions___closed__1;
x_114 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_114, 0, x_81);
lean_ctor_set(x_114, 1, x_100);
lean_ctor_set(x_114, 2, x_99);
lean_ctor_set(x_114, 3, x_82);
lean_ctor_set(x_114, 4, x_8);
lean_ctor_set(x_114, 5, x_112);
lean_ctor_set(x_114, 6, x_102);
lean_ctor_set(x_114, 7, x_103);
lean_ctor_set(x_114, 8, x_96);
lean_ctor_set(x_114, 9, x_88);
lean_ctor_set(x_114, 10, x_89);
lean_ctor_set(x_114, 11, x_95);
lean_ctor_set(x_114, 12, x_104);
lean_ctor_set(x_114, 13, x_113);
lean_ctor_set(x_114, 14, x_113);
lean_ctor_set(x_114, 15, x_110);
lean_ctor_set(x_114, 16, x_111);
x_16 = x_114;
x_17 = x_97;
goto block_46;
}
}
block_122:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
if (lean_is_scalar(x_90)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_90;
 lean_ctor_set_tag(x_118, 1);
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_mk(x_118);
x_120 = l_Array_append___rarg(x_92, x_119);
lean_dec(x_119);
x_121 = l_Lake_decodeLeanOptions___closed__1;
x_96 = x_121;
x_97 = x_120;
goto block_115;
}
}
block_160:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_154);
x_157 = lean_array_mk(x_156);
x_158 = l_Array_append___rarg(x_86, x_157);
lean_dec(x_157);
x_159 = l_Lake_decodeLeanOptions___closed__1;
x_91 = x_159;
x_92 = x_158;
goto block_153;
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
lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_408; 
x_222 = lean_ctor_get(x_4, 0);
x_223 = lean_ctor_get(x_4, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_4);
x_224 = lean_ctor_get(x_1, 4);
lean_inc(x_224);
x_225 = 1;
lean_inc(x_224);
x_226 = l_Lean_Parser_mkInputContext(x_222, x_224, x_225);
lean_inc(x_226);
x_408 = l_Lake_Toml_loadToml(x_226, x_5);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_408, 1);
lean_inc(x_410);
lean_dec(x_408);
x_411 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_411, 0, x_409);
x_412 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_412, 0, x_411);
lean_ctor_set(x_412, 1, x_223);
x_227 = x_412;
x_228 = x_410;
goto block_407;
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_413 = lean_ctor_get(x_408, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_408, 1);
lean_inc(x_414);
lean_dec(x_408);
x_415 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_415, 0, x_413);
x_416 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_416, 0, x_415);
lean_ctor_set(x_416, 1, x_223);
x_227 = x_416;
x_228 = x_414;
goto block_407;
}
block_407:
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_ctor_get(x_227, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_231 = x_227;
} else {
 lean_dec_ref(x_227);
 x_231 = lean_box(0);
}
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_231);
lean_dec(x_226);
lean_dec(x_224);
lean_dec(x_1);
x_258 = lean_ctor_get(x_229, 0);
lean_inc(x_258);
lean_dec(x_229);
x_259 = lean_array_get_size(x_230);
x_260 = l_Lake_loadTomlConfig___closed__1;
x_261 = l_Lean_MessageLog_forM___at_Lake_loadTomlConfig___spec__2(x_258, x_260, x_230, x_228);
lean_dec(x_258);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_266 = x_262;
} else {
 lean_dec_ref(x_262);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
 lean_ctor_set_tag(x_267, 1);
}
lean_ctor_set(x_267, 0, x_259);
lean_ctor_set(x_267, 1, x_265);
if (lean_is_scalar(x_264)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_264;
}
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_263);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_269 = lean_ctor_get(x_261, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_270 = x_261;
} else {
 lean_dec_ref(x_261);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_262, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_272 = x_262;
} else {
 lean_dec_ref(x_262);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_259);
lean_ctor_set(x_273, 1, x_271);
if (lean_is_scalar(x_270)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_270;
}
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_269);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_259);
x_275 = lean_ctor_get(x_261, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_261, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_277 = x_261;
} else {
 lean_dec_ref(x_261);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_279 = lean_ctor_get(x_229, 0);
lean_inc(x_279);
lean_dec(x_229);
x_398 = l_Lake_LeanOption_decodeToml___closed__10;
x_399 = lean_box(0);
lean_inc(x_279);
x_400 = l_Lake_Toml_Table_decode___at_Lake_DependencySrc_decodeToml___spec__1(x_279, x_398, x_399);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
lean_dec(x_400);
x_402 = l_Lake_decodeLeanOptions___closed__1;
x_403 = l_Array_append___rarg(x_402, x_401);
lean_dec(x_401);
x_404 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_280 = x_404;
x_281 = x_403;
goto block_397;
}
else
{
lean_object* x_405; lean_object* x_406; 
x_405 = lean_ctor_get(x_400, 0);
lean_inc(x_405);
lean_dec(x_400);
x_406 = l_Lake_decodeLeanOptions___closed__1;
x_280 = x_405;
x_281 = x_406;
goto block_397;
}
block_397:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_385; 
x_282 = l_Lake_stringToLegalOrSimpleName(x_280);
lean_inc(x_279);
lean_inc(x_282);
x_385 = l_Lake_PackageConfig_decodeToml(x_282, x_279);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
lean_dec(x_385);
x_387 = lean_box(0);
x_388 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__3;
x_389 = l_Lake_PackageConfig_decodeToml___closed__7;
x_390 = l_Lake_LeanOption_decodeToml___closed__3;
x_391 = 0;
x_392 = l_Lake_PackageConfig_decodeToml___closed__31;
x_393 = l_Lake_loadTomlConfig___closed__6;
x_394 = lean_alloc_ctor(0, 28, 3);
lean_ctor_set(x_394, 0, x_388);
lean_ctor_set(x_394, 1, x_389);
lean_ctor_set(x_394, 2, x_387);
lean_ctor_set(x_394, 3, x_390);
lean_ctor_set(x_394, 4, x_390);
lean_ctor_set(x_394, 5, x_390);
lean_ctor_set(x_394, 6, x_388);
lean_ctor_set(x_394, 7, x_388);
lean_ctor_set(x_394, 8, x_388);
lean_ctor_set(x_394, 9, x_388);
lean_ctor_set(x_394, 10, x_388);
lean_ctor_set(x_394, 11, x_388);
lean_ctor_set(x_394, 12, x_387);
lean_ctor_set(x_394, 13, x_387);
lean_ctor_set(x_394, 14, x_387);
lean_ctor_set(x_394, 15, x_388);
lean_ctor_set(x_394, 16, x_388);
lean_ctor_set(x_394, 17, x_390);
lean_ctor_set(x_394, 18, x_388);
lean_ctor_set(x_394, 19, x_390);
lean_ctor_set(x_394, 20, x_392);
lean_ctor_set(x_394, 21, x_393);
lean_ctor_set(x_394, 22, x_388);
lean_ctor_set(x_394, 23, x_390);
lean_ctor_set(x_394, 24, x_388);
lean_ctor_set(x_394, 25, x_388);
lean_ctor_set(x_394, 26, x_390);
lean_ctor_set(x_394, 27, x_388);
lean_ctor_set_uint8(x_394, sizeof(void*)*28, x_391);
lean_ctor_set_uint8(x_394, sizeof(void*)*28 + 1, x_391);
lean_ctor_set_uint8(x_394, sizeof(void*)*28 + 2, x_391);
x_395 = l_Array_append___rarg(x_281, x_386);
lean_dec(x_386);
x_283 = x_394;
x_284 = x_395;
goto block_384;
}
else
{
lean_object* x_396; 
x_396 = lean_ctor_get(x_385, 0);
lean_inc(x_396);
lean_dec(x_385);
x_283 = x_396;
x_284 = x_281;
goto block_384;
}
block_384:
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_351; lean_object* x_352; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_inc(x_279);
lean_inc(x_282);
x_285 = l_Lake_decodeTargetDecls(x_282, x_279, x_284);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_288 = x_285;
} else {
 lean_dec_ref(x_285);
 x_288 = lean_box(0);
}
x_289 = lean_ctor_get(x_286, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_286, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_291 = x_286;
} else {
 lean_dec_ref(x_286);
 x_291 = lean_box(0);
}
x_351 = lean_box(0);
x_358 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_359 = l_Lake_loadTomlConfig___closed__5;
lean_inc(x_279);
x_360 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_358, x_359, x_279);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; 
x_361 = l_Lake_decodeLeanOptions___closed__1;
x_292 = x_361;
x_293 = x_287;
goto block_350;
}
else
{
lean_object* x_362; lean_object* x_363; 
x_362 = lean_ctor_get(x_360, 0);
lean_inc(x_362);
lean_dec(x_360);
x_363 = lean_ctor_get(x_362, 1);
lean_inc(x_363);
lean_dec(x_362);
switch (lean_obj_tag(x_363)) {
case 0:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_365 = x_363;
} else {
 lean_dec_ref(x_363);
 x_365 = lean_box(0);
}
x_366 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(0, 2, 0);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_366);
x_352 = x_367;
goto block_357;
}
case 2:
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_363, 0);
lean_inc(x_368);
lean_dec(x_363);
x_369 = l_Lake_LeanConfig_decodeToml___closed__5;
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
x_352 = x_370;
goto block_357;
}
case 3:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_363, 0);
lean_inc(x_371);
lean_dec(x_363);
x_372 = l_Lake_LeanConfig_decodeToml___closed__5;
x_373 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
x_352 = x_373;
goto block_357;
}
case 5:
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_363, 1);
lean_inc(x_374);
lean_dec(x_363);
x_375 = l_Lake_Toml_decodeArray___at_Lake_StrPat_decodeToml___spec__1(x_374);
lean_dec(x_374);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
lean_dec(x_375);
x_377 = l_Array_append___rarg(x_287, x_376);
lean_dec(x_376);
x_378 = l_Lake_decodeLeanOptions___closed__1;
x_292 = x_378;
x_293 = x_377;
goto block_350;
}
else
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_375, 0);
lean_inc(x_379);
lean_dec(x_375);
x_292 = x_379;
x_293 = x_287;
goto block_350;
}
}
default: 
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_380 = lean_ctor_get(x_363, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_381 = x_363;
} else {
 lean_dec_ref(x_363);
 x_381 = lean_box(0);
}
x_382 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_381)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_381;
 lean_ctor_set_tag(x_383, 0);
}
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_382);
x_352 = x_383;
goto block_357;
}
}
}
block_350:
{
size_t x_294; size_t x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_317; lean_object* x_318; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_294 = lean_array_size(x_292);
x_295 = 0;
x_296 = l_Array_mapMUnsafe_map___at_Lake_loadTomlConfig___spec__8(x_294, x_295, x_292);
x_317 = lean_box(0);
x_324 = l_Lake_Toml_Table_decode___at_Lake_LeanOption_decodeToml___spec__1___closed__1;
x_325 = l_Lake_loadTomlConfig___closed__3;
x_326 = l_Lake_Toml_RBDict_findEntry_x3f___rarg(x_324, x_325, x_279);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; 
lean_dec(x_291);
lean_dec(x_288);
x_327 = l_Lake_decodeLeanOptions___closed__1;
x_297 = x_327;
x_298 = x_293;
goto block_316;
}
else
{
lean_object* x_328; lean_object* x_329; 
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
lean_dec(x_326);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
switch (lean_obj_tag(x_329)) {
case 0:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_288);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_331 = x_329;
} else {
 lean_dec_ref(x_329);
 x_331 = lean_box(0);
}
x_332 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_331)) {
 x_333 = lean_alloc_ctor(0, 2, 0);
} else {
 x_333 = x_331;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_332);
x_318 = x_333;
goto block_323;
}
case 2:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_329, 0);
lean_inc(x_334);
lean_dec(x_329);
x_335 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_288)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_288;
}
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
x_318 = x_336;
goto block_323;
}
case 3:
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_329, 0);
lean_inc(x_337);
lean_dec(x_329);
x_338 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_288)) {
 x_339 = lean_alloc_ctor(0, 2, 0);
} else {
 x_339 = x_288;
}
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
x_318 = x_339;
goto block_323;
}
case 5:
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_291);
lean_dec(x_288);
x_340 = lean_ctor_get(x_329, 1);
lean_inc(x_340);
lean_dec(x_329);
x_341 = l_Lake_Toml_decodeArray___at_Lake_loadTomlConfig___spec__9(x_340);
lean_dec(x_340);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
lean_dec(x_341);
x_343 = l_Array_append___rarg(x_293, x_342);
lean_dec(x_342);
x_344 = l_Lake_decodeLeanOptions___closed__1;
x_297 = x_344;
x_298 = x_343;
goto block_316;
}
else
{
lean_object* x_345; 
x_345 = lean_ctor_get(x_341, 0);
lean_inc(x_345);
lean_dec(x_341);
x_297 = x_345;
x_298 = x_293;
goto block_316;
}
}
default: 
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_288);
x_346 = lean_ctor_get(x_329, 0);
lean_inc(x_346);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_347 = x_329;
} else {
 lean_dec_ref(x_329);
 x_347 = lean_box(0);
}
x_348 = l_Lake_LeanConfig_decodeToml___closed__5;
if (lean_is_scalar(x_347)) {
 x_349 = lean_alloc_ctor(0, 2, 0);
} else {
 x_349 = x_347;
 lean_ctor_set_tag(x_349, 0);
}
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_348);
x_318 = x_349;
goto block_323;
}
}
}
block_316:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_299 = lean_ctor_get(x_1, 2);
lean_inc(x_299);
x_300 = lean_ctor_get(x_1, 3);
lean_inc(x_300);
x_301 = l_System_FilePath_join(x_299, x_300);
x_302 = lean_ctor_get(x_283, 2);
lean_inc(x_302);
x_303 = lean_ctor_get(x_1, 8);
lean_inc(x_303);
x_304 = lean_ctor_get(x_1, 9);
lean_inc(x_304);
lean_dec(x_1);
x_305 = lean_box(0);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_306 = lean_ctor_get(x_283, 16);
lean_inc(x_306);
x_307 = lean_ctor_get(x_283, 18);
lean_inc(x_307);
x_308 = l_Lake_defaultManifestFile;
x_309 = l_Lake_decodeLeanOptions___closed__1;
x_310 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_310, 0, x_282);
lean_ctor_set(x_310, 1, x_301);
lean_ctor_set(x_310, 2, x_300);
lean_ctor_set(x_310, 3, x_283);
lean_ctor_set(x_310, 4, x_224);
lean_ctor_set(x_310, 5, x_308);
lean_ctor_set(x_310, 6, x_303);
lean_ctor_set(x_310, 7, x_304);
lean_ctor_set(x_310, 8, x_297);
lean_ctor_set(x_310, 9, x_289);
lean_ctor_set(x_310, 10, x_290);
lean_ctor_set(x_310, 11, x_296);
lean_ctor_set(x_310, 12, x_305);
lean_ctor_set(x_310, 13, x_309);
lean_ctor_set(x_310, 14, x_309);
lean_ctor_set(x_310, 15, x_306);
lean_ctor_set(x_310, 16, x_307);
x_232 = x_310;
x_233 = x_298;
goto block_257;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_283, 16);
lean_inc(x_311);
x_312 = lean_ctor_get(x_283, 18);
lean_inc(x_312);
x_313 = lean_ctor_get(x_302, 0);
lean_inc(x_313);
lean_dec(x_302);
x_314 = l_Lake_decodeLeanOptions___closed__1;
x_315 = lean_alloc_ctor(0, 17, 0);
lean_ctor_set(x_315, 0, x_282);
lean_ctor_set(x_315, 1, x_301);
lean_ctor_set(x_315, 2, x_300);
lean_ctor_set(x_315, 3, x_283);
lean_ctor_set(x_315, 4, x_224);
lean_ctor_set(x_315, 5, x_313);
lean_ctor_set(x_315, 6, x_303);
lean_ctor_set(x_315, 7, x_304);
lean_ctor_set(x_315, 8, x_297);
lean_ctor_set(x_315, 9, x_289);
lean_ctor_set(x_315, 10, x_290);
lean_ctor_set(x_315, 11, x_296);
lean_ctor_set(x_315, 12, x_305);
lean_ctor_set(x_315, 13, x_314);
lean_ctor_set(x_315, 14, x_314);
lean_ctor_set(x_315, 15, x_311);
lean_ctor_set(x_315, 16, x_312);
x_232 = x_315;
x_233 = x_298;
goto block_257;
}
}
block_323:
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
if (lean_is_scalar(x_291)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_291;
 lean_ctor_set_tag(x_319, 1);
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_317);
x_320 = lean_array_mk(x_319);
x_321 = l_Array_append___rarg(x_293, x_320);
lean_dec(x_320);
x_322 = l_Lake_decodeLeanOptions___closed__1;
x_297 = x_322;
x_298 = x_321;
goto block_316;
}
}
block_357:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_351);
x_354 = lean_array_mk(x_353);
x_355 = l_Array_append___rarg(x_287, x_354);
lean_dec(x_354);
x_356 = l_Lake_decodeLeanOptions___closed__1;
x_292 = x_356;
x_293 = x_355;
goto block_350;
}
}
}
}
block_257:
{
uint8_t x_234; 
x_234 = l_Array_isEmpty___rarg(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
lean_dec(x_232);
x_235 = lean_array_get_size(x_233);
x_236 = lean_unsigned_to_nat(0u);
x_237 = lean_nat_dec_lt(x_236, x_235);
x_238 = lean_array_get_size(x_230);
if (x_237 == 0)
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_235);
lean_dec(x_233);
lean_dec(x_226);
if (lean_is_scalar(x_231)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_231;
 lean_ctor_set_tag(x_239, 1);
}
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_230);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_228);
return x_240;
}
else
{
uint8_t x_241; 
x_241 = lean_nat_dec_le(x_235, x_235);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
lean_dec(x_235);
lean_dec(x_233);
lean_dec(x_226);
if (lean_is_scalar(x_231)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_231;
 lean_ctor_set_tag(x_242, 1);
}
lean_ctor_set(x_242, 0, x_238);
lean_ctor_set(x_242, 1, x_230);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_228);
return x_243;
}
else
{
size_t x_244; size_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_231);
x_244 = 0;
x_245 = lean_usize_of_nat(x_235);
lean_dec(x_235);
x_246 = lean_box(0);
x_247 = l_Array_foldlMUnsafe_fold___at_Lake_loadTomlConfig___spec__1(x_226, x_233, x_244, x_245, x_246, x_230, x_228);
lean_dec(x_233);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_250 = x_247;
} else {
 lean_dec_ref(x_247);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_252 = x_248;
} else {
 lean_dec_ref(x_248);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
 lean_ctor_set_tag(x_253, 1);
}
lean_ctor_set(x_253, 0, x_238);
lean_ctor_set(x_253, 1, x_251);
if (lean_is_scalar(x_250)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_250;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_249);
return x_254;
}
}
}
else
{
lean_object* x_255; lean_object* x_256; 
lean_dec(x_233);
lean_dec(x_226);
if (lean_is_scalar(x_231)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_231;
}
lean_ctor_set(x_255, 0, x_232);
lean_ctor_set(x_255, 1, x_230);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_228);
return x_256;
}
}
}
}
}
else
{
uint8_t x_417; 
lean_dec(x_1);
x_417 = !lean_is_exclusive(x_4);
if (x_417 == 0)
{
lean_object* x_418; 
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_4);
lean_ctor_set(x_418, 1, x_5);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_419 = lean_ctor_get(x_4, 0);
x_420 = lean_ctor_get(x_4, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_4);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_5);
return x_422;
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
lean_object* initialize_Lake_Toml_Load(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Decode(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Log(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Load_Toml(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
l_Lake_LeanOption_decodeToml___closed__6 = _init_l_Lake_LeanOption_decodeToml___closed__6();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__6);
l_Lake_LeanOption_decodeToml___closed__7 = _init_l_Lake_LeanOption_decodeToml___closed__7();
lean_mark_persistent(l_Lake_LeanOption_decodeToml___closed__7);
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
l_Lake_WorkspaceConfig_decodeToml___closed__3 = _init_l_Lake_WorkspaceConfig_decodeToml___closed__3();
lean_mark_persistent(l_Lake_WorkspaceConfig_decodeToml___closed__3);
l_Lake_WorkspaceConfig_decodeToml___closed__4 = _init_l_Lake_WorkspaceConfig_decodeToml___closed__4();
lean_mark_persistent(l_Lake_WorkspaceConfig_decodeToml___closed__4);
l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1 = _init_l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1();
lean_mark_persistent(l_Lake_instDecodeTomlWorkspaceConfig___lambda__1___closed__1);
l_Lake_instDecodeTomlWorkspaceConfig___closed__1 = _init_l_Lake_instDecodeTomlWorkspaceConfig___closed__1();
lean_mark_persistent(l_Lake_instDecodeTomlWorkspaceConfig___closed__1);
l_Lake_instDecodeTomlWorkspaceConfig = _init_l_Lake_instDecodeTomlWorkspaceConfig();
lean_mark_persistent(l_Lake_instDecodeTomlWorkspaceConfig);
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
l_Lake_instDecodeTomlLeanConfig___closed__1 = _init_l_Lake_instDecodeTomlLeanConfig___closed__1();
lean_mark_persistent(l_Lake_instDecodeTomlLeanConfig___closed__1);
l_Lake_instDecodeTomlLeanConfig = _init_l_Lake_instDecodeTomlLeanConfig();
lean_mark_persistent(l_Lake_instDecodeTomlLeanConfig);
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
l_Lake_DependencySrc_decodeToml___closed__20 = _init_l_Lake_DependencySrc_decodeToml___closed__20();
lean_mark_persistent(l_Lake_DependencySrc_decodeToml___closed__20);
l_Lake_instDecodeTomlDependencySrc___closed__1 = _init_l_Lake_instDecodeTomlDependencySrc___closed__1();
lean_mark_persistent(l_Lake_instDecodeTomlDependencySrc___closed__1);
l_Lake_instDecodeTomlDependencySrc = _init_l_Lake_instDecodeTomlDependencySrc();
lean_mark_persistent(l_Lake_instDecodeTomlDependencySrc);
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
l_Lake_instDecodeTomlDependency___closed__1 = _init_l_Lake_instDecodeTomlDependency___closed__1();
lean_mark_persistent(l_Lake_instDecodeTomlDependency___closed__1);
l_Lake_instDecodeTomlDependency = _init_l_Lake_instDecodeTomlDependency();
lean_mark_persistent(l_Lake_instDecodeTomlDependency);
l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__1 = _init_l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__1();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__1);
l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__2 = _init_l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__2();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__2);
l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__3 = _init_l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__3();
lean_mark_persistent(l_Array_foldlMUnsafe_fold___at_Lake_decodeTargetDecls_go___spec__5___closed__3);
l_Lake_decodeTargetDecls___closed__1 = _init_l_Lake_decodeTargetDecls___closed__1();
lean_mark_persistent(l_Lake_decodeTargetDecls___closed__1);
l_Lake_decodeTargetDecls___closed__2 = _init_l_Lake_decodeTargetDecls___closed__2();
lean_mark_persistent(l_Lake_decodeTargetDecls___closed__2);
l_Lake_decodeTargetDecls___closed__3 = _init_l_Lake_decodeTargetDecls___closed__3();
lean_mark_persistent(l_Lake_decodeTargetDecls___closed__3);
l_Lake_decodeTargetDecls___closed__4 = _init_l_Lake_decodeTargetDecls___closed__4();
lean_mark_persistent(l_Lake_decodeTargetDecls___closed__4);
l_Lake_decodeTargetDecls___closed__5 = _init_l_Lake_decodeTargetDecls___closed__5();
lean_mark_persistent(l_Lake_decodeTargetDecls___closed__5);
l_Lake_decodeTargetDecls___closed__6 = _init_l_Lake_decodeTargetDecls___closed__6();
lean_mark_persistent(l_Lake_decodeTargetDecls___closed__6);
l_Lake_decodeTargetDecls___closed__7 = _init_l_Lake_decodeTargetDecls___closed__7();
lean_mark_persistent(l_Lake_decodeTargetDecls___closed__7);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
