// Lean compiler output
// Module: Lake.CLI.Init
// Imports: public import Lake.Config.Env public import Lake.Config.Lang import Lake.Util.Git import Lake.Util.Version import Lake.Config.Package import Lake.Config.Workspace import Lake.Load.Config import Lake.Load.Workspace import Lake.Build.Actions
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeFileContents;
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_defaultExeRoot;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___boxed(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object*);
lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprInitTemplate___closed__0;
extern lean_object* l_Lake_toolchainFileName;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents;
static lean_object* l_Lake_defaultExeRoot___closed__1;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10;
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___boxed(lean_object*);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22;
lean_object* l_String_Slice_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static lean_object* l_Lake_init___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2;
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object*);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__4;
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object*, lean_object*);
extern uint32_t l_Lean_idBeginEscape;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18;
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_instReprInitTemplate_repr___closed__11;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_instReprInitTemplate_repr___closed__0;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__3;
uint8_t l_System_FilePath_pathExists(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8;
LEAN_EXPORT uint8_t l_Lake_instInhabitedInitTemplate;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_IO_FS_createDirAll(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__8;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3;
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_toLower(uint32_t);
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
static lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20;
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_instReprInitTemplate_repr___closed__8;
static lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1;
static lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents(lean_object*);
lean_object* l_Lake_StdVer_toString(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__21;
static uint32_t l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static uint32_t l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0;
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5;
lean_object* l_Lake_ToolchainVer_ofString(lean_object*);
static lean_object* l_Lake_instReprInitTemplate_repr___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0;
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__2;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4;
extern lean_object* l_Std_Format_defWidth;
extern lean_object* l_Lake_defaultLakeDir;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4;
static lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1;
static lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__4;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__5;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__4;
static lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprInitTemplate_repr___closed__10;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(uint8_t, lean_object*, lean_object*, uint8_t);
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__4;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2;
extern lean_object* l_Lean_NameSet_empty;
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8;
static lean_object* l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0;
lean_object* lean_io_realpath(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14;
lean_object* lean_panic_fn(lean_object*, lean_object*);
static lean_object* l_Lake_instReprInitTemplate_repr___closed__7;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15;
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5;
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__3;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19;
LEAN_EXPORT lean_object* l_Lake_init(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_toUpperCamelCase(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents(lean_object*, lean_object*);
lean_object* l_Lake_GitRepo_checkoutBranch(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object*, uint8_t, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprInitTemplate_repr___closed__6;
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx(uint8_t);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_defaultConfigFile;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1;
static lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_defaultExeRoot___closed__0;
lean_object* l_Char_utf8Size(uint32_t);
lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_basicFileContents;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object*);
static lean_object* l_Lake_instReprInitTemplate_repr___closed__9;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__7;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__9;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx___boxed(lean_object*);
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
uint8_t l_Lake_GitRepo_insideWorkTree(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx(uint8_t);
extern lean_object* l_Lake_Git_upstreamBranch;
static size_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
static lean_object* _init_l_Lake_defaultExeRoot___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_defaultExeRoot___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_defaultExeRoot___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_defaultExeRoot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultExeRoot___closed__1;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultLakeDir;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1;
x_2 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
x_2 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__4;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def hello := \"world\"\n", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_basicFileContents() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- This module serves as the root of the `", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` library.\n-- Import modules here that should be built as part of the library.\nimport ", 86, 86);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".Basic\n", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0;
x_4 = lean_string_append(x_3, x_1);
x_5 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1;
x_6 = lean_string_append(x_4, x_5);
x_7 = 1;
x_8 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_7);
x_9 = lean_string_append(x_6, x_8);
lean_dec_ref(x_8);
x_10 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0;
x_3 = 1;
x_4 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2;
x_7 = lean_string_append(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = l_Lake_defaultExeRoot;
x_3 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lean", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1;
x_2 = l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileName() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\ndef main : IO Unit :=\n  IO.println s!\"Hello, {hello}!\"\n", 57, 57);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0;
x_3 = 1;
x_4 = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(x_1, x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec_ref(x_4);
x_6 = l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0;
x_7 = lean_string_append(x_5, x_6);
return x_7;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def main : IO Unit :=\n  IO.println s!\"Hello, world!\"\n", 53, 53);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_exeFileContents() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import Lake\nopen Lake DSL\n\npackage ", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_Format_defWidth;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n\nlean_lib ", 40, 40);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  -- add library configuration options here\n\n@[default_target]\nlean_exe ", 79, 79);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  root := `Main\n", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_2);
x_14 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_String_quote(x_3);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Std_Format_pretty(x_17, x_7, x_8, x_8);
x_19 = lean_string_append(x_15, x_18);
lean_dec_ref(x_18);
x_20 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__4;
x_21 = lean_string_append(x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name = ", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nversion = \"0.1.0\"\ndefaultTargets = [", 37, 37);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]\n\n[[lean_lib]]\nname = ", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n[[lean_exe]]\nname = ", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nroot = \"Main\"\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
x_17 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_String_quote(x_2);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Std_Format_pretty(x_20, x_7, x_8, x_8);
x_22 = lean_string_append(x_18, x_21);
lean_dec_ref(x_21);
x_23 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_15);
lean_dec_ref(x_15);
x_26 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4;
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n\n@[default_target]\nlean_exe ", 58, 58);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Std_Format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
lean_dec_ref(x_14);
x_16 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__4;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]\n\n[[lean_exe]]\nname = ", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Std_Format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
x_16 = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_14);
lean_dec_ref(x_14);
x_19 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4;
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n\n@[default_target]\nlean_lib ", 58, 58);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  -- add library configuration options here\n", 51, 51);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_Format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec_ref(x_8);
x_10 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Std_Format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
x_16 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_14);
lean_dec_ref(x_14);
x_19 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n  keywords := #[\"math\"]\n  leanOptions := #[\n    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`\n  ]\n\nrequire \"leanprover-community\" / \"mathlib\" @ git ", 191, 185);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n@[default_target]\nlean_lib ", 29, 29);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  -- add any library configuration options here\n", 55, 55);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
lean_dec_ref(x_15);
x_17 = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_2);
x_20 = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2;
x_21 = lean_string_append(x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nversion = \"0.1.0\"\nkeywords = [\"math\"]\ndefaultTargets = [", 57, 57);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]\n\n[leanOptions]\npp.unicode.fun = true # pretty-prints `fun a ↦ b`\n\n[[require]]\nname = \"mathlib\"\nscope = \"leanprover-community\"\nrev = ", 136, 134);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n[[lean_lib]]\nname = ", 22, 22);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_2);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
x_17 = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_String_quote(x_3);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Std_Format_pretty(x_20, x_7, x_8, x_8);
x_22 = lean_string_append(x_18, x_21);
lean_dec_ref(x_21);
x_23 = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_15);
lean_dec_ref(x_15);
x_26 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n  keywords := #[\"math\"]\n  leanOptions := #[\n    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`\n    ⟨`relaxedAutoImplicit, false⟩,\n    ⟨`maxSynthPendingDepth, .ofNat 3⟩,\n    ⟨`weak.linter.mathlibStandardSet, true⟩,\n  ]\n\nrequire \"leanprover-community\" / \"mathlib\" @ git ", 323, 305);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
lean_dec_ref(x_15);
x_17 = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_2);
x_20 = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2;
x_21 = lean_string_append(x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]\n\n[leanOptions]\npp.unicode.fun = true # pretty-prints `fun a ↦ b`\nrelaxedAutoImplicit = false\nweak.linter.mathlibStandardSet = true\nmaxSynthPendingDepth = 3\n\n[[require]]\nname = \"mathlib\"\nscope = \"leanprover-community\"\nrev = ", 227, 225);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0;
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec_ref(x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_2);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Std_Format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
x_17 = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_String_quote(x_3);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_Std_Format_pretty(x_20, x_7, x_8, x_8);
x_22 = lean_string_append(x_18, x_21);
lean_dec_ref(x_21);
x_23 = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_15);
lean_dec_ref(x_15);
x_26 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("# ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n## GitHub configuration\n\nTo set up your new GitHub repository, follow these steps:\n\n* Under your repository name, click **Settings**.\n* In the **Actions** section of the sidebar, click \"General\".\n* Check the box **Allow GitHub Actions to create and approve pull requests**.\n* Click the **Pages** section of the settings sidebar.\n* In the **Source** dropdown menu, select \"GitHub Actions\".\n\nAfter following the steps above, you can remove this section from the README file.\n", 475, 475);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0;
x_3 = lean_string_append(x_2, x_1);
x_4 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0;
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v5\n      - uses: leanprover/lean-action@v1\n", 200, 200);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\n# Sets permissions of the GITHUB_TOKEN to allow deployment to GitHub Pages\npermissions:\n  contents: read # Read access to repository contents\n  pages: write # Write access to GitHub Pages\n  id-token: write # Write access to ID tokens\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v5\n      - uses: leanprover/lean-action@v1\n      - uses: leanprover-community/docgen-action@v1\n", 487, 487);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: Update Dependencies\n\non:\n  # schedule:             # Sets a schedule to trigger the workflow\n  #   - cron: \"0 8 * * *\" # Every day at 08:00 AM UTC (see https://docs.github.com/en/actions/writing-workflows/choosing-when-your-workflow-runs/events-that-trigger-workflows#schedule)\n  workflow_dispatch:    # Allows the workflow to be triggered manually via the GitHub interface\n\njobs:\n  check-for-updates: # Determines which updates to apply.\n    runs-on: ubuntu-latest\n    outputs:\n      is-update-available: ${{ steps.check-for-updates.outputs.is-update-available }}\n      new-tags: ${{ steps.check-for-updates.outputs.new-tags }}\n    steps:\n      - name: Run the action\n        id: check-for-updates\n        uses: leanprover-community/mathlib-update-action@v1\n        # START CONFIGURATION BLOCK 1\n        # END CONFIGURATION BLOCK 1\n  do-update: # Runs the upgrade, tests it, and makes a PR/issue/commit.\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write      # Grants permission to push changes to the repository\n      issues: write        # Grants permission to create or update issues\n      pull-requests: write # Grants permission to create or update pull requests\n    needs: check-for-updates\n    if: ${{ needs.check-for-updates.outputs.is-update-available == 'true' }}\n    strategy: # Runs for each update discovered by the `check-for-updates` job.\n      max-parallel: 1 # Ensures that the PRs/issues are created in order.\n      matrix:\n        tag: ${{ fromJSON(needs.check-for-updates.outputs.new-tags) }}\n    steps:\n      - name: Run the action\n        id: update-the-repo\n        uses: leanprover-community/mathlib-update-action/do-update@v1\n        with:\n          tag: ${{ matrix.tag }}\n          # START CONFIGURATION BLOCK 2\n          on_update_succeeds: pr # Create a pull request if the update succeeds\n          on_update_fails: issue # Create an issue if the update fails\n          # END CONFIGURATION BLOCK 2\n", 1950, 1950);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: Create Release\n\non:\n  push:\n    branches:\n      - 'main'\n      - 'master'\n    paths:\n      - 'lean-toolchain'\n\njobs:\n  lean-release-tag:\n    name: Add Lean release tag\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n    - name: lean-release-tag action\n      uses: leanprover-community/lean-release-tag@v1\n      with:\n        do-release: true\n        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}\n", 427, 427);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents() {
_start:
{
lean_object* x_1; 
x_1 = l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_InitTemplate_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lake_InitTemplate_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = l_Lake_InitTemplate_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_std_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_std_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_exe_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_exe_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_lib_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_lib_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_mathLax_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_mathLax_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lake_InitTemplate_math_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_math_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.std", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprInitTemplate_repr___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.exe", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprInitTemplate_repr___closed__2;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.lib", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprInitTemplate_repr___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.mathLax", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprInitTemplate_repr___closed__6;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.math", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_instReprInitTemplate_repr___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate_repr___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; lean_object* x_17; lean_object* x_24; lean_object* x_31; 
switch (x_1) {
case 0:
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_unsigned_to_nat(1024u);
x_39 = lean_nat_dec_le(x_38, x_2);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Lake_instReprInitTemplate_repr___closed__10;
x_3 = x_40;
goto block_9;
}
else
{
lean_object* x_41; 
x_41 = l_Lake_instReprInitTemplate_repr___closed__11;
x_3 = x_41;
goto block_9;
}
}
case 1:
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_unsigned_to_nat(1024u);
x_43 = lean_nat_dec_le(x_42, x_2);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Lake_instReprInitTemplate_repr___closed__10;
x_10 = x_44;
goto block_16;
}
else
{
lean_object* x_45; 
x_45 = l_Lake_instReprInitTemplate_repr___closed__11;
x_10 = x_45;
goto block_16;
}
}
case 2:
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_unsigned_to_nat(1024u);
x_47 = lean_nat_dec_le(x_46, x_2);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Lake_instReprInitTemplate_repr___closed__10;
x_17 = x_48;
goto block_23;
}
else
{
lean_object* x_49; 
x_49 = l_Lake_instReprInitTemplate_repr___closed__11;
x_17 = x_49;
goto block_23;
}
}
case 3:
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_unsigned_to_nat(1024u);
x_51 = lean_nat_dec_le(x_50, x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lake_instReprInitTemplate_repr___closed__10;
x_24 = x_52;
goto block_30;
}
else
{
lean_object* x_53; 
x_53 = l_Lake_instReprInitTemplate_repr___closed__11;
x_24 = x_53;
goto block_30;
}
}
default: 
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_unsigned_to_nat(1024u);
x_55 = lean_nat_dec_le(x_54, x_2);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = l_Lake_instReprInitTemplate_repr___closed__10;
x_31 = x_56;
goto block_37;
}
else
{
lean_object* x_57; 
x_57 = l_Lake_instReprInitTemplate_repr___closed__11;
x_31 = x_57;
goto block_37;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lake_instReprInitTemplate_repr___closed__1;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = l_Lake_instReprInitTemplate_repr___closed__3;
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
block_23:
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = l_Lake_instReprInitTemplate_repr___closed__5;
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = 0;
x_21 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_20);
x_22 = l_Repr_addAppParen(x_21, x_2);
return x_22;
}
block_30:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lake_instReprInitTemplate_repr___closed__7;
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = 0;
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = l_Repr_addAppParen(x_28, x_2);
return x_29;
}
block_37:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lake_instReprInitTemplate_repr___closed__9;
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = 0;
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
x_36 = l_Repr_addAppParen(x_35, x_2);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = l_Lake_instReprInitTemplate_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instReprInitTemplate_repr___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_instReprInitTemplate___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_dec_le(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_dec_le(x_1, x_6);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = 4;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 3;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 2;
return x_10;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_le(x_1, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_InitTemplate_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lake_InitTemplate_ctorIdx(x_1);
x_4 = l_Lake_InitTemplate_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_instDecidableEqInitTemplate(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint8_t _init_l_Lake_instInhabitedInitTemplate() {
_start:
{
uint8_t x_1; 
x_1 = 0;
return x_1;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("std", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exe", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lib", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("math-lax", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("math", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 4;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__6() {
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
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__7() {
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
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__8() {
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
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__9() {
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lake_InitTemplate_ofString_x3f___closed__0;
x_3 = lean_string_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lake_InitTemplate_ofString_x3f___closed__1;
x_5 = lean_string_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lake_InitTemplate_ofString_x3f___closed__2;
x_7 = lean_string_dec_eq(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lake_InitTemplate_ofString_x3f___closed__3;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lake_InitTemplate_ofString_x3f___closed__4;
x_11 = lean_string_dec_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; 
x_13 = l_Lake_InitTemplate_ofString_x3f___closed__5;
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = l_Lake_InitTemplate_ofString_x3f___closed__6;
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = l_Lake_InitTemplate_ofString_x3f___closed__7;
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = l_Lake_InitTemplate_ofString_x3f___closed__8;
return x_16;
}
}
else
{
lean_object* x_17; 
x_17 = l_Lake_InitTemplate_ofString_x3f___closed__9;
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_ofString_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
static uint32_t _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0() {
_start:
{
uint32_t x_1; 
x_1 = l_Lean_idBeginEscape;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0;
x_2 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static uint32_t _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__3() {
_start:
{
uint32_t x_1; 
x_1 = l_Lean_idEndEscape;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__3;
x_2 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2;
x_3 = lean_string_append(x_2, x_1);
x_4 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__4;
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Init_0__Lake_escapeIdent(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CLI.Init", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private.Lake.CLI.Init.0.Lake.escapeName!", 41, 41);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2;
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_unsigned_to_nat(354u);
x_4 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1;
x_5 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2;
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_unsigned_to_nat(357u);
x_4 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1;
x_5 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3;
x_3 = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = l___private_Lake_CLI_Init_0__Lake_escapeIdent(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
x_9 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
x_10 = lean_string_append(x_8, x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_escapeIdent(x_7);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
return x_12;
}
}
default: 
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5;
x_14 = l_panic___at___00__private_Lake_CLI_Init_0__Lake_escapeName_x21_spec__0(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_9; uint8_t x_10; 
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = lean_nat_dec_eq(x_2, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_string_utf8_get_fast(x_1, x_2);
x_12 = 46;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
x_3 = x_11;
goto block_8;
}
else
{
uint32_t x_14; 
x_14 = 45;
x_3 = x_14;
goto block_8;
}
}
else
{
lean_dec(x_2);
return x_1;
}
block_8:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_2);
x_4 = lean_string_utf8_set(x_1, x_2, x_3);
x_5 = l_Char_utf8Size(x_3);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = 0;
x_3 = l_Lean_Name_toString(x_1, x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_string_utf8_get_fast(x_1, x_2);
x_6 = l_Char_toLower(x_5);
lean_inc(x_2);
x_7 = lean_string_utf8_set(x_1, x_2, x_6);
x_8 = l_Char_utf8Size(x_6);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_8);
lean_dec(x_2);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("master", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("v", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_39; 
x_39 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0;
x_7 = x_39;
goto block_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_5, 0);
lean_inc(x_40);
lean_dec_ref(x_5);
x_41 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1;
x_42 = l_Lake_StdVer_toString(x_40);
x_43 = lean_string_append(x_41, x_42);
lean_dec_ref(x_42);
x_7 = x_43;
goto block_38;
}
block_38:
{
switch (x_1) {
case 0:
{
lean_dec_ref(x_7);
if (x_2 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_9 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_10 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_6, x_9);
x_11 = l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents(x_6, x_8, x_10);
lean_dec_ref(x_8);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = 1;
x_13 = l_Lean_Name_toString(x_4, x_12);
x_14 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_15 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_6, x_14);
x_16 = l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents(x_6, x_13, x_15);
return x_16;
}
}
case 1:
{
lean_dec_ref(x_7);
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_18 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_6, x_17);
x_19 = l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents(x_6, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(0u);
lean_inc_ref(x_6);
x_21 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_6, x_20);
x_22 = l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(x_6, x_21);
return x_22;
}
}
case 2:
{
lean_dec_ref(x_7);
if (x_2 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_24 = l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(x_6, x_23);
lean_dec_ref(x_23);
return x_24;
}
else
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_25 = 1;
x_26 = l_Lean_Name_toString(x_4, x_25);
x_27 = l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(x_6, x_26);
return x_27;
}
}
case 3:
{
if (x_2 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_29 = l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents(x_6, x_28, x_7);
lean_dec_ref(x_28);
return x_29;
}
else
{
uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_30 = 1;
x_31 = l_Lean_Name_toString(x_4, x_30);
x_32 = l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents(x_6, x_31, x_7);
return x_32;
}
}
default: 
{
if (x_2 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_34 = l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents(x_6, x_33, x_7);
lean_dec_ref(x_33);
return x_34;
}
else
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 1;
x_36 = l_Lean_Name_toString(x_4, x_35);
x_37 = l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents(x_6, x_36, x_7);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox(x_2);
x_8 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("creating lean-action CI workflow", 32, 32);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".github", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("workflows", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_action_ci.yml", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("created lean-action CI workflow at '", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("update.yml", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("create-release.yml", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("created Mathlib update CI workflow at '", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("created create-release CI workflow at '", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("create-release CI workflow already exists", 41, 41);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Mathlib update CI workflow already exists", 41, 41);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean-action CI workflow already exists", 38, 38);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = 0;
x_6 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1;
x_7 = lean_array_push(x_3, x_6);
x_8 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2;
x_9 = l_Lake_joinRelative(x_1, x_8);
x_10 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3;
x_11 = l_Lake_joinRelative(x_9, x_10);
lean_inc_ref(x_11);
x_12 = l_IO_FS_createDirAll(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_72; 
lean_dec_ref(x_12);
x_13 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4;
lean_inc_ref(x_11);
x_14 = l_Lake_joinRelative(x_11, x_13);
x_72 = l_System_FilePath_pathExists(x_14);
if (x_72 == 0)
{
uint8_t x_73; uint8_t x_74; 
x_73 = 4;
x_74 = l_Lake_instDecidableEqInitTemplate(x_2, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0;
x_76 = l_IO_FS_writeFile(x_14, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_dec_ref(x_76);
x_15 = x_7;
x_16 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_io_error_to_string(x_77);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_array_get_size(x_7);
x_82 = lean_array_push(x_7, x_80);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0;
x_85 = l_IO_FS_writeFile(x_14, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_dec_ref(x_85);
x_15 = x_7;
x_16 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
x_87 = lean_io_error_to_string(x_86);
x_88 = 3;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_array_get_size(x_7);
x_91 = lean_array_push(x_7, x_89);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_14);
lean_dec_ref(x_11);
x_93 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16;
x_94 = lean_array_push(x_7, x_93);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
block_71:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_17 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5;
x_18 = lean_string_append(x_17, x_14);
lean_dec_ref(x_14);
x_19 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_5);
x_22 = lean_array_push(x_15, x_21);
x_23 = 4;
x_24 = l_Lake_instDecidableEqInitTemplate(x_2, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_11);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7;
lean_inc_ref(x_11);
x_28 = l_Lake_joinRelative(x_11, x_27);
x_29 = l_System_FilePath_pathExists(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0;
x_31 = l_IO_FS_writeFile(x_28, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_31);
x_32 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8;
x_33 = l_Lake_joinRelative(x_11, x_32);
x_34 = l_System_FilePath_pathExists(x_33);
x_35 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9;
x_36 = lean_string_append(x_35, x_28);
lean_dec_ref(x_28);
x_37 = lean_string_append(x_36, x_19);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_5);
x_39 = lean_array_push(x_22, x_38);
if (x_34 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0;
x_41 = l_IO_FS_writeFile(x_33, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_41);
x_42 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10;
x_43 = lean_string_append(x_42, x_33);
lean_dec_ref(x_33);
x_44 = lean_string_append(x_43, x_19);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_5);
x_46 = lean_box(0);
x_47 = lean_array_push(x_39, x_45);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_33);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec_ref(x_41);
x_50 = lean_io_error_to_string(x_49);
x_51 = 3;
x_52 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_51);
x_53 = lean_array_get_size(x_39);
x_54 = lean_array_push(x_39, x_52);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec_ref(x_33);
x_56 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12;
x_57 = lean_array_push(x_39, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_28);
lean_dec_ref(x_11);
x_60 = lean_ctor_get(x_31, 0);
lean_inc(x_60);
lean_dec_ref(x_31);
x_61 = lean_io_error_to_string(x_60);
x_62 = 3;
x_63 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
x_64 = lean_array_get_size(x_22);
x_65 = lean_array_push(x_22, x_63);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_28);
lean_dec_ref(x_11);
x_67 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14;
x_68 = lean_array_push(x_22, x_67);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec_ref(x_11);
x_97 = lean_ctor_get(x_12, 0);
lean_inc(x_97);
lean_dec_ref(x_12);
x_98 = lean_io_error_to_string(x_97);
x_99 = 3;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = lean_array_get_size(x_7);
x_102 = lean_array_push(x_7, x_100);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_1, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_2, x_1, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_2(x_1, x_2, lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg(x_1, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg(x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = 1;
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
lean_dec_ref(x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_4);
return x_14;
}
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_defaultConfigFile;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("creating a new math package with a non-release Lean toolchain; Mathlib may not work properly", 92, 92);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not create a `lean-toolchain` file for the new package; no known toolchain name for the current Elan/Lean/Lake", 116, 116);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".gitignore", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_toolchainFileName;
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to initialize git repository", 35, 35);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Git_upstreamBranch;
return x_1;
}
}
static uint8_t _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0;
x_2 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("README.md", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Basic.lean", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package already initialized", 27, 27);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__21;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; lean_object* x_478; uint8_t x_490; lean_object* x_491; lean_object* x_518; uint8_t x_519; 
x_13 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0;
x_399 = l_Lake_ConfigLang_fileExtension(x_4);
x_400 = l_System_FilePath_addExtension(x_13, x_399);
lean_dec_ref(x_399);
lean_inc_ref(x_1);
x_401 = l_Lake_joinRelative(x_1, x_400);
x_490 = l_System_FilePath_pathExists(x_401);
x_518 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_519 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_519 == 0)
{
x_491 = lean_box(0);
goto block_517;
}
else
{
uint8_t x_520; 
x_520 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_520 == 0)
{
x_491 = lean_box(0);
goto block_517;
}
else
{
lean_object* x_521; size_t x_522; size_t x_523; lean_object* x_524; 
x_521 = lean_box(0);
x_522 = 0;
x_523 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_524 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_518, x_522, x_523, x_521, x_7);
lean_dec_ref(x_524);
x_491 = lean_box(0);
goto block_517;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_31:
{
if (x_6 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_box(0);
x_19 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
lean_inc_ref(x_1);
x_20 = l_Lake_joinRelative(x_1, x_19);
lean_inc_ref(x_20);
x_21 = l_Lake_joinRelative(x_20, x_13);
x_22 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1;
x_23 = lean_box(1);
x_24 = lean_box(0);
x_25 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
x_26 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_1);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_19);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_13);
lean_ctor_set(x_26, 8, x_21);
lean_ctor_set(x_26, 9, x_22);
lean_ctor_set(x_26, 10, x_23);
lean_ctor_set(x_26, 11, x_24);
lean_ctor_set(x_26, 12, x_25);
lean_ctor_set(x_26, 13, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*14, x_6);
lean_ctor_set_uint8(x_26, sizeof(void*)*14 + 1, x_6);
lean_ctor_set_uint8(x_26, sizeof(void*)*14 + 2, x_6);
x_27 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2;
x_28 = l_Lake_updateManifest(x_26, x_27, x_14);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_14);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
block_37:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4;
lean_inc_ref(x_34);
x_36 = lean_apply_2(x_34, x_35, lean_box(0));
x_14 = x_34;
x_15 = lean_box(0);
goto block_31;
}
else
{
lean_dec_ref(x_33);
x_14 = x_34;
x_15 = lean_box(0);
goto block_31;
}
}
block_43:
{
switch (x_3) {
case 3:
{
x_32 = lean_box(0);
x_33 = x_38;
x_34 = x_39;
goto block_37;
}
case 4:
{
x_32 = lean_box(0);
x_33 = x_38;
x_34 = x_39;
goto block_37;
}
default: 
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
block_50:
{
if (x_46 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
lean_inc_ref(x_45);
x_49 = lean_apply_2(x_45, x_48, lean_box(0));
x_38 = x_44;
x_39 = x_45;
x_40 = lean_box(0);
goto block_43;
}
else
{
x_38 = x_44;
x_39 = x_45;
x_40 = lean_box(0);
goto block_43;
}
}
block_124:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_56 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7;
lean_inc_ref(x_1);
x_57 = l_Lake_joinRelative(x_1, x_56);
x_58 = 4;
x_59 = lean_io_prim_handle_mk(x_57, x_58);
lean_dec_ref(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
x_62 = lean_io_prim_handle_put_str(x_60, x_61);
lean_dec(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec_ref(x_62);
x_63 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8;
lean_inc_ref(x_1);
x_64 = l_Lake_joinRelative(x_1, x_63);
x_65 = lean_string_utf8_byte_size(x_51);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_53);
x_68 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
x_69 = lean_string_append(x_51, x_68);
x_70 = l_IO_FS_writeFile(x_64, x_69);
lean_dec_ref(x_69);
lean_dec_ref(x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
x_38 = x_52;
x_39 = x_54;
x_40 = lean_box(0);
goto block_43;
}
else
{
uint8_t x_71; 
lean_dec(x_52);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_io_error_to_string(x_72);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_apply_2(x_54, x_75, lean_box(0));
x_77 = lean_box(0);
lean_ctor_set(x_70, 0, x_77);
return x_70;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec(x_70);
x_79 = lean_io_error_to_string(x_78);
x_80 = 3;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = lean_apply_2(x_54, x_81, lean_box(0));
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec_ref(x_51);
x_85 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_85);
lean_dec_ref(x_53);
x_86 = lean_string_utf8_byte_size(x_85);
lean_dec_ref(x_85);
x_87 = lean_nat_dec_eq(x_86, x_66);
if (x_87 == 0)
{
uint8_t x_88; lean_object* x_89; uint8_t x_90; 
x_88 = l_System_FilePath_pathExists(x_64);
lean_dec_ref(x_64);
x_89 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_90 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_90 == 0)
{
x_44 = x_52;
x_45 = x_54;
x_46 = x_88;
x_47 = lean_box(0);
goto block_50;
}
else
{
uint8_t x_91; 
x_91 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_91 == 0)
{
x_44 = x_52;
x_45 = x_54;
x_46 = x_88;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; 
x_92 = lean_box(0);
x_93 = 0;
x_94 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_54);
x_95 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_89, x_93, x_94, x_92, x_54);
lean_dec_ref(x_95);
x_44 = x_52;
x_45 = x_54;
x_46 = x_88;
x_47 = lean_box(0);
goto block_50;
}
}
}
else
{
lean_dec_ref(x_64);
x_38 = x_52;
x_39 = x_54;
x_40 = lean_box(0);
goto block_43;
}
}
}
else
{
uint8_t x_96; 
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_62);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_62, 0);
x_98 = lean_io_error_to_string(x_97);
x_99 = 3;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = lean_apply_2(x_54, x_100, lean_box(0));
x_102 = lean_box(0);
lean_ctor_set(x_62, 0, x_102);
return x_62;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_62, 0);
lean_inc(x_103);
lean_dec(x_62);
x_104 = lean_io_error_to_string(x_103);
x_105 = 3;
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_105);
x_107 = lean_apply_2(x_54, x_106, lean_box(0));
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_110 = !lean_is_exclusive(x_59);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_59, 0);
x_112 = lean_io_error_to_string(x_111);
x_113 = 3;
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
x_115 = lean_apply_2(x_54, x_114, lean_box(0));
x_116 = lean_box(0);
lean_ctor_set(x_59, 0, x_116);
return x_59;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_59, 0);
lean_inc(x_117);
lean_dec(x_59);
x_118 = lean_io_error_to_string(x_117);
x_119 = 3;
x_120 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = lean_apply_2(x_54, x_120, lean_box(0));
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
block_132:
{
lean_object* x_130; lean_object* x_131; 
x_130 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15;
lean_inc_ref(x_128);
x_131 = lean_apply_2(x_128, x_130, lean_box(0));
x_51 = x_125;
x_52 = x_126;
x_53 = x_127;
x_54 = x_128;
x_55 = lean_box(0);
goto block_124;
}
block_159:
{
lean_object* x_138; uint8_t x_139; 
x_138 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
x_139 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17;
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_unsigned_to_nat(0u);
x_141 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_1);
x_142 = l_Lake_GitRepo_checkoutBranch(x_138, x_1, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_array_get_size(x_143);
x_145 = lean_nat_dec_lt(x_140, x_144);
if (x_145 == 0)
{
lean_dec(x_143);
x_51 = x_133;
x_52 = x_134;
x_53 = x_135;
x_54 = x_136;
x_55 = lean_box(0);
goto block_124;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_le(x_144, x_144);
if (x_146 == 0)
{
lean_dec(x_143);
x_51 = x_133;
x_52 = x_134;
x_53 = x_135;
x_54 = x_136;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_object* x_147; size_t x_148; size_t x_149; lean_object* x_150; 
x_147 = lean_box(0);
x_148 = 0;
x_149 = lean_usize_of_nat(x_144);
lean_inc_ref(x_136);
x_150 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_143, x_148, x_149, x_147, x_136);
lean_dec(x_143);
lean_dec_ref(x_150);
x_51 = x_133;
x_52 = x_134;
x_53 = x_135;
x_54 = x_136;
x_55 = lean_box(0);
goto block_124;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = lean_ctor_get(x_142, 1);
lean_inc(x_151);
lean_dec_ref(x_142);
x_152 = lean_array_get_size(x_151);
x_153 = lean_nat_dec_lt(x_140, x_152);
if (x_153 == 0)
{
lean_dec(x_151);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
else
{
uint8_t x_154; 
x_154 = lean_nat_dec_le(x_152, x_152);
if (x_154 == 0)
{
lean_dec(x_151);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_155; size_t x_156; size_t x_157; lean_object* x_158; 
x_155 = lean_box(0);
x_156 = 0;
x_157 = lean_usize_of_nat(x_152);
lean_inc_ref(x_136);
x_158 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_151, x_156, x_157, x_155, x_136);
lean_dec(x_151);
lean_dec_ref(x_158);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
}
}
}
else
{
x_51 = x_133;
x_52 = x_134;
x_53 = x_135;
x_54 = x_136;
x_55 = lean_box(0);
goto block_124;
}
}
block_185:
{
if (x_164 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_unsigned_to_nat(0u);
x_167 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_1);
x_168 = l_Lake_GitRepo_quietInit(x_1, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = lean_array_get_size(x_169);
x_171 = lean_nat_dec_lt(x_166, x_170);
if (x_171 == 0)
{
lean_dec(x_169);
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_163;
x_137 = lean_box(0);
goto block_159;
}
else
{
uint8_t x_172; 
x_172 = lean_nat_dec_le(x_170, x_170);
if (x_172 == 0)
{
lean_dec(x_169);
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_163;
x_137 = lean_box(0);
goto block_159;
}
else
{
lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; 
x_173 = lean_box(0);
x_174 = 0;
x_175 = lean_usize_of_nat(x_170);
lean_inc_ref(x_163);
x_176 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_169, x_174, x_175, x_173, x_163);
lean_dec(x_169);
lean_dec_ref(x_176);
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_163;
x_137 = lean_box(0);
goto block_159;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_168, 1);
lean_inc(x_177);
lean_dec_ref(x_168);
x_178 = lean_array_get_size(x_177);
x_179 = lean_nat_dec_lt(x_166, x_178);
if (x_179 == 0)
{
lean_dec(x_177);
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = x_163;
x_129 = lean_box(0);
goto block_132;
}
else
{
uint8_t x_180; 
x_180 = lean_nat_dec_le(x_178, x_178);
if (x_180 == 0)
{
lean_dec(x_177);
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = x_163;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_181; size_t x_182; size_t x_183; lean_object* x_184; 
x_181 = lean_box(0);
x_182 = 0;
x_183 = lean_usize_of_nat(x_178);
lean_inc_ref(x_163);
x_184 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_177, x_182, x_183, x_181, x_163);
lean_dec(x_177);
lean_dec_ref(x_184);
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = x_163;
x_129 = lean_box(0);
goto block_132;
}
}
}
}
else
{
x_51 = x_160;
x_52 = x_161;
x_53 = x_162;
x_54 = x_163;
x_55 = lean_box(0);
goto block_124;
}
}
block_199:
{
uint8_t x_191; lean_object* x_192; uint8_t x_193; 
lean_inc_ref(x_1);
x_191 = l_Lake_GitRepo_insideWorkTree(x_1);
x_192 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_193 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_193 == 0)
{
x_160 = x_186;
x_161 = x_187;
x_162 = x_188;
x_163 = x_189;
x_164 = x_191;
x_165 = lean_box(0);
goto block_185;
}
else
{
uint8_t x_194; 
x_194 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_194 == 0)
{
x_160 = x_186;
x_161 = x_187;
x_162 = x_188;
x_163 = x_189;
x_164 = x_191;
x_165 = lean_box(0);
goto block_185;
}
else
{
lean_object* x_195; size_t x_196; size_t x_197; lean_object* x_198; 
x_195 = lean_box(0);
x_196 = 0;
x_197 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_189);
x_198 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_192, x_196, x_197, x_195, x_189);
lean_dec_ref(x_198);
x_160 = x_186;
x_161 = x_187;
x_162 = x_188;
x_163 = x_189;
x_164 = x_191;
x_165 = lean_box(0);
goto block_185;
}
}
}
block_222:
{
lean_object* x_207; 
x_207 = l_IO_FS_writeFile(x_203, x_206);
lean_dec_ref(x_206);
lean_dec_ref(x_203);
if (lean_obj_tag(x_207) == 0)
{
lean_dec_ref(x_207);
x_186 = x_200;
x_187 = x_202;
x_188 = x_204;
x_189 = x_205;
x_190 = lean_box(0);
goto block_199;
}
else
{
uint8_t x_208; 
lean_dec_ref(x_204);
lean_dec(x_202);
lean_dec_ref(x_200);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_io_error_to_string(x_209);
x_211 = 3;
x_212 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_211);
x_213 = lean_apply_2(x_205, x_212, lean_box(0));
x_214 = lean_box(0);
lean_ctor_set(x_207, 0, x_214);
return x_207;
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_215 = lean_ctor_get(x_207, 0);
lean_inc(x_215);
lean_dec(x_207);
x_216 = lean_io_error_to_string(x_215);
x_217 = 3;
x_218 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*1, x_217);
x_219 = lean_apply_2(x_205, x_218, lean_box(0));
x_220 = lean_box(0);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
}
block_236:
{
if (x_228 == 0)
{
uint8_t x_230; uint8_t x_231; 
x_230 = 4;
x_231 = l_Lake_instDecidableEqInitTemplate(x_3, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_233 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_232);
lean_dec_ref(x_232);
x_200 = x_223;
x_201 = lean_box(0);
x_202 = x_224;
x_203 = x_225;
x_204 = x_226;
x_205 = x_227;
x_206 = x_233;
goto block_222;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_235 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_234);
lean_dec_ref(x_234);
x_200 = x_223;
x_201 = lean_box(0);
x_202 = x_224;
x_203 = x_225;
x_204 = x_226;
x_205 = x_227;
x_206 = x_235;
goto block_222;
}
}
else
{
lean_dec_ref(x_225);
lean_dec(x_2);
x_186 = x_223;
x_187 = x_224;
x_188 = x_226;
x_189 = x_227;
x_190 = lean_box(0);
goto block_199;
}
}
block_252:
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; uint8_t x_246; 
x_242 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18;
lean_inc_ref(x_1);
x_243 = l_Lake_joinRelative(x_1, x_242);
x_244 = l_System_FilePath_pathExists(x_243);
x_245 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_246 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_246 == 0)
{
x_223 = x_237;
x_224 = x_238;
x_225 = x_243;
x_226 = x_239;
x_227 = x_240;
x_228 = x_244;
x_229 = lean_box(0);
goto block_236;
}
else
{
uint8_t x_247; 
x_247 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_247 == 0)
{
x_223 = x_237;
x_224 = x_238;
x_225 = x_243;
x_226 = x_239;
x_227 = x_240;
x_228 = x_244;
x_229 = lean_box(0);
goto block_236;
}
else
{
lean_object* x_248; size_t x_249; size_t x_250; lean_object* x_251; 
x_248 = lean_box(0);
x_249 = 0;
x_250 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_240);
x_251 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_245, x_249, x_250, x_248, x_240);
lean_dec_ref(x_251);
x_223 = x_237;
x_224 = x_238;
x_225 = x_243;
x_226 = x_239;
x_227 = x_240;
x_228 = x_244;
x_229 = lean_box(0);
goto block_236;
}
}
}
block_295:
{
if (x_259 == 0)
{
uint8_t x_261; uint8_t x_262; 
x_261 = 1;
x_262 = l_Lake_instDecidableEqInitTemplate(x_3, x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_256);
x_264 = l_IO_FS_writeFile(x_253, x_263);
lean_dec_ref(x_263);
lean_dec_ref(x_253);
if (lean_obj_tag(x_264) == 0)
{
lean_dec_ref(x_264);
x_237 = x_254;
x_238 = x_255;
x_239 = x_258;
x_240 = x_257;
x_241 = lean_box(0);
goto block_252;
}
else
{
uint8_t x_265; 
lean_dec_ref(x_258);
lean_dec(x_255);
lean_dec_ref(x_254);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_io_error_to_string(x_266);
x_268 = 3;
x_269 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set_uint8(x_269, sizeof(void*)*1, x_268);
x_270 = lean_apply_2(x_257, x_269, lean_box(0));
x_271 = lean_box(0);
lean_ctor_set(x_264, 0, x_271);
return x_264;
}
else
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = lean_ctor_get(x_264, 0);
lean_inc(x_272);
lean_dec(x_264);
x_273 = lean_io_error_to_string(x_272);
x_274 = 3;
x_275 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*1, x_274);
x_276 = lean_apply_2(x_257, x_275, lean_box(0));
x_277 = lean_box(0);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_277);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_256);
x_279 = l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
x_280 = l_IO_FS_writeFile(x_253, x_279);
lean_dec_ref(x_253);
if (lean_obj_tag(x_280) == 0)
{
lean_dec_ref(x_280);
x_237 = x_254;
x_238 = x_255;
x_239 = x_258;
x_240 = x_257;
x_241 = lean_box(0);
goto block_252;
}
else
{
uint8_t x_281; 
lean_dec_ref(x_258);
lean_dec(x_255);
lean_dec_ref(x_254);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = lean_io_error_to_string(x_282);
x_284 = 3;
x_285 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set_uint8(x_285, sizeof(void*)*1, x_284);
x_286 = lean_apply_2(x_257, x_285, lean_box(0));
x_287 = lean_box(0);
lean_ctor_set(x_280, 0, x_287);
return x_280;
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_288 = lean_ctor_get(x_280, 0);
lean_inc(x_288);
lean_dec(x_280);
x_289 = lean_io_error_to_string(x_288);
x_290 = 3;
x_291 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set_uint8(x_291, sizeof(void*)*1, x_290);
x_292 = lean_apply_2(x_257, x_291, lean_box(0));
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
}
else
{
lean_dec(x_256);
lean_dec_ref(x_253);
x_237 = x_254;
x_238 = x_255;
x_239 = x_258;
x_240 = x_257;
x_241 = lean_box(0);
goto block_252;
}
}
block_312:
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; uint8_t x_306; 
x_302 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_1);
x_303 = l_Lake_joinRelative(x_1, x_302);
x_304 = l_System_FilePath_pathExists(x_303);
x_305 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_306 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_306 == 0)
{
x_253 = x_303;
x_254 = x_296;
x_255 = x_297;
x_256 = x_298;
x_257 = x_299;
x_258 = x_300;
x_259 = x_304;
x_260 = lean_box(0);
goto block_295;
}
else
{
uint8_t x_307; 
x_307 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_307 == 0)
{
x_253 = x_303;
x_254 = x_296;
x_255 = x_297;
x_256 = x_298;
x_257 = x_299;
x_258 = x_300;
x_259 = x_304;
x_260 = lean_box(0);
goto block_295;
}
else
{
lean_object* x_308; size_t x_309; size_t x_310; lean_object* x_311; 
x_308 = lean_box(0);
x_309 = 0;
x_310 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_299);
x_311 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_305, x_309, x_310, x_308, x_299);
lean_dec_ref(x_311);
x_253 = x_303;
x_254 = x_296;
x_255 = x_297;
x_256 = x_298;
x_257 = x_299;
x_258 = x_300;
x_259 = x_304;
x_260 = lean_box(0);
goto block_295;
}
}
}
block_319:
{
switch (x_3) {
case 0:
{
x_296 = x_313;
x_297 = x_314;
x_298 = x_315;
x_299 = x_317;
x_300 = x_316;
x_301 = lean_box(0);
goto block_312;
}
case 1:
{
x_296 = x_313;
x_297 = x_314;
x_298 = x_315;
x_299 = x_317;
x_300 = x_316;
x_301 = lean_box(0);
goto block_312;
}
default: 
{
lean_dec(x_315);
x_237 = x_313;
x_238 = x_314;
x_239 = x_316;
x_240 = x_317;
x_241 = lean_box(0);
goto block_252;
}
}
}
block_343:
{
lean_object* x_328; 
x_328 = l_IO_FS_writeFile(x_324, x_327);
lean_dec_ref(x_327);
lean_dec_ref(x_324);
if (lean_obj_tag(x_328) == 0)
{
lean_dec_ref(x_328);
x_313 = x_320;
x_314 = x_321;
x_315 = x_322;
x_316 = x_325;
x_317 = x_323;
x_318 = lean_box(0);
goto block_319;
}
else
{
uint8_t x_329; 
lean_dec_ref(x_325);
lean_dec(x_322);
lean_dec(x_321);
lean_dec_ref(x_320);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_330 = lean_ctor_get(x_328, 0);
x_331 = lean_io_error_to_string(x_330);
x_332 = 3;
x_333 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set_uint8(x_333, sizeof(void*)*1, x_332);
x_334 = lean_apply_2(x_323, x_333, lean_box(0));
x_335 = lean_box(0);
lean_ctor_set(x_328, 0, x_335);
return x_328;
}
else
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_336 = lean_ctor_get(x_328, 0);
lean_inc(x_336);
lean_dec(x_328);
x_337 = lean_io_error_to_string(x_336);
x_338 = 3;
x_339 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set_uint8(x_339, sizeof(void*)*1, x_338);
x_340 = lean_apply_2(x_323, x_339, lean_box(0));
x_341 = lean_box(0);
x_342 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_342, 0, x_341);
return x_342;
}
}
}
block_357:
{
uint8_t x_351; uint8_t x_352; 
x_351 = 4;
x_352 = l_Lake_instDecidableEqInitTemplate(x_3, x_351);
if (x_352 == 0)
{
uint8_t x_353; lean_object* x_354; lean_object* x_355; 
x_353 = 1;
lean_inc(x_346);
x_354 = l_Lean_Name_toString(x_346, x_353);
lean_inc(x_346);
x_355 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_354, x_346);
lean_dec_ref(x_354);
x_320 = x_344;
x_321 = x_345;
x_322 = x_346;
x_323 = x_349;
x_324 = x_347;
x_325 = x_348;
x_326 = lean_box(0);
x_327 = x_355;
goto block_343;
}
else
{
lean_object* x_356; 
lean_inc(x_346);
x_356 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_346);
x_320 = x_344;
x_321 = x_345;
x_322 = x_346;
x_323 = x_349;
x_324 = x_347;
x_325 = x_348;
x_326 = lean_box(0);
x_327 = x_356;
goto block_343;
}
}
block_398:
{
if (x_365 == 0)
{
lean_object* x_367; 
x_367 = l_IO_FS_createDirAll(x_360);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; 
lean_dec_ref(x_367);
x_368 = l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
x_369 = l_IO_FS_writeFile(x_359, x_368);
lean_dec_ref(x_359);
if (lean_obj_tag(x_369) == 0)
{
lean_dec_ref(x_369);
x_344 = x_358;
x_345 = x_361;
x_346 = x_362;
x_347 = x_363;
x_348 = x_364;
x_349 = x_7;
x_350 = lean_box(0);
goto block_357;
}
else
{
uint8_t x_370; 
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec_ref(x_358);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_370 = !lean_is_exclusive(x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_371 = lean_ctor_get(x_369, 0);
x_372 = lean_io_error_to_string(x_371);
x_373 = 3;
x_374 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*1, x_373);
x_375 = lean_apply_2(x_7, x_374, lean_box(0));
x_376 = lean_box(0);
lean_ctor_set(x_369, 0, x_376);
return x_369;
}
else
{
lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_377 = lean_ctor_get(x_369, 0);
lean_inc(x_377);
lean_dec(x_369);
x_378 = lean_io_error_to_string(x_377);
x_379 = 3;
x_380 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set_uint8(x_380, sizeof(void*)*1, x_379);
x_381 = lean_apply_2(x_7, x_380, lean_box(0));
x_382 = lean_box(0);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
return x_383;
}
}
}
else
{
uint8_t x_384; 
lean_dec_ref(x_364);
lean_dec_ref(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec_ref(x_359);
lean_dec_ref(x_358);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_384 = !lean_is_exclusive(x_367);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_385 = lean_ctor_get(x_367, 0);
x_386 = lean_io_error_to_string(x_385);
x_387 = 3;
x_388 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*1, x_387);
x_389 = lean_apply_2(x_7, x_388, lean_box(0));
x_390 = lean_box(0);
lean_ctor_set(x_367, 0, x_390);
return x_367;
}
else
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_391 = lean_ctor_get(x_367, 0);
lean_inc(x_391);
lean_dec(x_367);
x_392 = lean_io_error_to_string(x_391);
x_393 = 3;
x_394 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*1, x_393);
x_395 = lean_apply_2(x_7, x_394, lean_box(0));
x_396 = lean_box(0);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
return x_397;
}
}
}
else
{
lean_dec_ref(x_360);
lean_dec_ref(x_359);
x_344 = x_358;
x_345 = x_361;
x_346 = x_362;
x_347 = x_363;
x_348 = x_364;
x_349 = x_7;
x_350 = lean_box(0);
goto block_357;
}
}
block_437:
{
lean_object* x_408; lean_object* x_409; 
lean_inc(x_407);
lean_inc(x_404);
lean_inc(x_2);
x_408 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_3, x_4, x_2, x_404, x_407);
x_409 = l_IO_FS_writeFile(x_401, x_408);
lean_dec_ref(x_408);
lean_dec_ref(x_401);
if (lean_obj_tag(x_409) == 0)
{
lean_dec_ref(x_409);
if (lean_obj_tag(x_403) == 1)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; uint8_t x_417; 
x_410 = lean_ctor_get(x_403, 0);
lean_inc(x_410);
lean_dec_ref(x_403);
x_411 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
lean_inc(x_410);
x_412 = l_System_FilePath_withExtension(x_410, x_411);
x_413 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19;
lean_inc_ref(x_412);
x_414 = l_Lake_joinRelative(x_412, x_413);
x_415 = l_System_FilePath_pathExists(x_414);
x_416 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_417 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_417 == 0)
{
x_358 = x_402;
x_359 = x_414;
x_360 = x_412;
x_361 = x_407;
x_362 = x_404;
x_363 = x_410;
x_364 = x_406;
x_365 = x_415;
x_366 = lean_box(0);
goto block_398;
}
else
{
uint8_t x_418; 
x_418 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_418 == 0)
{
x_358 = x_402;
x_359 = x_414;
x_360 = x_412;
x_361 = x_407;
x_362 = x_404;
x_363 = x_410;
x_364 = x_406;
x_365 = x_415;
x_366 = lean_box(0);
goto block_398;
}
else
{
lean_object* x_419; size_t x_420; size_t x_421; lean_object* x_422; 
x_419 = lean_box(0);
x_420 = 0;
x_421 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_422 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_416, x_420, x_421, x_419, x_7);
lean_dec_ref(x_422);
x_358 = x_402;
x_359 = x_414;
x_360 = x_412;
x_361 = x_407;
x_362 = x_404;
x_363 = x_410;
x_364 = x_406;
x_365 = x_415;
x_366 = lean_box(0);
goto block_398;
}
}
}
else
{
lean_dec(x_403);
x_313 = x_402;
x_314 = x_407;
x_315 = x_404;
x_316 = x_406;
x_317 = x_7;
x_318 = lean_box(0);
goto block_319;
}
}
else
{
uint8_t x_423; 
lean_dec(x_407);
lean_dec_ref(x_406);
lean_dec(x_404);
lean_dec(x_403);
lean_dec_ref(x_402);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_423 = !lean_is_exclusive(x_409);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_ctor_get(x_409, 0);
x_425 = lean_io_error_to_string(x_424);
x_426 = 3;
x_427 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set_uint8(x_427, sizeof(void*)*1, x_426);
x_428 = lean_apply_2(x_7, x_427, lean_box(0));
x_429 = lean_box(0);
lean_ctor_set(x_409, 0, x_429);
return x_409;
}
else
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_430 = lean_ctor_get(x_409, 0);
lean_inc(x_430);
lean_dec(x_409);
x_431 = lean_io_error_to_string(x_430);
x_432 = 3;
x_433 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*1, x_432);
x_434 = lean_apply_2(x_7, x_433, lean_box(0));
x_435 = lean_box(0);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_435);
return x_436;
}
}
}
block_447:
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_5, 1);
x_442 = lean_ctor_get(x_5, 15);
lean_inc_ref(x_442);
x_443 = l_Lake_ToolchainVer_ofString(x_442);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_443, 1);
lean_inc_ref(x_444);
lean_dec_ref(x_443);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_444);
lean_inc_ref(x_441);
lean_inc_ref(x_442);
x_402 = x_442;
x_403 = x_439;
x_404 = x_438;
x_405 = lean_box(0);
x_406 = x_441;
x_407 = x_445;
goto block_437;
}
else
{
lean_object* x_446; 
lean_dec_ref(x_443);
x_446 = lean_box(0);
lean_inc_ref(x_441);
lean_inc_ref(x_442);
x_402 = x_442;
x_403 = x_439;
x_404 = x_438;
x_405 = lean_box(0);
x_406 = x_441;
x_407 = x_446;
goto block_437;
}
}
block_454:
{
if (x_450 == 0)
{
lean_object* x_452; 
x_452 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_452, 0, x_449);
x_438 = x_448;
x_439 = x_452;
x_440 = lean_box(0);
goto block_447;
}
else
{
lean_object* x_453; 
lean_dec_ref(x_449);
x_453 = lean_box(0);
x_438 = x_448;
x_439 = x_453;
x_440 = lean_box(0);
goto block_447;
}
}
block_470:
{
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; uint8_t x_463; 
lean_dec_ref(x_456);
lean_inc(x_2);
x_459 = l_Lake_toUpperCamelCase(x_2);
lean_inc(x_459);
x_460 = l_Lean_modToFilePath(x_1, x_459, x_455);
lean_dec_ref(x_455);
x_461 = l_System_FilePath_pathExists(x_460);
x_462 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_463 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_463 == 0)
{
x_448 = x_459;
x_449 = x_460;
x_450 = x_461;
x_451 = lean_box(0);
goto block_454;
}
else
{
uint8_t x_464; 
x_464 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_464 == 0)
{
x_448 = x_459;
x_449 = x_460;
x_450 = x_461;
x_451 = lean_box(0);
goto block_454;
}
else
{
lean_object* x_465; size_t x_466; size_t x_467; lean_object* x_468; 
x_465 = lean_box(0);
x_466 = 0;
x_467 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_468 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_462, x_466, x_467, x_465, x_7);
lean_dec_ref(x_468);
x_448 = x_459;
x_449 = x_460;
x_450 = x_461;
x_451 = lean_box(0);
goto block_454;
}
}
}
else
{
lean_object* x_469; 
lean_dec_ref(x_455);
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_456);
lean_inc(x_2);
x_438 = x_2;
x_439 = x_469;
x_440 = lean_box(0);
goto block_447;
}
}
block_477:
{
uint8_t x_475; uint8_t x_476; 
x_475 = 1;
x_476 = l_Lake_instDecidableEqInitTemplate(x_3, x_475);
if (x_476 == 0)
{
x_455 = x_471;
x_456 = x_472;
x_457 = lean_box(0);
x_458 = x_473;
goto block_470;
}
else
{
x_455 = x_471;
x_456 = x_472;
x_457 = lean_box(0);
x_458 = x_476;
goto block_470;
}
}
block_489:
{
lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; uint8_t x_483; 
x_479 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20;
lean_inc(x_2);
x_480 = l_Lean_modToFilePath(x_1, x_2, x_479);
x_481 = l_System_FilePath_pathExists(x_480);
x_482 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_483 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_483 == 0)
{
x_471 = x_479;
x_472 = x_480;
x_473 = x_481;
x_474 = lean_box(0);
goto block_477;
}
else
{
uint8_t x_484; 
x_484 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_484 == 0)
{
x_471 = x_479;
x_472 = x_480;
x_473 = x_481;
x_474 = lean_box(0);
goto block_477;
}
else
{
lean_object* x_485; size_t x_486; size_t x_487; lean_object* x_488; 
x_485 = lean_box(0);
x_486 = 0;
x_487 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_488 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_482, x_486, x_487, x_485, x_7);
lean_dec_ref(x_488);
x_471 = x_479;
x_472 = x_480;
x_473 = x_481;
x_474 = lean_box(0);
goto block_477;
}
}
}
block_517:
{
if (x_490 == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_unsigned_to_nat(0u);
x_493 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_1);
x_494 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_1, x_3, x_493);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec_ref(x_494);
x_496 = lean_array_get_size(x_495);
x_497 = lean_nat_dec_lt(x_492, x_496);
if (x_497 == 0)
{
lean_dec(x_495);
x_478 = lean_box(0);
goto block_489;
}
else
{
uint8_t x_498; 
x_498 = lean_nat_dec_le(x_496, x_496);
if (x_498 == 0)
{
lean_dec(x_495);
x_478 = lean_box(0);
goto block_489;
}
else
{
lean_object* x_499; size_t x_500; size_t x_501; lean_object* x_502; 
x_499 = lean_box(0);
x_500 = 0;
x_501 = lean_usize_of_nat(x_496);
lean_inc_ref(x_7);
x_502 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_495, x_500, x_501, x_499, x_7);
lean_dec(x_495);
lean_dec_ref(x_502);
x_478 = lean_box(0);
goto block_489;
}
}
}
else
{
lean_object* x_503; lean_object* x_504; uint8_t x_505; 
lean_dec_ref(x_401);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_503 = lean_ctor_get(x_494, 1);
lean_inc(x_503);
lean_dec_ref(x_494);
x_504 = lean_array_get_size(x_503);
x_505 = lean_nat_dec_lt(x_492, x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; 
lean_dec(x_503);
lean_dec_ref(x_7);
x_506 = lean_box(0);
x_507 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_507, 0, x_506);
return x_507;
}
else
{
uint8_t x_508; 
x_508 = lean_nat_dec_le(x_504, x_504);
if (x_508 == 0)
{
lean_dec(x_503);
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_509; size_t x_510; size_t x_511; lean_object* x_512; 
x_509 = lean_box(0);
x_510 = 0;
x_511 = lean_usize_of_nat(x_504);
x_512 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_503, x_510, x_511, x_509, x_7);
lean_dec(x_503);
lean_dec_ref(x_512);
x_9 = lean_box(0);
goto block_12;
}
}
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec_ref(x_401);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_513 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22;
x_514 = lean_apply_2(x_7, x_513, lean_box(0));
x_515 = lean_box(0);
x_516 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_516, 0, x_515);
return x_516;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___redArg(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_1, x_7, x_8, x_4, x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_3);
x_10 = lean_unbox(x_4);
x_11 = lean_unbox(x_6);
x_12 = l___private_Lake_CLI_Init_0__Lake_initPkg(x_1, x_2, x_9, x_10, x_5, x_11, x_7);
return x_12;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1;
x_2 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_2, 2);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_nat_dec_eq(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_nat_add(x_6, x_3);
lean_dec(x_3);
x_11 = lean_string_utf8_get_fast(x_5, x_10);
x_12 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0;
x_13 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2;
x_14 = lean_box_uint32(x_11);
x_15 = l_List_elem___redArg(x_12, x_14, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_string_utf8_next_fast(x_5, x_10);
lean_dec(x_10);
x_17 = lean_nat_sub(x_16, x_6);
{
lean_object* _tmp_2 = x_17;
uint8_t _tmp_3 = x_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_dec(x_10);
return x_15;
}
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(x_1, x_2, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(x_3, x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_sub(x_4, x_3);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_8 = lean_string_utf8_get_fast(x_2, x_3);
x_9 = 46;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_string_utf8_next_fast(x_2, x_3);
x_13 = lean_nat_sub(x_12, x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
else
{
lean_object* x_15; 
x_15 = lean_box(0);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_add(x_4, x_2);
lean_inc(x_5);
lean_inc_ref(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_5);
x_8 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(x_7);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_9);
x_11 = lean_nat_dec_lt(x_2, x_10);
lean_dec(x_2);
if (x_11 == 0)
{
lean_dec(x_10);
return x_7;
}
else
{
lean_dec_ref(x_7);
x_2 = x_10;
goto _start;
}
}
else
{
lean_dec(x_8);
lean_dec(x_2);
return x_7;
}
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("illegal package name '", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("main", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5;
x_2 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6;
x_2 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7;
x_2 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reserved package name", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_14; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_string_utf8_byte_size(x_1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc_ref(x_1);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_30);
x_34 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(x_33, x_31);
lean_dec_ref(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 2);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = lean_nat_sub(x_36, x_35);
lean_dec(x_35);
lean_dec(x_36);
x_38 = lean_nat_dec_eq(x_37, x_31);
lean_dec(x_37);
x_14 = x_38;
goto block_29;
}
else
{
x_14 = x_32;
goto block_29;
}
block_13:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0;
x_5 = lean_string_append(x_4, x_1);
lean_dec_ref(x_1);
x_6 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
x_7 = lean_string_append(x_5, x_6);
x_8 = 3;
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_8);
x_10 = lean_array_get_size(x_2);
x_11 = lean_array_push(x_2, x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
block_29:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_string_utf8_byte_size(x_1);
lean_inc_ref(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(x_17);
lean_dec_ref(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1;
x_20 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_1, x_15);
x_21 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8;
x_22 = l_List_elem___redArg(x_19, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10;
x_26 = lean_array_get_size(x_2);
x_27 = lean_array_push(x_2, x_25);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
goto block_13;
}
}
else
{
goto block_13;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = lean_unbox(x_1);
x_9 = lean_unbox(x_6);
x_10 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0(x_8, x_2, x_3, x_4, x_5, x_9, x_7);
lean_dec_ref(x_2);
x_11 = lean_box(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_Slice_Pattern_ForwardPattern_defaultDropPrefix_x3f___at___00__private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__2_spec__2(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox(x_1);
x_6 = lean_unbox(x_4);
x_7 = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg(x_5, x_2, x_3, x_6);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_init___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("illegal package name: could not derive one from '", 49, 49);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; lean_object* x_366; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_448; lean_object* x_449; uint8_t x_450; lean_object* x_451; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; lean_object* x_478; uint8_t x_490; lean_object* x_491; lean_object* x_518; uint8_t x_519; 
x_13 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0;
x_399 = l_Lake_ConfigLang_fileExtension(x_5);
x_400 = l_System_FilePath_addExtension(x_13, x_399);
lean_dec_ref(x_399);
lean_inc_ref(x_2);
x_401 = l_Lake_joinRelative(x_2, x_400);
x_490 = l_System_FilePath_pathExists(x_401);
x_518 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_519 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_519 == 0)
{
x_491 = lean_box(0);
goto block_517;
}
else
{
uint8_t x_520; 
x_520 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_520 == 0)
{
x_491 = lean_box(0);
goto block_517;
}
else
{
lean_object* x_521; size_t x_522; size_t x_523; lean_object* x_524; 
x_521 = lean_box(0);
x_522 = 0;
x_523 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_524 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_518, x_522, x_523, x_521, x_1);
lean_dec_ref(x_524);
x_491 = lean_box(0);
goto block_517;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_31:
{
if (x_7 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_16 = lean_box(0);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_box(0);
x_19 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
lean_inc_ref(x_2);
x_20 = l_Lake_joinRelative(x_2, x_19);
lean_inc_ref(x_20);
x_21 = l_Lake_joinRelative(x_20, x_13);
x_22 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1;
x_23 = lean_box(1);
x_24 = lean_box(0);
x_25 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
x_26 = lean_alloc_ctor(0, 14, 3);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_2);
lean_ctor_set(x_26, 3, x_17);
lean_ctor_set(x_26, 4, x_18);
lean_ctor_set(x_26, 5, x_19);
lean_ctor_set(x_26, 6, x_20);
lean_ctor_set(x_26, 7, x_13);
lean_ctor_set(x_26, 8, x_21);
lean_ctor_set(x_26, 9, x_22);
lean_ctor_set(x_26, 10, x_23);
lean_ctor_set(x_26, 11, x_24);
lean_ctor_set(x_26, 12, x_25);
lean_ctor_set(x_26, 13, x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*14, x_7);
lean_ctor_set_uint8(x_26, sizeof(void*)*14 + 1, x_7);
lean_ctor_set_uint8(x_26, sizeof(void*)*14 + 2, x_7);
x_27 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2;
x_28 = l_Lake_updateManifest(x_26, x_27, x_14);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_14);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
block_37:
{
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4;
lean_inc_ref(x_34);
x_36 = lean_apply_2(x_34, x_35, lean_box(0));
x_14 = x_34;
x_15 = lean_box(0);
goto block_31;
}
else
{
lean_dec_ref(x_33);
x_14 = x_34;
x_15 = lean_box(0);
goto block_31;
}
}
block_43:
{
switch (x_4) {
case 3:
{
x_32 = lean_box(0);
x_33 = x_38;
x_34 = x_39;
goto block_37;
}
case 4:
{
x_32 = lean_box(0);
x_33 = x_38;
x_34 = x_39;
goto block_37;
}
default: 
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
block_50:
{
if (x_46 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
lean_inc_ref(x_45);
x_49 = lean_apply_2(x_45, x_48, lean_box(0));
x_38 = x_44;
x_39 = x_45;
x_40 = lean_box(0);
goto block_43;
}
else
{
x_38 = x_44;
x_39 = x_45;
x_40 = lean_box(0);
goto block_43;
}
}
block_124:
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_56 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7;
lean_inc_ref(x_2);
x_57 = l_Lake_joinRelative(x_2, x_56);
x_58 = 4;
x_59 = lean_io_prim_handle_mk(x_57, x_58);
lean_dec_ref(x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
x_62 = lean_io_prim_handle_put_str(x_60, x_61);
lean_dec(x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec_ref(x_62);
x_63 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8;
lean_inc_ref(x_2);
x_64 = l_Lake_joinRelative(x_2, x_63);
x_65 = lean_string_utf8_byte_size(x_52);
x_66 = lean_unsigned_to_nat(0u);
x_67 = lean_nat_dec_eq(x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec_ref(x_53);
x_68 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
x_69 = lean_string_append(x_52, x_68);
x_70 = l_IO_FS_writeFile(x_64, x_69);
lean_dec_ref(x_69);
lean_dec_ref(x_64);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
x_38 = x_51;
x_39 = x_54;
x_40 = lean_box(0);
goto block_43;
}
else
{
uint8_t x_71; 
lean_dec(x_51);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_io_error_to_string(x_72);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_apply_2(x_54, x_75, lean_box(0));
x_77 = lean_box(0);
lean_ctor_set(x_70, 0, x_77);
return x_70;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec(x_70);
x_79 = lean_io_error_to_string(x_78);
x_80 = 3;
x_81 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_80);
x_82 = lean_apply_2(x_54, x_81, lean_box(0));
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
lean_dec_ref(x_52);
x_85 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_85);
lean_dec_ref(x_53);
x_86 = lean_string_utf8_byte_size(x_85);
lean_dec_ref(x_85);
x_87 = lean_nat_dec_eq(x_86, x_66);
if (x_87 == 0)
{
uint8_t x_88; lean_object* x_89; uint8_t x_90; 
x_88 = l_System_FilePath_pathExists(x_64);
lean_dec_ref(x_64);
x_89 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_90 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_90 == 0)
{
x_44 = x_51;
x_45 = x_54;
x_46 = x_88;
x_47 = lean_box(0);
goto block_50;
}
else
{
uint8_t x_91; 
x_91 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_91 == 0)
{
x_44 = x_51;
x_45 = x_54;
x_46 = x_88;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_object* x_92; size_t x_93; size_t x_94; lean_object* x_95; 
x_92 = lean_box(0);
x_93 = 0;
x_94 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_54);
x_95 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_89, x_93, x_94, x_92, x_54);
lean_dec_ref(x_95);
x_44 = x_51;
x_45 = x_54;
x_46 = x_88;
x_47 = lean_box(0);
goto block_50;
}
}
}
else
{
lean_dec_ref(x_64);
x_38 = x_51;
x_39 = x_54;
x_40 = lean_box(0);
goto block_43;
}
}
}
else
{
uint8_t x_96; 
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_96 = !lean_is_exclusive(x_62);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_97 = lean_ctor_get(x_62, 0);
x_98 = lean_io_error_to_string(x_97);
x_99 = 3;
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
x_101 = lean_apply_2(x_54, x_100, lean_box(0));
x_102 = lean_box(0);
lean_ctor_set(x_62, 0, x_102);
return x_62;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_62, 0);
lean_inc(x_103);
lean_dec(x_62);
x_104 = lean_io_error_to_string(x_103);
x_105 = 3;
x_106 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set_uint8(x_106, sizeof(void*)*1, x_105);
x_107 = lean_apply_2(x_54, x_106, lean_box(0));
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec_ref(x_53);
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_110 = !lean_is_exclusive(x_59);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_59, 0);
x_112 = lean_io_error_to_string(x_111);
x_113 = 3;
x_114 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*1, x_113);
x_115 = lean_apply_2(x_54, x_114, lean_box(0));
x_116 = lean_box(0);
lean_ctor_set(x_59, 0, x_116);
return x_59;
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_117 = lean_ctor_get(x_59, 0);
lean_inc(x_117);
lean_dec(x_59);
x_118 = lean_io_error_to_string(x_117);
x_119 = 3;
x_120 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*1, x_119);
x_121 = lean_apply_2(x_54, x_120, lean_box(0));
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
block_132:
{
lean_object* x_130; lean_object* x_131; 
x_130 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15;
lean_inc_ref(x_127);
x_131 = lean_apply_2(x_127, x_130, lean_box(0));
x_51 = x_125;
x_52 = x_126;
x_53 = x_128;
x_54 = x_127;
x_55 = lean_box(0);
goto block_124;
}
block_159:
{
lean_object* x_138; uint8_t x_139; 
x_138 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
x_139 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17;
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_unsigned_to_nat(0u);
x_141 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_2);
x_142 = l_Lake_GitRepo_checkoutBranch(x_138, x_2, x_141);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_array_get_size(x_143);
x_145 = lean_nat_dec_lt(x_140, x_144);
if (x_145 == 0)
{
lean_dec(x_143);
x_51 = x_133;
x_52 = x_134;
x_53 = x_136;
x_54 = x_135;
x_55 = lean_box(0);
goto block_124;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_le(x_144, x_144);
if (x_146 == 0)
{
lean_dec(x_143);
x_51 = x_133;
x_52 = x_134;
x_53 = x_136;
x_54 = x_135;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_object* x_147; size_t x_148; size_t x_149; lean_object* x_150; 
x_147 = lean_box(0);
x_148 = 0;
x_149 = lean_usize_of_nat(x_144);
lean_inc_ref(x_135);
x_150 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_143, x_148, x_149, x_147, x_135);
lean_dec(x_143);
lean_dec_ref(x_150);
x_51 = x_133;
x_52 = x_134;
x_53 = x_136;
x_54 = x_135;
x_55 = lean_box(0);
goto block_124;
}
}
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_151 = lean_ctor_get(x_142, 1);
lean_inc(x_151);
lean_dec_ref(x_142);
x_152 = lean_array_get_size(x_151);
x_153 = lean_nat_dec_lt(x_140, x_152);
if (x_153 == 0)
{
lean_dec(x_151);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
else
{
uint8_t x_154; 
x_154 = lean_nat_dec_le(x_152, x_152);
if (x_154 == 0)
{
lean_dec(x_151);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_155; size_t x_156; size_t x_157; lean_object* x_158; 
x_155 = lean_box(0);
x_156 = 0;
x_157 = lean_usize_of_nat(x_152);
lean_inc_ref(x_135);
x_158 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_151, x_156, x_157, x_155, x_135);
lean_dec(x_151);
lean_dec_ref(x_158);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
}
}
}
else
{
x_51 = x_133;
x_52 = x_134;
x_53 = x_136;
x_54 = x_135;
x_55 = lean_box(0);
goto block_124;
}
}
block_185:
{
if (x_164 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_unsigned_to_nat(0u);
x_167 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_2);
x_168 = l_Lake_GitRepo_quietInit(x_2, x_167);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = lean_array_get_size(x_169);
x_171 = lean_nat_dec_lt(x_166, x_170);
if (x_171 == 0)
{
lean_dec(x_169);
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_163;
x_137 = lean_box(0);
goto block_159;
}
else
{
uint8_t x_172; 
x_172 = lean_nat_dec_le(x_170, x_170);
if (x_172 == 0)
{
lean_dec(x_169);
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_163;
x_137 = lean_box(0);
goto block_159;
}
else
{
lean_object* x_173; size_t x_174; size_t x_175; lean_object* x_176; 
x_173 = lean_box(0);
x_174 = 0;
x_175 = lean_usize_of_nat(x_170);
lean_inc_ref(x_162);
x_176 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_169, x_174, x_175, x_173, x_162);
lean_dec(x_169);
lean_dec_ref(x_176);
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_163;
x_137 = lean_box(0);
goto block_159;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_177 = lean_ctor_get(x_168, 1);
lean_inc(x_177);
lean_dec_ref(x_168);
x_178 = lean_array_get_size(x_177);
x_179 = lean_nat_dec_lt(x_166, x_178);
if (x_179 == 0)
{
lean_dec(x_177);
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = x_163;
x_129 = lean_box(0);
goto block_132;
}
else
{
uint8_t x_180; 
x_180 = lean_nat_dec_le(x_178, x_178);
if (x_180 == 0)
{
lean_dec(x_177);
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = x_163;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_181; size_t x_182; size_t x_183; lean_object* x_184; 
x_181 = lean_box(0);
x_182 = 0;
x_183 = lean_usize_of_nat(x_178);
lean_inc_ref(x_162);
x_184 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_177, x_182, x_183, x_181, x_162);
lean_dec(x_177);
lean_dec_ref(x_184);
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = x_163;
x_129 = lean_box(0);
goto block_132;
}
}
}
}
else
{
x_51 = x_160;
x_52 = x_161;
x_53 = x_163;
x_54 = x_162;
x_55 = lean_box(0);
goto block_124;
}
}
block_199:
{
uint8_t x_191; lean_object* x_192; uint8_t x_193; 
lean_inc_ref(x_2);
x_191 = l_Lake_GitRepo_insideWorkTree(x_2);
x_192 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_193 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_193 == 0)
{
x_160 = x_186;
x_161 = x_187;
x_162 = x_189;
x_163 = x_188;
x_164 = x_191;
x_165 = lean_box(0);
goto block_185;
}
else
{
uint8_t x_194; 
x_194 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_194 == 0)
{
x_160 = x_186;
x_161 = x_187;
x_162 = x_189;
x_163 = x_188;
x_164 = x_191;
x_165 = lean_box(0);
goto block_185;
}
else
{
lean_object* x_195; size_t x_196; size_t x_197; lean_object* x_198; 
x_195 = lean_box(0);
x_196 = 0;
x_197 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_189);
x_198 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_192, x_196, x_197, x_195, x_189);
lean_dec_ref(x_198);
x_160 = x_186;
x_161 = x_187;
x_162 = x_189;
x_163 = x_188;
x_164 = x_191;
x_165 = lean_box(0);
goto block_185;
}
}
}
block_222:
{
lean_object* x_207; 
x_207 = l_IO_FS_writeFile(x_204, x_206);
lean_dec_ref(x_206);
lean_dec_ref(x_204);
if (lean_obj_tag(x_207) == 0)
{
lean_dec_ref(x_207);
x_186 = x_201;
x_187 = x_202;
x_188 = x_205;
x_189 = x_203;
x_190 = lean_box(0);
goto block_199;
}
else
{
uint8_t x_208; 
lean_dec_ref(x_205);
lean_dec_ref(x_202);
lean_dec(x_201);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_io_error_to_string(x_209);
x_211 = 3;
x_212 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*1, x_211);
x_213 = lean_apply_2(x_203, x_212, lean_box(0));
x_214 = lean_box(0);
lean_ctor_set(x_207, 0, x_214);
return x_207;
}
else
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_215 = lean_ctor_get(x_207, 0);
lean_inc(x_215);
lean_dec(x_207);
x_216 = lean_io_error_to_string(x_215);
x_217 = 3;
x_218 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set_uint8(x_218, sizeof(void*)*1, x_217);
x_219 = lean_apply_2(x_203, x_218, lean_box(0));
x_220 = lean_box(0);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
return x_221;
}
}
}
block_236:
{
if (x_228 == 0)
{
uint8_t x_230; uint8_t x_231; 
x_230 = 4;
x_231 = l_Lake_instDecidableEqInitTemplate(x_4, x_230);
if (x_231 == 0)
{
lean_object* x_232; lean_object* x_233; 
x_232 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_233 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_232);
lean_dec_ref(x_232);
x_200 = lean_box(0);
x_201 = x_223;
x_202 = x_224;
x_203 = x_226;
x_204 = x_225;
x_205 = x_227;
x_206 = x_233;
goto block_222;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_235 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_234);
lean_dec_ref(x_234);
x_200 = lean_box(0);
x_201 = x_223;
x_202 = x_224;
x_203 = x_226;
x_204 = x_225;
x_205 = x_227;
x_206 = x_235;
goto block_222;
}
}
else
{
lean_dec_ref(x_225);
lean_dec(x_3);
x_186 = x_223;
x_187 = x_224;
x_188 = x_227;
x_189 = x_226;
x_190 = lean_box(0);
goto block_199;
}
}
block_252:
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; uint8_t x_246; 
x_242 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18;
lean_inc_ref(x_2);
x_243 = l_Lake_joinRelative(x_2, x_242);
x_244 = l_System_FilePath_pathExists(x_243);
x_245 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_246 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_246 == 0)
{
x_223 = x_237;
x_224 = x_238;
x_225 = x_243;
x_226 = x_240;
x_227 = x_239;
x_228 = x_244;
x_229 = lean_box(0);
goto block_236;
}
else
{
uint8_t x_247; 
x_247 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_247 == 0)
{
x_223 = x_237;
x_224 = x_238;
x_225 = x_243;
x_226 = x_240;
x_227 = x_239;
x_228 = x_244;
x_229 = lean_box(0);
goto block_236;
}
else
{
lean_object* x_248; size_t x_249; size_t x_250; lean_object* x_251; 
x_248 = lean_box(0);
x_249 = 0;
x_250 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_240);
x_251 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_245, x_249, x_250, x_248, x_240);
lean_dec_ref(x_251);
x_223 = x_237;
x_224 = x_238;
x_225 = x_243;
x_226 = x_240;
x_227 = x_239;
x_228 = x_244;
x_229 = lean_box(0);
goto block_236;
}
}
}
block_295:
{
if (x_259 == 0)
{
uint8_t x_261; uint8_t x_262; 
x_261 = 1;
x_262 = l_Lake_instDecidableEqInitTemplate(x_4, x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_257);
x_264 = l_IO_FS_writeFile(x_253, x_263);
lean_dec_ref(x_263);
lean_dec_ref(x_253);
if (lean_obj_tag(x_264) == 0)
{
lean_dec_ref(x_264);
x_237 = x_254;
x_238 = x_255;
x_239 = x_256;
x_240 = x_258;
x_241 = lean_box(0);
goto block_252;
}
else
{
uint8_t x_265; 
lean_dec_ref(x_256);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_io_error_to_string(x_266);
x_268 = 3;
x_269 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set_uint8(x_269, sizeof(void*)*1, x_268);
x_270 = lean_apply_2(x_258, x_269, lean_box(0));
x_271 = lean_box(0);
lean_ctor_set(x_264, 0, x_271);
return x_264;
}
else
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = lean_ctor_get(x_264, 0);
lean_inc(x_272);
lean_dec(x_264);
x_273 = lean_io_error_to_string(x_272);
x_274 = 3;
x_275 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set_uint8(x_275, sizeof(void*)*1, x_274);
x_276 = lean_apply_2(x_258, x_275, lean_box(0));
x_277 = lean_box(0);
x_278 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_278, 0, x_277);
return x_278;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_257);
x_279 = l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
x_280 = l_IO_FS_writeFile(x_253, x_279);
lean_dec_ref(x_253);
if (lean_obj_tag(x_280) == 0)
{
lean_dec_ref(x_280);
x_237 = x_254;
x_238 = x_255;
x_239 = x_256;
x_240 = x_258;
x_241 = lean_box(0);
goto block_252;
}
else
{
uint8_t x_281; 
lean_dec_ref(x_256);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_281 = !lean_is_exclusive(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_282 = lean_ctor_get(x_280, 0);
x_283 = lean_io_error_to_string(x_282);
x_284 = 3;
x_285 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set_uint8(x_285, sizeof(void*)*1, x_284);
x_286 = lean_apply_2(x_258, x_285, lean_box(0));
x_287 = lean_box(0);
lean_ctor_set(x_280, 0, x_287);
return x_280;
}
else
{
lean_object* x_288; lean_object* x_289; uint8_t x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_288 = lean_ctor_get(x_280, 0);
lean_inc(x_288);
lean_dec(x_280);
x_289 = lean_io_error_to_string(x_288);
x_290 = 3;
x_291 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set_uint8(x_291, sizeof(void*)*1, x_290);
x_292 = lean_apply_2(x_258, x_291, lean_box(0));
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
}
else
{
lean_dec(x_257);
lean_dec_ref(x_253);
x_237 = x_254;
x_238 = x_255;
x_239 = x_256;
x_240 = x_258;
x_241 = lean_box(0);
goto block_252;
}
}
block_312:
{
lean_object* x_302; lean_object* x_303; uint8_t x_304; lean_object* x_305; uint8_t x_306; 
x_302 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_2);
x_303 = l_Lake_joinRelative(x_2, x_302);
x_304 = l_System_FilePath_pathExists(x_303);
x_305 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_306 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_306 == 0)
{
x_253 = x_303;
x_254 = x_296;
x_255 = x_297;
x_256 = x_298;
x_257 = x_299;
x_258 = x_301;
x_259 = x_304;
x_260 = lean_box(0);
goto block_295;
}
else
{
uint8_t x_307; 
x_307 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_307 == 0)
{
x_253 = x_303;
x_254 = x_296;
x_255 = x_297;
x_256 = x_298;
x_257 = x_299;
x_258 = x_301;
x_259 = x_304;
x_260 = lean_box(0);
goto block_295;
}
else
{
lean_object* x_308; size_t x_309; size_t x_310; lean_object* x_311; 
x_308 = lean_box(0);
x_309 = 0;
x_310 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_301);
x_311 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_305, x_309, x_310, x_308, x_301);
lean_dec_ref(x_311);
x_253 = x_303;
x_254 = x_296;
x_255 = x_297;
x_256 = x_298;
x_257 = x_299;
x_258 = x_301;
x_259 = x_304;
x_260 = lean_box(0);
goto block_295;
}
}
}
block_319:
{
switch (x_4) {
case 0:
{
x_296 = x_313;
x_297 = x_314;
x_298 = x_315;
x_299 = x_316;
x_300 = lean_box(0);
x_301 = x_317;
goto block_312;
}
case 1:
{
x_296 = x_313;
x_297 = x_314;
x_298 = x_315;
x_299 = x_316;
x_300 = lean_box(0);
x_301 = x_317;
goto block_312;
}
default: 
{
lean_dec(x_316);
x_237 = x_313;
x_238 = x_314;
x_239 = x_315;
x_240 = x_317;
x_241 = lean_box(0);
goto block_252;
}
}
}
block_343:
{
lean_object* x_328; 
x_328 = l_IO_FS_writeFile(x_324, x_327);
lean_dec_ref(x_327);
lean_dec_ref(x_324);
if (lean_obj_tag(x_328) == 0)
{
lean_dec_ref(x_328);
x_313 = x_321;
x_314 = x_322;
x_315 = x_325;
x_316 = x_326;
x_317 = x_323;
x_318 = lean_box(0);
goto block_319;
}
else
{
uint8_t x_329; 
lean_dec(x_326);
lean_dec_ref(x_325);
lean_dec_ref(x_322);
lean_dec(x_321);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_330 = lean_ctor_get(x_328, 0);
x_331 = lean_io_error_to_string(x_330);
x_332 = 3;
x_333 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set_uint8(x_333, sizeof(void*)*1, x_332);
x_334 = lean_apply_2(x_323, x_333, lean_box(0));
x_335 = lean_box(0);
lean_ctor_set(x_328, 0, x_335);
return x_328;
}
else
{
lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_336 = lean_ctor_get(x_328, 0);
lean_inc(x_336);
lean_dec(x_328);
x_337 = lean_io_error_to_string(x_336);
x_338 = 3;
x_339 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set_uint8(x_339, sizeof(void*)*1, x_338);
x_340 = lean_apply_2(x_323, x_339, lean_box(0));
x_341 = lean_box(0);
x_342 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_342, 0, x_341);
return x_342;
}
}
}
block_357:
{
uint8_t x_351; uint8_t x_352; 
x_351 = 4;
x_352 = l_Lake_instDecidableEqInitTemplate(x_4, x_351);
if (x_352 == 0)
{
uint8_t x_353; lean_object* x_354; lean_object* x_355; 
x_353 = 1;
lean_inc(x_348);
x_354 = l_Lean_Name_toString(x_348, x_353);
lean_inc(x_348);
x_355 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_354, x_348);
lean_dec_ref(x_354);
x_320 = lean_box(0);
x_321 = x_344;
x_322 = x_346;
x_323 = x_349;
x_324 = x_345;
x_325 = x_347;
x_326 = x_348;
x_327 = x_355;
goto block_343;
}
else
{
lean_object* x_356; 
lean_inc(x_348);
x_356 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_348);
x_320 = lean_box(0);
x_321 = x_344;
x_322 = x_346;
x_323 = x_349;
x_324 = x_345;
x_325 = x_347;
x_326 = x_348;
x_327 = x_356;
goto block_343;
}
}
block_398:
{
if (x_365 == 0)
{
lean_object* x_367; 
x_367 = l_IO_FS_createDirAll(x_358);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; lean_object* x_369; 
lean_dec_ref(x_367);
x_368 = l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
x_369 = l_IO_FS_writeFile(x_364, x_368);
lean_dec_ref(x_364);
if (lean_obj_tag(x_369) == 0)
{
lean_dec_ref(x_369);
x_344 = x_359;
x_345 = x_361;
x_346 = x_360;
x_347 = x_362;
x_348 = x_363;
x_349 = x_1;
x_350 = lean_box(0);
goto block_357;
}
else
{
uint8_t x_370; 
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec(x_359);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_370 = !lean_is_exclusive(x_369);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_371 = lean_ctor_get(x_369, 0);
x_372 = lean_io_error_to_string(x_371);
x_373 = 3;
x_374 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set_uint8(x_374, sizeof(void*)*1, x_373);
x_375 = lean_apply_2(x_1, x_374, lean_box(0));
x_376 = lean_box(0);
lean_ctor_set(x_369, 0, x_376);
return x_369;
}
else
{
lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_377 = lean_ctor_get(x_369, 0);
lean_inc(x_377);
lean_dec(x_369);
x_378 = lean_io_error_to_string(x_377);
x_379 = 3;
x_380 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set_uint8(x_380, sizeof(void*)*1, x_379);
x_381 = lean_apply_2(x_1, x_380, lean_box(0));
x_382 = lean_box(0);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
return x_383;
}
}
}
else
{
uint8_t x_384; 
lean_dec_ref(x_364);
lean_dec(x_363);
lean_dec_ref(x_362);
lean_dec_ref(x_361);
lean_dec_ref(x_360);
lean_dec(x_359);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_384 = !lean_is_exclusive(x_367);
if (x_384 == 0)
{
lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_385 = lean_ctor_get(x_367, 0);
x_386 = lean_io_error_to_string(x_385);
x_387 = 3;
x_388 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set_uint8(x_388, sizeof(void*)*1, x_387);
x_389 = lean_apply_2(x_1, x_388, lean_box(0));
x_390 = lean_box(0);
lean_ctor_set(x_367, 0, x_390);
return x_367;
}
else
{
lean_object* x_391; lean_object* x_392; uint8_t x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_391 = lean_ctor_get(x_367, 0);
lean_inc(x_391);
lean_dec(x_367);
x_392 = lean_io_error_to_string(x_391);
x_393 = 3;
x_394 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set_uint8(x_394, sizeof(void*)*1, x_393);
x_395 = lean_apply_2(x_1, x_394, lean_box(0));
x_396 = lean_box(0);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
return x_397;
}
}
}
else
{
lean_dec_ref(x_364);
lean_dec_ref(x_358);
x_344 = x_359;
x_345 = x_361;
x_346 = x_360;
x_347 = x_362;
x_348 = x_363;
x_349 = x_1;
x_350 = lean_box(0);
goto block_357;
}
}
block_437:
{
lean_object* x_408; lean_object* x_409; 
lean_inc(x_407);
lean_inc(x_406);
lean_inc(x_3);
x_408 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_4, x_5, x_3, x_406, x_407);
x_409 = l_IO_FS_writeFile(x_401, x_408);
lean_dec_ref(x_408);
lean_dec_ref(x_401);
if (lean_obj_tag(x_409) == 0)
{
lean_dec_ref(x_409);
if (lean_obj_tag(x_402) == 1)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; uint8_t x_415; lean_object* x_416; uint8_t x_417; 
x_410 = lean_ctor_get(x_402, 0);
lean_inc(x_410);
lean_dec_ref(x_402);
x_411 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
lean_inc(x_410);
x_412 = l_System_FilePath_withExtension(x_410, x_411);
x_413 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19;
lean_inc_ref(x_412);
x_414 = l_Lake_joinRelative(x_412, x_413);
x_415 = l_System_FilePath_pathExists(x_414);
x_416 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_417 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_417 == 0)
{
x_358 = x_412;
x_359 = x_407;
x_360 = x_403;
x_361 = x_410;
x_362 = x_404;
x_363 = x_406;
x_364 = x_414;
x_365 = x_415;
x_366 = lean_box(0);
goto block_398;
}
else
{
uint8_t x_418; 
x_418 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_418 == 0)
{
x_358 = x_412;
x_359 = x_407;
x_360 = x_403;
x_361 = x_410;
x_362 = x_404;
x_363 = x_406;
x_364 = x_414;
x_365 = x_415;
x_366 = lean_box(0);
goto block_398;
}
else
{
lean_object* x_419; size_t x_420; size_t x_421; lean_object* x_422; 
x_419 = lean_box(0);
x_420 = 0;
x_421 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_422 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_416, x_420, x_421, x_419, x_1);
lean_dec_ref(x_422);
x_358 = x_412;
x_359 = x_407;
x_360 = x_403;
x_361 = x_410;
x_362 = x_404;
x_363 = x_406;
x_364 = x_414;
x_365 = x_415;
x_366 = lean_box(0);
goto block_398;
}
}
}
else
{
lean_dec(x_402);
x_313 = x_407;
x_314 = x_403;
x_315 = x_404;
x_316 = x_406;
x_317 = x_1;
x_318 = lean_box(0);
goto block_319;
}
}
else
{
uint8_t x_423; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec_ref(x_404);
lean_dec_ref(x_403);
lean_dec(x_402);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_423 = !lean_is_exclusive(x_409);
if (x_423 == 0)
{
lean_object* x_424; lean_object* x_425; uint8_t x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_424 = lean_ctor_get(x_409, 0);
x_425 = lean_io_error_to_string(x_424);
x_426 = 3;
x_427 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set_uint8(x_427, sizeof(void*)*1, x_426);
x_428 = lean_apply_2(x_1, x_427, lean_box(0));
x_429 = lean_box(0);
lean_ctor_set(x_409, 0, x_429);
return x_409;
}
else
{
lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_430 = lean_ctor_get(x_409, 0);
lean_inc(x_430);
lean_dec(x_409);
x_431 = lean_io_error_to_string(x_430);
x_432 = 3;
x_433 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set_uint8(x_433, sizeof(void*)*1, x_432);
x_434 = lean_apply_2(x_1, x_433, lean_box(0));
x_435 = lean_box(0);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_435);
return x_436;
}
}
}
block_447:
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_6, 1);
x_442 = lean_ctor_get(x_6, 15);
lean_inc_ref(x_442);
x_443 = l_Lake_ToolchainVer_ofString(x_442);
if (lean_obj_tag(x_443) == 0)
{
lean_object* x_444; lean_object* x_445; 
x_444 = lean_ctor_get(x_443, 1);
lean_inc_ref(x_444);
lean_dec_ref(x_443);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_444);
lean_inc_ref(x_441);
lean_inc_ref(x_442);
x_402 = x_439;
x_403 = x_442;
x_404 = x_441;
x_405 = lean_box(0);
x_406 = x_438;
x_407 = x_445;
goto block_437;
}
else
{
lean_object* x_446; 
lean_dec_ref(x_443);
x_446 = lean_box(0);
lean_inc_ref(x_441);
lean_inc_ref(x_442);
x_402 = x_439;
x_403 = x_442;
x_404 = x_441;
x_405 = lean_box(0);
x_406 = x_438;
x_407 = x_446;
goto block_437;
}
}
block_454:
{
if (x_450 == 0)
{
lean_object* x_452; 
x_452 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_452, 0, x_449);
x_438 = x_448;
x_439 = x_452;
x_440 = lean_box(0);
goto block_447;
}
else
{
lean_object* x_453; 
lean_dec_ref(x_449);
x_453 = lean_box(0);
x_438 = x_448;
x_439 = x_453;
x_440 = lean_box(0);
goto block_447;
}
}
block_470:
{
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; uint8_t x_461; lean_object* x_462; uint8_t x_463; 
lean_dec_ref(x_456);
lean_inc(x_3);
x_459 = l_Lake_toUpperCamelCase(x_3);
lean_inc(x_459);
x_460 = l_Lean_modToFilePath(x_2, x_459, x_455);
lean_dec_ref(x_455);
x_461 = l_System_FilePath_pathExists(x_460);
x_462 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_463 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_463 == 0)
{
x_448 = x_459;
x_449 = x_460;
x_450 = x_461;
x_451 = lean_box(0);
goto block_454;
}
else
{
uint8_t x_464; 
x_464 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_464 == 0)
{
x_448 = x_459;
x_449 = x_460;
x_450 = x_461;
x_451 = lean_box(0);
goto block_454;
}
else
{
lean_object* x_465; size_t x_466; size_t x_467; lean_object* x_468; 
x_465 = lean_box(0);
x_466 = 0;
x_467 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_468 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_462, x_466, x_467, x_465, x_1);
lean_dec_ref(x_468);
x_448 = x_459;
x_449 = x_460;
x_450 = x_461;
x_451 = lean_box(0);
goto block_454;
}
}
}
else
{
lean_object* x_469; 
lean_dec_ref(x_455);
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_456);
lean_inc(x_3);
x_438 = x_3;
x_439 = x_469;
x_440 = lean_box(0);
goto block_447;
}
}
block_477:
{
uint8_t x_475; uint8_t x_476; 
x_475 = 1;
x_476 = l_Lake_instDecidableEqInitTemplate(x_4, x_475);
if (x_476 == 0)
{
x_455 = x_471;
x_456 = x_472;
x_457 = lean_box(0);
x_458 = x_473;
goto block_470;
}
else
{
x_455 = x_471;
x_456 = x_472;
x_457 = lean_box(0);
x_458 = x_476;
goto block_470;
}
}
block_489:
{
lean_object* x_479; lean_object* x_480; uint8_t x_481; lean_object* x_482; uint8_t x_483; 
x_479 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20;
lean_inc(x_3);
x_480 = l_Lean_modToFilePath(x_2, x_3, x_479);
x_481 = l_System_FilePath_pathExists(x_480);
x_482 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_483 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_483 == 0)
{
x_471 = x_479;
x_472 = x_480;
x_473 = x_481;
x_474 = lean_box(0);
goto block_477;
}
else
{
uint8_t x_484; 
x_484 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_484 == 0)
{
x_471 = x_479;
x_472 = x_480;
x_473 = x_481;
x_474 = lean_box(0);
goto block_477;
}
else
{
lean_object* x_485; size_t x_486; size_t x_487; lean_object* x_488; 
x_485 = lean_box(0);
x_486 = 0;
x_487 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_488 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_482, x_486, x_487, x_485, x_1);
lean_dec_ref(x_488);
x_471 = x_479;
x_472 = x_480;
x_473 = x_481;
x_474 = lean_box(0);
goto block_477;
}
}
}
block_517:
{
if (x_490 == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_unsigned_to_nat(0u);
x_493 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_2);
x_494 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_2, x_4, x_493);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; uint8_t x_497; 
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec_ref(x_494);
x_496 = lean_array_get_size(x_495);
x_497 = lean_nat_dec_lt(x_492, x_496);
if (x_497 == 0)
{
lean_dec(x_495);
x_478 = lean_box(0);
goto block_489;
}
else
{
uint8_t x_498; 
x_498 = lean_nat_dec_le(x_496, x_496);
if (x_498 == 0)
{
lean_dec(x_495);
x_478 = lean_box(0);
goto block_489;
}
else
{
lean_object* x_499; size_t x_500; size_t x_501; lean_object* x_502; 
x_499 = lean_box(0);
x_500 = 0;
x_501 = lean_usize_of_nat(x_496);
lean_inc_ref(x_1);
x_502 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_495, x_500, x_501, x_499, x_1);
lean_dec(x_495);
lean_dec_ref(x_502);
x_478 = lean_box(0);
goto block_489;
}
}
}
else
{
lean_object* x_503; lean_object* x_504; uint8_t x_505; 
lean_dec_ref(x_401);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_503 = lean_ctor_get(x_494, 1);
lean_inc(x_503);
lean_dec_ref(x_494);
x_504 = lean_array_get_size(x_503);
x_505 = lean_nat_dec_lt(x_492, x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; 
lean_dec(x_503);
lean_dec_ref(x_1);
x_506 = lean_box(0);
x_507 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_507, 0, x_506);
return x_507;
}
else
{
uint8_t x_508; 
x_508 = lean_nat_dec_le(x_504, x_504);
if (x_508 == 0)
{
lean_dec(x_503);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_509; size_t x_510; size_t x_511; lean_object* x_512; 
x_509 = lean_box(0);
x_510 = 0;
x_511 = lean_usize_of_nat(x_504);
x_512 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_503, x_510, x_511, x_509, x_1);
lean_dec(x_503);
lean_dec_ref(x_512);
x_9 = lean_box(0);
goto block_12;
}
}
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec_ref(x_401);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_513 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22;
x_514 = lean_apply_2(x_1, x_513, lean_box(0));
x_515 = lean_box(0);
x_516 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_516, 0, x_515);
return x_516;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_33; lean_object* x_34; lean_object* x_64; uint8_t x_65; 
x_64 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
x_65 = lean_string_dec_eq(x_1, x_64);
if (x_65 == 0)
{
x_33 = x_1;
x_34 = lean_box(0);
goto block_63;
}
else
{
lean_object* x_66; 
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_66 = lean_io_realpath(x_5);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = l_System_FilePath_fileName(x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_70 = l_Lake_init___closed__0;
x_71 = lean_string_append(x_70, x_68);
lean_dec(x_68);
x_72 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
x_73 = lean_string_append(x_71, x_72);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_apply_2(x_7, x_75, lean_box(0));
x_77 = lean_box(0);
lean_ctor_set_tag(x_66, 1);
lean_ctor_set(x_66, 0, x_77);
return x_66;
}
else
{
lean_object* x_78; 
lean_free_object(x_66);
lean_dec(x_68);
x_78 = lean_ctor_get(x_69, 0);
lean_inc(x_78);
lean_dec_ref(x_69);
x_33 = x_78;
x_34 = lean_box(0);
goto block_63;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_66, 0);
lean_inc(x_79);
lean_dec(x_66);
lean_inc(x_79);
x_80 = l_System_FilePath_fileName(x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_81 = l_Lake_init___closed__0;
x_82 = lean_string_append(x_81, x_79);
lean_dec(x_79);
x_83 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
x_84 = lean_string_append(x_82, x_83);
x_85 = 3;
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_85);
x_87 = lean_apply_2(x_7, x_86, lean_box(0));
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_79);
x_90 = lean_ctor_get(x_80, 0);
lean_inc(x_90);
lean_dec_ref(x_80);
x_33 = x_90;
x_34 = lean_box(0);
goto block_63;
}
}
}
else
{
uint8_t x_91; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_91 = !lean_is_exclusive(x_66);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_92 = lean_ctor_get(x_66, 0);
x_93 = lean_io_error_to_string(x_92);
x_94 = 3;
x_95 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*1, x_94);
x_96 = lean_apply_2(x_7, x_95, lean_box(0));
x_97 = lean_box(0);
lean_ctor_set(x_66, 0, x_97);
return x_66;
}
else
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_98 = lean_ctor_get(x_66, 0);
lean_inc(x_98);
lean_dec(x_66);
x_99 = lean_io_error_to_string(x_98);
x_100 = 3;
x_101 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_100);
x_102 = lean_apply_2(x_7, x_101, lean_box(0));
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_32:
{
lean_object* x_15; 
lean_inc_ref(x_5);
x_15 = l_IO_FS_createDirAll(x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_15);
x_16 = l_Lake_stringToLegalOrSimpleName(x_13);
x_17 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(x_7, x_5, x_16, x_2, x_3, x_4, x_6);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec_ref(x_13);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_io_error_to_string(x_19);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_apply_2(x_7, x_22, lean_box(0));
x_24 = lean_box(0);
lean_ctor_set(x_15, 0, x_24);
return x_15;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_15, 0);
lean_inc(x_25);
lean_dec(x_15);
x_26 = lean_io_error_to_string(x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_apply_2(x_7, x_28, lean_box(0));
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
block_63:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_string_utf8_byte_size(x_33);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_String_Slice_trimAscii(x_37);
lean_dec_ref(x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc_ref(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 2);
lean_inc(x_41);
lean_dec_ref(x_38);
x_42 = lean_string_utf8_extract(x_39, x_40, x_41);
lean_dec(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
x_43 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_42);
x_44 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_42, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_array_get_size(x_45);
x_47 = lean_nat_dec_lt(x_35, x_46);
if (x_47 == 0)
{
lean_dec(x_45);
x_13 = x_42;
x_14 = lean_box(0);
goto block_32;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
lean_dec(x_45);
x_13 = x_42;
x_14 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_49 = lean_box(0);
x_50 = 0;
x_51 = lean_usize_of_nat(x_46);
lean_inc_ref(x_7);
x_52 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_45, x_50, x_51, x_49, x_7);
lean_dec(x_45);
lean_dec_ref(x_52);
x_13 = x_42;
x_14 = lean_box(0);
goto block_32;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec_ref(x_42);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_dec_ref(x_44);
x_54 = lean_array_get_size(x_53);
x_55 = lean_nat_dec_lt(x_35, x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_dec_ref(x_7);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = lean_nat_dec_le(x_54, x_54);
if (x_58 == 0)
{
lean_dec(x_53);
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; 
x_59 = lean_box(0);
x_60 = 0;
x_61 = lean_usize_of_nat(x_54);
x_62 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_53, x_60, x_61, x_59, x_7);
lean_dec(x_53);
lean_dec_ref(x_62);
x_9 = lean_box(0);
goto block_12;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_6);
x_12 = l_Lake_init(x_1, x_9, x_10, x_4, x_5, x_11, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_4);
x_10 = lean_unbox(x_5);
x_11 = lean_unbox(x_7);
x_12 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(x_1, x_2, x_3, x_9, x_10, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lake_new(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_42; lean_object* x_43; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_string_utf8_byte_size(x_1);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_String_Slice_trimAscii(x_15);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = lean_string_utf8_extract(x_17, x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
x_42 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_20);
x_43 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_20, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_array_get_size(x_44);
x_46 = lean_nat_dec_lt(x_13, x_45);
if (x_46 == 0)
{
lean_dec(x_44);
x_21 = lean_box(0);
goto block_41;
}
else
{
uint8_t x_47; 
x_47 = lean_nat_dec_le(x_45, x_45);
if (x_47 == 0)
{
lean_dec(x_44);
x_21 = lean_box(0);
goto block_41;
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_48 = lean_box(0);
x_49 = 0;
x_50 = lean_usize_of_nat(x_45);
lean_inc_ref(x_7);
x_51 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_44, x_49, x_50, x_48, x_7);
lean_dec(x_44);
lean_dec_ref(x_51);
x_21 = lean_box(0);
goto block_41;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
lean_dec_ref(x_20);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec_ref(x_43);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_13, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
lean_dec_ref(x_7);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_53, x_53);
if (x_57 == 0)
{
lean_dec(x_52);
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; 
x_58 = lean_box(0);
x_59 = 0;
x_60 = lean_usize_of_nat(x_53);
x_61 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_52, x_59, x_60, x_58, x_7);
lean_dec(x_52);
lean_dec_ref(x_61);
x_9 = lean_box(0);
goto block_12;
}
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
block_41:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lake_stringToLegalOrSimpleName(x_20);
lean_inc(x_22);
x_23 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_22);
x_24 = l_Lake_joinRelative(x_5, x_23);
lean_inc_ref(x_24);
x_25 = l_IO_FS_createDirAll(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_25);
x_26 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__0(x_7, x_24, x_22, x_2, x_3, x_4, x_6);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec_ref(x_24);
lean_dec(x_22);
lean_dec_ref(x_4);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_25, 0);
x_29 = lean_io_error_to_string(x_28);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_30);
x_32 = lean_apply_2(x_7, x_31, lean_box(0));
x_33 = lean_box(0);
lean_ctor_set(x_25, 0, x_33);
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = lean_ctor_get(x_25, 0);
lean_inc(x_34);
lean_dec(x_25);
x_35 = lean_io_error_to_string(x_34);
x_36 = 3;
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_36);
x_38 = lean_apply_2(x_7, x_37, lean_box(0));
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_6);
x_12 = l_Lake_new(x_1, x_9, x_10, x_4, x_5, x_11, x_7);
return x_12;
}
}
lean_object* initialize_Lake_Config_Env(uint8_t builtin);
lean_object* initialize_Lake_Config_Lang(uint8_t builtin);
lean_object* initialize_Lake_Util_Git(uint8_t builtin);
lean_object* initialize_Lake_Util_Version(uint8_t builtin);
lean_object* initialize_Lake_Config_Package(uint8_t builtin);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Init(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Config_Env(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Lang(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Git(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_defaultExeRoot___closed__0 = _init_l_Lake_defaultExeRoot___closed__0();
lean_mark_persistent(l_Lake_defaultExeRoot___closed__0);
l_Lake_defaultExeRoot___closed__1 = _init_l_Lake_defaultExeRoot___closed__1();
lean_mark_persistent(l_Lake_defaultExeRoot___closed__1);
l_Lake_defaultExeRoot = _init_l_Lake_defaultExeRoot();
lean_mark_persistent(l_Lake_defaultExeRoot);
l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__1);
l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__2);
l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3 = _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3);
l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__4 = _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__4);
l___private_Lake_CLI_Init_0__Lake_gitignoreContents = _init_l___private_Lake_CLI_Init_0__Lake_gitignoreContents();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_gitignoreContents);
l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_basicFileContents = _init_l___private_Lake_CLI_Init_0__Lake_basicFileContents();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_basicFileContents);
l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__1);
l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2);
l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__0);
l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1);
l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2);
l___private_Lake_CLI_Init_0__Lake_mainFileName = _init_l___private_Lake_CLI_Init_0__Lake_mainFileName();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mainFileName);
l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_exeFileContents = _init_l___private_Lake_CLI_Init_0__Lake_exeFileContents();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_exeFileContents);
l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__1);
l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__2);
l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3 = _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3);
l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__4 = _init_l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__4);
l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__1);
l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2);
l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3 = _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3);
l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4 = _init_l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4);
l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_exeLeanConfigFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents___closed__1);
l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__1);
l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__2);
l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__1);
l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2);
l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathLeanConfigFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathTomlConfigFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents = _init_l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_leanActionWorkflowContents);
l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents = _init_l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents);
l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents = _init_l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_mathUpdateActionWorkflowContents);
l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents = _init_l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents);
l_Lake_instReprInitTemplate_repr___closed__0 = _init_l_Lake_instReprInitTemplate_repr___closed__0();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__0);
l_Lake_instReprInitTemplate_repr___closed__1 = _init_l_Lake_instReprInitTemplate_repr___closed__1();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__1);
l_Lake_instReprInitTemplate_repr___closed__2 = _init_l_Lake_instReprInitTemplate_repr___closed__2();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__2);
l_Lake_instReprInitTemplate_repr___closed__3 = _init_l_Lake_instReprInitTemplate_repr___closed__3();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__3);
l_Lake_instReprInitTemplate_repr___closed__4 = _init_l_Lake_instReprInitTemplate_repr___closed__4();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__4);
l_Lake_instReprInitTemplate_repr___closed__5 = _init_l_Lake_instReprInitTemplate_repr___closed__5();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__5);
l_Lake_instReprInitTemplate_repr___closed__6 = _init_l_Lake_instReprInitTemplate_repr___closed__6();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__6);
l_Lake_instReprInitTemplate_repr___closed__7 = _init_l_Lake_instReprInitTemplate_repr___closed__7();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__7);
l_Lake_instReprInitTemplate_repr___closed__8 = _init_l_Lake_instReprInitTemplate_repr___closed__8();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__8);
l_Lake_instReprInitTemplate_repr___closed__9 = _init_l_Lake_instReprInitTemplate_repr___closed__9();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__9);
l_Lake_instReprInitTemplate_repr___closed__10 = _init_l_Lake_instReprInitTemplate_repr___closed__10();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__10);
l_Lake_instReprInitTemplate_repr___closed__11 = _init_l_Lake_instReprInitTemplate_repr___closed__11();
lean_mark_persistent(l_Lake_instReprInitTemplate_repr___closed__11);
l_Lake_instReprInitTemplate___closed__0 = _init_l_Lake_instReprInitTemplate___closed__0();
lean_mark_persistent(l_Lake_instReprInitTemplate___closed__0);
l_Lake_instReprInitTemplate = _init_l_Lake_instReprInitTemplate();
lean_mark_persistent(l_Lake_instReprInitTemplate);
l_Lake_instInhabitedInitTemplate = _init_l_Lake_instInhabitedInitTemplate();
l_Lake_InitTemplate_ofString_x3f___closed__0 = _init_l_Lake_InitTemplate_ofString_x3f___closed__0();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__0);
l_Lake_InitTemplate_ofString_x3f___closed__1 = _init_l_Lake_InitTemplate_ofString_x3f___closed__1();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__1);
l_Lake_InitTemplate_ofString_x3f___closed__2 = _init_l_Lake_InitTemplate_ofString_x3f___closed__2();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__2);
l_Lake_InitTemplate_ofString_x3f___closed__3 = _init_l_Lake_InitTemplate_ofString_x3f___closed__3();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__3);
l_Lake_InitTemplate_ofString_x3f___closed__4 = _init_l_Lake_InitTemplate_ofString_x3f___closed__4();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__4);
l_Lake_InitTemplate_ofString_x3f___closed__5 = _init_l_Lake_InitTemplate_ofString_x3f___closed__5();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__5);
l_Lake_InitTemplate_ofString_x3f___closed__6 = _init_l_Lake_InitTemplate_ofString_x3f___closed__6();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__6);
l_Lake_InitTemplate_ofString_x3f___closed__7 = _init_l_Lake_InitTemplate_ofString_x3f___closed__7();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__7);
l_Lake_InitTemplate_ofString_x3f___closed__8 = _init_l_Lake_InitTemplate_ofString_x3f___closed__8();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__8);
l_Lake_InitTemplate_ofString_x3f___closed__9 = _init_l_Lake_InitTemplate_ofString_x3f___closed__9();
lean_mark_persistent(l_Lake_InitTemplate_ofString_x3f___closed__9);
l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__0();
l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1);
l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__2);
l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__3 = _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__3();
l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__4 = _init_l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__4);
l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0);
l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1);
l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2);
l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3 = _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__3);
l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4 = _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4);
l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5 = _init_l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5);
l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__0);
l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__0);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__1);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__2);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__3);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__4);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__5);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__7);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__8);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__9);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__11);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__13);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15);
l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16 = _init_l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__16);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__3);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__5);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11();
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12();
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13();
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__14);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17();
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__21 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__21();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__21);
l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22 = _init_l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22);
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__0);
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1___boxed__const__1);
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__1);
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2___boxed__const__1);
l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2 = _init_l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2();
lean_mark_persistent(l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0_spec__0___redArg___closed__2);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__2);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__3);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__4);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__7);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9);
l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10 = _init_l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10();
lean_mark_persistent(l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10);
l_Lake_init___closed__0 = _init_l_Lake_init___closed__0();
lean_mark_persistent(l_Lake_init___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
