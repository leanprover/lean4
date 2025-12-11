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
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg(x_5, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
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
lean_dec_ref(x_5);
return x_9;
}
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
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; lean_object* x_490; lean_object* x_502; uint8_t x_504; lean_object* x_505; lean_object* x_532; uint8_t x_533; 
x_13 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0;
x_411 = l_Lake_ConfigLang_fileExtension(x_4);
x_412 = l_System_FilePath_addExtension(x_13, x_411);
lean_dec_ref(x_411);
lean_inc_ref(x_1);
x_413 = l_Lake_joinRelative(x_1, x_412);
x_504 = l_System_FilePath_pathExists(x_413);
x_532 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_533 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_533 == 0)
{
x_505 = lean_box(0);
goto block_531;
}
else
{
uint8_t x_534; 
x_534 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_534 == 0)
{
x_505 = lean_box(0);
goto block_531;
}
else
{
lean_object* x_535; size_t x_536; size_t x_537; lean_object* x_538; 
x_535 = lean_box(0);
x_536 = 0;
x_537 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_538 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_532, x_536, x_537, x_535, x_7);
if (lean_obj_tag(x_538) == 0)
{
lean_dec_ref(x_538);
x_505 = lean_box(0);
goto block_531;
}
else
{
lean_dec_ref(x_413);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_538;
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
if (lean_obj_tag(x_95) == 0)
{
lean_dec_ref(x_95);
x_44 = x_52;
x_45 = x_54;
x_46 = x_88;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_dec_ref(x_54);
lean_dec(x_52);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_95;
}
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
block_138:
{
if (lean_obj_tag(x_137) == 0)
{
lean_dec_ref(x_137);
x_51 = x_133;
x_52 = x_134;
x_53 = x_135;
x_54 = x_136;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_dec_ref(x_137);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
}
block_165:
{
lean_object* x_144; uint8_t x_145; 
x_144 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
x_145 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17;
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_1);
x_148 = l_Lake_GitRepo_checkoutBranch(x_144, x_1, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_array_get_size(x_149);
x_151 = lean_nat_dec_lt(x_146, x_150);
if (x_151 == 0)
{
lean_dec(x_149);
x_51 = x_139;
x_52 = x_140;
x_53 = x_141;
x_54 = x_142;
x_55 = lean_box(0);
goto block_124;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_150, x_150);
if (x_152 == 0)
{
lean_dec(x_149);
x_51 = x_139;
x_52 = x_140;
x_53 = x_141;
x_54 = x_142;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_object* x_153; size_t x_154; size_t x_155; lean_object* x_156; 
x_153 = lean_box(0);
x_154 = 0;
x_155 = lean_usize_of_nat(x_150);
lean_inc_ref(x_142);
x_156 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_149, x_154, x_155, x_153, x_142);
lean_dec(x_149);
if (lean_obj_tag(x_156) == 0)
{
lean_dec_ref(x_156);
x_51 = x_139;
x_52 = x_140;
x_53 = x_141;
x_54 = x_142;
x_55 = lean_box(0);
goto block_124;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_156;
goto block_138;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_148, 1);
lean_inc(x_157);
lean_dec_ref(x_148);
x_158 = lean_array_get_size(x_157);
x_159 = lean_nat_dec_lt(x_146, x_158);
if (x_159 == 0)
{
lean_dec(x_157);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
uint8_t x_160; 
x_160 = lean_nat_dec_le(x_158, x_158);
if (x_160 == 0)
{
lean_dec(x_157);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; 
x_161 = lean_box(0);
x_162 = 0;
x_163 = lean_usize_of_nat(x_158);
lean_inc_ref(x_142);
x_164 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_157, x_162, x_163, x_161, x_142);
lean_dec(x_157);
if (lean_obj_tag(x_164) == 0)
{
lean_dec_ref(x_164);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_164;
goto block_138;
}
}
}
}
}
else
{
x_51 = x_139;
x_52 = x_140;
x_53 = x_141;
x_54 = x_142;
x_55 = lean_box(0);
goto block_124;
}
}
block_171:
{
if (lean_obj_tag(x_170) == 0)
{
lean_dec_ref(x_170);
x_139 = x_166;
x_140 = x_167;
x_141 = x_168;
x_142 = x_169;
x_143 = lean_box(0);
goto block_165;
}
else
{
lean_dec_ref(x_170);
x_125 = x_166;
x_126 = x_167;
x_127 = x_168;
x_128 = x_169;
x_129 = lean_box(0);
goto block_132;
}
}
block_197:
{
if (x_176 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_unsigned_to_nat(0u);
x_179 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_1);
x_180 = l_Lake_GitRepo_quietInit(x_1, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = lean_array_get_size(x_181);
x_183 = lean_nat_dec_lt(x_178, x_182);
if (x_183 == 0)
{
lean_dec(x_181);
x_139 = x_172;
x_140 = x_173;
x_141 = x_174;
x_142 = x_175;
x_143 = lean_box(0);
goto block_165;
}
else
{
uint8_t x_184; 
x_184 = lean_nat_dec_le(x_182, x_182);
if (x_184 == 0)
{
lean_dec(x_181);
x_139 = x_172;
x_140 = x_173;
x_141 = x_174;
x_142 = x_175;
x_143 = lean_box(0);
goto block_165;
}
else
{
lean_object* x_185; size_t x_186; size_t x_187; lean_object* x_188; 
x_185 = lean_box(0);
x_186 = 0;
x_187 = lean_usize_of_nat(x_182);
lean_inc_ref(x_175);
x_188 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_181, x_186, x_187, x_185, x_175);
lean_dec(x_181);
if (lean_obj_tag(x_188) == 0)
{
lean_dec_ref(x_188);
x_139 = x_172;
x_140 = x_173;
x_141 = x_174;
x_142 = x_175;
x_143 = lean_box(0);
goto block_165;
}
else
{
x_166 = x_172;
x_167 = x_173;
x_168 = x_174;
x_169 = x_175;
x_170 = x_188;
goto block_171;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_189 = lean_ctor_get(x_180, 1);
lean_inc(x_189);
lean_dec_ref(x_180);
x_190 = lean_array_get_size(x_189);
x_191 = lean_nat_dec_lt(x_178, x_190);
if (x_191 == 0)
{
lean_dec(x_189);
x_125 = x_172;
x_126 = x_173;
x_127 = x_174;
x_128 = x_175;
x_129 = lean_box(0);
goto block_132;
}
else
{
uint8_t x_192; 
x_192 = lean_nat_dec_le(x_190, x_190);
if (x_192 == 0)
{
lean_dec(x_189);
x_125 = x_172;
x_126 = x_173;
x_127 = x_174;
x_128 = x_175;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_193; size_t x_194; size_t x_195; lean_object* x_196; 
x_193 = lean_box(0);
x_194 = 0;
x_195 = lean_usize_of_nat(x_190);
lean_inc_ref(x_175);
x_196 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_189, x_194, x_195, x_193, x_175);
lean_dec(x_189);
if (lean_obj_tag(x_196) == 0)
{
lean_dec_ref(x_196);
x_125 = x_172;
x_126 = x_173;
x_127 = x_174;
x_128 = x_175;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_166 = x_172;
x_167 = x_173;
x_168 = x_174;
x_169 = x_175;
x_170 = x_196;
goto block_171;
}
}
}
}
}
else
{
x_51 = x_172;
x_52 = x_173;
x_53 = x_174;
x_54 = x_175;
x_55 = lean_box(0);
goto block_124;
}
}
block_211:
{
uint8_t x_203; lean_object* x_204; uint8_t x_205; 
lean_inc_ref(x_1);
x_203 = l_Lake_GitRepo_insideWorkTree(x_1);
x_204 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_205 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_205 == 0)
{
x_172 = x_198;
x_173 = x_199;
x_174 = x_200;
x_175 = x_201;
x_176 = x_203;
x_177 = lean_box(0);
goto block_197;
}
else
{
uint8_t x_206; 
x_206 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_206 == 0)
{
x_172 = x_198;
x_173 = x_199;
x_174 = x_200;
x_175 = x_201;
x_176 = x_203;
x_177 = lean_box(0);
goto block_197;
}
else
{
lean_object* x_207; size_t x_208; size_t x_209; lean_object* x_210; 
x_207 = lean_box(0);
x_208 = 0;
x_209 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_201);
x_210 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_204, x_208, x_209, x_207, x_201);
if (lean_obj_tag(x_210) == 0)
{
lean_dec_ref(x_210);
x_172 = x_198;
x_173 = x_199;
x_174 = x_200;
x_175 = x_201;
x_176 = x_203;
x_177 = lean_box(0);
goto block_197;
}
else
{
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec(x_199);
lean_dec_ref(x_198);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_210;
}
}
}
}
block_234:
{
lean_object* x_219; 
x_219 = l_IO_FS_writeFile(x_215, x_218);
lean_dec_ref(x_218);
lean_dec_ref(x_215);
if (lean_obj_tag(x_219) == 0)
{
lean_dec_ref(x_219);
x_198 = x_212;
x_199 = x_214;
x_200 = x_216;
x_201 = x_217;
x_202 = lean_box(0);
goto block_211;
}
else
{
uint8_t x_220; 
lean_dec_ref(x_216);
lean_dec(x_214);
lean_dec_ref(x_212);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_io_error_to_string(x_221);
x_223 = 3;
x_224 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set_uint8(x_224, sizeof(void*)*1, x_223);
x_225 = lean_apply_2(x_217, x_224, lean_box(0));
x_226 = lean_box(0);
lean_ctor_set(x_219, 0, x_226);
return x_219;
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_227 = lean_ctor_get(x_219, 0);
lean_inc(x_227);
lean_dec(x_219);
x_228 = lean_io_error_to_string(x_227);
x_229 = 3;
x_230 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_229);
x_231 = lean_apply_2(x_217, x_230, lean_box(0));
x_232 = lean_box(0);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
}
block_248:
{
if (x_240 == 0)
{
uint8_t x_242; uint8_t x_243; 
x_242 = 4;
x_243 = l_Lake_instDecidableEqInitTemplate(x_3, x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_245 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_244);
lean_dec_ref(x_244);
x_212 = x_235;
x_213 = lean_box(0);
x_214 = x_236;
x_215 = x_237;
x_216 = x_238;
x_217 = x_239;
x_218 = x_245;
goto block_234;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_247 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_246);
lean_dec_ref(x_246);
x_212 = x_235;
x_213 = lean_box(0);
x_214 = x_236;
x_215 = x_237;
x_216 = x_238;
x_217 = x_239;
x_218 = x_247;
goto block_234;
}
}
else
{
lean_dec_ref(x_237);
lean_dec(x_2);
x_198 = x_235;
x_199 = x_236;
x_200 = x_238;
x_201 = x_239;
x_202 = lean_box(0);
goto block_211;
}
}
block_264:
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_254 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18;
lean_inc_ref(x_1);
x_255 = l_Lake_joinRelative(x_1, x_254);
x_256 = l_System_FilePath_pathExists(x_255);
x_257 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_258 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_258 == 0)
{
x_235 = x_249;
x_236 = x_250;
x_237 = x_255;
x_238 = x_251;
x_239 = x_252;
x_240 = x_256;
x_241 = lean_box(0);
goto block_248;
}
else
{
uint8_t x_259; 
x_259 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_259 == 0)
{
x_235 = x_249;
x_236 = x_250;
x_237 = x_255;
x_238 = x_251;
x_239 = x_252;
x_240 = x_256;
x_241 = lean_box(0);
goto block_248;
}
else
{
lean_object* x_260; size_t x_261; size_t x_262; lean_object* x_263; 
x_260 = lean_box(0);
x_261 = 0;
x_262 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_252);
x_263 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_257, x_261, x_262, x_260, x_252);
if (lean_obj_tag(x_263) == 0)
{
lean_dec_ref(x_263);
x_235 = x_249;
x_236 = x_250;
x_237 = x_255;
x_238 = x_251;
x_239 = x_252;
x_240 = x_256;
x_241 = lean_box(0);
goto block_248;
}
else
{
lean_dec_ref(x_255);
lean_dec_ref(x_252);
lean_dec_ref(x_251);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_263;
}
}
}
}
block_307:
{
if (x_271 == 0)
{
uint8_t x_273; uint8_t x_274; 
x_273 = 1;
x_274 = l_Lake_instDecidableEqInitTemplate(x_3, x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_268);
x_276 = l_IO_FS_writeFile(x_265, x_275);
lean_dec_ref(x_275);
lean_dec_ref(x_265);
if (lean_obj_tag(x_276) == 0)
{
lean_dec_ref(x_276);
x_249 = x_266;
x_250 = x_267;
x_251 = x_270;
x_252 = x_269;
x_253 = lean_box(0);
goto block_264;
}
else
{
uint8_t x_277; 
lean_dec_ref(x_270);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_io_error_to_string(x_278);
x_280 = 3;
x_281 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set_uint8(x_281, sizeof(void*)*1, x_280);
x_282 = lean_apply_2(x_269, x_281, lean_box(0));
x_283 = lean_box(0);
lean_ctor_set(x_276, 0, x_283);
return x_276;
}
else
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_276, 0);
lean_inc(x_284);
lean_dec(x_276);
x_285 = lean_io_error_to_string(x_284);
x_286 = 3;
x_287 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set_uint8(x_287, sizeof(void*)*1, x_286);
x_288 = lean_apply_2(x_269, x_287, lean_box(0));
x_289 = lean_box(0);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
return x_290;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_268);
x_291 = l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
x_292 = l_IO_FS_writeFile(x_265, x_291);
lean_dec_ref(x_265);
if (lean_obj_tag(x_292) == 0)
{
lean_dec_ref(x_292);
x_249 = x_266;
x_250 = x_267;
x_251 = x_270;
x_252 = x_269;
x_253 = lean_box(0);
goto block_264;
}
else
{
uint8_t x_293; 
lean_dec_ref(x_270);
lean_dec(x_267);
lean_dec_ref(x_266);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_294 = lean_ctor_get(x_292, 0);
x_295 = lean_io_error_to_string(x_294);
x_296 = 3;
x_297 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set_uint8(x_297, sizeof(void*)*1, x_296);
x_298 = lean_apply_2(x_269, x_297, lean_box(0));
x_299 = lean_box(0);
lean_ctor_set(x_292, 0, x_299);
return x_292;
}
else
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_300 = lean_ctor_get(x_292, 0);
lean_inc(x_300);
lean_dec(x_292);
x_301 = lean_io_error_to_string(x_300);
x_302 = 3;
x_303 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*1, x_302);
x_304 = lean_apply_2(x_269, x_303, lean_box(0));
x_305 = lean_box(0);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_305);
return x_306;
}
}
}
}
else
{
lean_dec(x_268);
lean_dec_ref(x_265);
x_249 = x_266;
x_250 = x_267;
x_251 = x_270;
x_252 = x_269;
x_253 = lean_box(0);
goto block_264;
}
}
block_324:
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; uint8_t x_318; 
x_314 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_1);
x_315 = l_Lake_joinRelative(x_1, x_314);
x_316 = l_System_FilePath_pathExists(x_315);
x_317 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_318 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_318 == 0)
{
x_265 = x_315;
x_266 = x_308;
x_267 = x_309;
x_268 = x_310;
x_269 = x_311;
x_270 = x_312;
x_271 = x_316;
x_272 = lean_box(0);
goto block_307;
}
else
{
uint8_t x_319; 
x_319 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_319 == 0)
{
x_265 = x_315;
x_266 = x_308;
x_267 = x_309;
x_268 = x_310;
x_269 = x_311;
x_270 = x_312;
x_271 = x_316;
x_272 = lean_box(0);
goto block_307;
}
else
{
lean_object* x_320; size_t x_321; size_t x_322; lean_object* x_323; 
x_320 = lean_box(0);
x_321 = 0;
x_322 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_311);
x_323 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_317, x_321, x_322, x_320, x_311);
if (lean_obj_tag(x_323) == 0)
{
lean_dec_ref(x_323);
x_265 = x_315;
x_266 = x_308;
x_267 = x_309;
x_268 = x_310;
x_269 = x_311;
x_270 = x_312;
x_271 = x_316;
x_272 = lean_box(0);
goto block_307;
}
else
{
lean_dec_ref(x_315);
lean_dec_ref(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec(x_309);
lean_dec_ref(x_308);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_323;
}
}
}
}
block_331:
{
switch (x_3) {
case 0:
{
x_308 = x_325;
x_309 = x_326;
x_310 = x_327;
x_311 = x_329;
x_312 = x_328;
x_313 = lean_box(0);
goto block_324;
}
case 1:
{
x_308 = x_325;
x_309 = x_326;
x_310 = x_327;
x_311 = x_329;
x_312 = x_328;
x_313 = lean_box(0);
goto block_324;
}
default: 
{
lean_dec(x_327);
x_249 = x_325;
x_250 = x_326;
x_251 = x_328;
x_252 = x_329;
x_253 = lean_box(0);
goto block_264;
}
}
}
block_355:
{
lean_object* x_340; 
x_340 = l_IO_FS_writeFile(x_336, x_339);
lean_dec_ref(x_339);
lean_dec_ref(x_336);
if (lean_obj_tag(x_340) == 0)
{
lean_dec_ref(x_340);
x_325 = x_332;
x_326 = x_333;
x_327 = x_334;
x_328 = x_337;
x_329 = x_335;
x_330 = lean_box(0);
goto block_331;
}
else
{
uint8_t x_341; 
lean_dec_ref(x_337);
lean_dec(x_334);
lean_dec(x_333);
lean_dec_ref(x_332);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_341 = !lean_is_exclusive(x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_342 = lean_ctor_get(x_340, 0);
x_343 = lean_io_error_to_string(x_342);
x_344 = 3;
x_345 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*1, x_344);
x_346 = lean_apply_2(x_335, x_345, lean_box(0));
x_347 = lean_box(0);
lean_ctor_set(x_340, 0, x_347);
return x_340;
}
else
{
lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_348 = lean_ctor_get(x_340, 0);
lean_inc(x_348);
lean_dec(x_340);
x_349 = lean_io_error_to_string(x_348);
x_350 = 3;
x_351 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set_uint8(x_351, sizeof(void*)*1, x_350);
x_352 = lean_apply_2(x_335, x_351, lean_box(0));
x_353 = lean_box(0);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_353);
return x_354;
}
}
}
block_369:
{
uint8_t x_363; uint8_t x_364; 
x_363 = 4;
x_364 = l_Lake_instDecidableEqInitTemplate(x_3, x_363);
if (x_364 == 0)
{
uint8_t x_365; lean_object* x_366; lean_object* x_367; 
x_365 = 1;
lean_inc(x_358);
x_366 = l_Lean_Name_toString(x_358, x_365);
lean_inc(x_358);
x_367 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_366, x_358);
lean_dec_ref(x_366);
x_332 = x_356;
x_333 = x_357;
x_334 = x_358;
x_335 = x_361;
x_336 = x_359;
x_337 = x_360;
x_338 = lean_box(0);
x_339 = x_367;
goto block_355;
}
else
{
lean_object* x_368; 
lean_inc(x_358);
x_368 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_358);
x_332 = x_356;
x_333 = x_357;
x_334 = x_358;
x_335 = x_361;
x_336 = x_359;
x_337 = x_360;
x_338 = lean_box(0);
x_339 = x_368;
goto block_355;
}
}
block_410:
{
if (x_377 == 0)
{
lean_object* x_379; 
x_379 = l_IO_FS_createDirAll(x_372);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; 
lean_dec_ref(x_379);
x_380 = l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
x_381 = l_IO_FS_writeFile(x_371, x_380);
lean_dec_ref(x_371);
if (lean_obj_tag(x_381) == 0)
{
lean_dec_ref(x_381);
x_356 = x_370;
x_357 = x_373;
x_358 = x_374;
x_359 = x_375;
x_360 = x_376;
x_361 = x_7;
x_362 = lean_box(0);
goto block_369;
}
else
{
uint8_t x_382; 
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec(x_374);
lean_dec(x_373);
lean_dec_ref(x_370);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_383 = lean_ctor_get(x_381, 0);
x_384 = lean_io_error_to_string(x_383);
x_385 = 3;
x_386 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*1, x_385);
x_387 = lean_apply_2(x_7, x_386, lean_box(0));
x_388 = lean_box(0);
lean_ctor_set(x_381, 0, x_388);
return x_381;
}
else
{
lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_389 = lean_ctor_get(x_381, 0);
lean_inc(x_389);
lean_dec(x_381);
x_390 = lean_io_error_to_string(x_389);
x_391 = 3;
x_392 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set_uint8(x_392, sizeof(void*)*1, x_391);
x_393 = lean_apply_2(x_7, x_392, lean_box(0));
x_394 = lean_box(0);
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_394);
return x_395;
}
}
}
else
{
uint8_t x_396; 
lean_dec_ref(x_376);
lean_dec_ref(x_375);
lean_dec(x_374);
lean_dec(x_373);
lean_dec_ref(x_371);
lean_dec_ref(x_370);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_396 = !lean_is_exclusive(x_379);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_397 = lean_ctor_get(x_379, 0);
x_398 = lean_io_error_to_string(x_397);
x_399 = 3;
x_400 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*1, x_399);
x_401 = lean_apply_2(x_7, x_400, lean_box(0));
x_402 = lean_box(0);
lean_ctor_set(x_379, 0, x_402);
return x_379;
}
else
{
lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_403 = lean_ctor_get(x_379, 0);
lean_inc(x_403);
lean_dec(x_379);
x_404 = lean_io_error_to_string(x_403);
x_405 = 3;
x_406 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set_uint8(x_406, sizeof(void*)*1, x_405);
x_407 = lean_apply_2(x_7, x_406, lean_box(0));
x_408 = lean_box(0);
x_409 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_409, 0, x_408);
return x_409;
}
}
}
else
{
lean_dec_ref(x_372);
lean_dec_ref(x_371);
x_356 = x_370;
x_357 = x_373;
x_358 = x_374;
x_359 = x_375;
x_360 = x_376;
x_361 = x_7;
x_362 = lean_box(0);
goto block_369;
}
}
block_449:
{
lean_object* x_420; lean_object* x_421; 
lean_inc(x_419);
lean_inc(x_416);
lean_inc(x_2);
x_420 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_3, x_4, x_2, x_416, x_419);
x_421 = l_IO_FS_writeFile(x_413, x_420);
lean_dec_ref(x_420);
lean_dec_ref(x_413);
if (lean_obj_tag(x_421) == 0)
{
lean_dec_ref(x_421);
if (lean_obj_tag(x_415) == 1)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; 
x_422 = lean_ctor_get(x_415, 0);
lean_inc(x_422);
lean_dec_ref(x_415);
x_423 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
lean_inc(x_422);
x_424 = l_System_FilePath_withExtension(x_422, x_423);
x_425 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19;
lean_inc_ref(x_424);
x_426 = l_Lake_joinRelative(x_424, x_425);
x_427 = l_System_FilePath_pathExists(x_426);
x_428 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_429 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_429 == 0)
{
x_370 = x_414;
x_371 = x_426;
x_372 = x_424;
x_373 = x_419;
x_374 = x_416;
x_375 = x_422;
x_376 = x_418;
x_377 = x_427;
x_378 = lean_box(0);
goto block_410;
}
else
{
uint8_t x_430; 
x_430 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_430 == 0)
{
x_370 = x_414;
x_371 = x_426;
x_372 = x_424;
x_373 = x_419;
x_374 = x_416;
x_375 = x_422;
x_376 = x_418;
x_377 = x_427;
x_378 = lean_box(0);
goto block_410;
}
else
{
lean_object* x_431; size_t x_432; size_t x_433; lean_object* x_434; 
x_431 = lean_box(0);
x_432 = 0;
x_433 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_434 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_428, x_432, x_433, x_431, x_7);
if (lean_obj_tag(x_434) == 0)
{
lean_dec_ref(x_434);
x_370 = x_414;
x_371 = x_426;
x_372 = x_424;
x_373 = x_419;
x_374 = x_416;
x_375 = x_422;
x_376 = x_418;
x_377 = x_427;
x_378 = lean_box(0);
goto block_410;
}
else
{
lean_dec_ref(x_426);
lean_dec_ref(x_424);
lean_dec(x_422);
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_416);
lean_dec_ref(x_414);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_434;
}
}
}
}
else
{
lean_dec(x_415);
x_325 = x_414;
x_326 = x_419;
x_327 = x_416;
x_328 = x_418;
x_329 = x_7;
x_330 = lean_box(0);
goto block_331;
}
}
else
{
uint8_t x_435; 
lean_dec(x_419);
lean_dec_ref(x_418);
lean_dec(x_416);
lean_dec(x_415);
lean_dec_ref(x_414);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_435 = !lean_is_exclusive(x_421);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_436 = lean_ctor_get(x_421, 0);
x_437 = lean_io_error_to_string(x_436);
x_438 = 3;
x_439 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*1, x_438);
x_440 = lean_apply_2(x_7, x_439, lean_box(0));
x_441 = lean_box(0);
lean_ctor_set(x_421, 0, x_441);
return x_421;
}
else
{
lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_442 = lean_ctor_get(x_421, 0);
lean_inc(x_442);
lean_dec(x_421);
x_443 = lean_io_error_to_string(x_442);
x_444 = 3;
x_445 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*1, x_444);
x_446 = lean_apply_2(x_7, x_445, lean_box(0));
x_447 = lean_box(0);
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_447);
return x_448;
}
}
}
block_459:
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_5, 1);
x_454 = lean_ctor_get(x_5, 15);
lean_inc_ref(x_454);
x_455 = l_Lake_ToolchainVer_ofString(x_454);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_455, 1);
lean_inc_ref(x_456);
lean_dec_ref(x_455);
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_456);
lean_inc_ref(x_453);
lean_inc_ref(x_454);
x_414 = x_454;
x_415 = x_451;
x_416 = x_450;
x_417 = lean_box(0);
x_418 = x_453;
x_419 = x_457;
goto block_449;
}
else
{
lean_object* x_458; 
lean_dec_ref(x_455);
x_458 = lean_box(0);
lean_inc_ref(x_453);
lean_inc_ref(x_454);
x_414 = x_454;
x_415 = x_451;
x_416 = x_450;
x_417 = lean_box(0);
x_418 = x_453;
x_419 = x_458;
goto block_449;
}
}
block_466:
{
if (x_462 == 0)
{
lean_object* x_464; 
x_464 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_464, 0, x_461);
x_450 = x_460;
x_451 = x_464;
x_452 = lean_box(0);
goto block_459;
}
else
{
lean_object* x_465; 
lean_dec_ref(x_461);
x_465 = lean_box(0);
x_450 = x_460;
x_451 = x_465;
x_452 = lean_box(0);
goto block_459;
}
}
block_482:
{
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; uint8_t x_475; 
lean_dec_ref(x_468);
lean_inc(x_2);
x_471 = l_Lake_toUpperCamelCase(x_2);
lean_inc(x_471);
x_472 = l_Lean_modToFilePath(x_1, x_471, x_467);
lean_dec_ref(x_467);
x_473 = l_System_FilePath_pathExists(x_472);
x_474 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_475 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_475 == 0)
{
x_460 = x_471;
x_461 = x_472;
x_462 = x_473;
x_463 = lean_box(0);
goto block_466;
}
else
{
uint8_t x_476; 
x_476 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_476 == 0)
{
x_460 = x_471;
x_461 = x_472;
x_462 = x_473;
x_463 = lean_box(0);
goto block_466;
}
else
{
lean_object* x_477; size_t x_478; size_t x_479; lean_object* x_480; 
x_477 = lean_box(0);
x_478 = 0;
x_479 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_480 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_474, x_478, x_479, x_477, x_7);
if (lean_obj_tag(x_480) == 0)
{
lean_dec_ref(x_480);
x_460 = x_471;
x_461 = x_472;
x_462 = x_473;
x_463 = lean_box(0);
goto block_466;
}
else
{
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_413);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_480;
}
}
}
}
else
{
lean_object* x_481; 
lean_dec_ref(x_467);
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_468);
lean_inc(x_2);
x_450 = x_2;
x_451 = x_481;
x_452 = lean_box(0);
goto block_459;
}
}
block_489:
{
uint8_t x_487; uint8_t x_488; 
x_487 = 1;
x_488 = l_Lake_instDecidableEqInitTemplate(x_3, x_487);
if (x_488 == 0)
{
x_467 = x_483;
x_468 = x_484;
x_469 = lean_box(0);
x_470 = x_485;
goto block_482;
}
else
{
x_467 = x_483;
x_468 = x_484;
x_469 = lean_box(0);
x_470 = x_488;
goto block_482;
}
}
block_501:
{
lean_object* x_491; lean_object* x_492; uint8_t x_493; lean_object* x_494; uint8_t x_495; 
x_491 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20;
lean_inc(x_2);
x_492 = l_Lean_modToFilePath(x_1, x_2, x_491);
x_493 = l_System_FilePath_pathExists(x_492);
x_494 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_495 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_495 == 0)
{
x_483 = x_491;
x_484 = x_492;
x_485 = x_493;
x_486 = lean_box(0);
goto block_489;
}
else
{
uint8_t x_496; 
x_496 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_496 == 0)
{
x_483 = x_491;
x_484 = x_492;
x_485 = x_493;
x_486 = lean_box(0);
goto block_489;
}
else
{
lean_object* x_497; size_t x_498; size_t x_499; lean_object* x_500; 
x_497 = lean_box(0);
x_498 = 0;
x_499 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_500 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_494, x_498, x_499, x_497, x_7);
if (lean_obj_tag(x_500) == 0)
{
lean_dec_ref(x_500);
x_483 = x_491;
x_484 = x_492;
x_485 = x_493;
x_486 = lean_box(0);
goto block_489;
}
else
{
lean_dec_ref(x_492);
lean_dec_ref(x_413);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_500;
}
}
}
}
block_503:
{
if (lean_obj_tag(x_502) == 0)
{
lean_dec_ref(x_502);
x_490 = lean_box(0);
goto block_501;
}
else
{
lean_dec_ref(x_413);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_502;
}
}
block_531:
{
if (x_504 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_unsigned_to_nat(0u);
x_507 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_1);
x_508 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_1, x_3, x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; 
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
lean_dec_ref(x_508);
x_510 = lean_array_get_size(x_509);
x_511 = lean_nat_dec_lt(x_506, x_510);
if (x_511 == 0)
{
lean_dec(x_509);
x_490 = lean_box(0);
goto block_501;
}
else
{
uint8_t x_512; 
x_512 = lean_nat_dec_le(x_510, x_510);
if (x_512 == 0)
{
lean_dec(x_509);
x_490 = lean_box(0);
goto block_501;
}
else
{
lean_object* x_513; size_t x_514; size_t x_515; lean_object* x_516; 
x_513 = lean_box(0);
x_514 = 0;
x_515 = lean_usize_of_nat(x_510);
lean_inc_ref(x_7);
x_516 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_509, x_514, x_515, x_513, x_7);
lean_dec(x_509);
if (lean_obj_tag(x_516) == 0)
{
lean_dec_ref(x_516);
x_490 = lean_box(0);
goto block_501;
}
else
{
x_502 = x_516;
goto block_503;
}
}
}
}
else
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_517 = lean_ctor_get(x_508, 1);
lean_inc(x_517);
lean_dec_ref(x_508);
x_518 = lean_array_get_size(x_517);
x_519 = lean_nat_dec_lt(x_506, x_518);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_517);
lean_dec_ref(x_413);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_520 = lean_box(0);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
return x_521;
}
else
{
uint8_t x_522; 
x_522 = lean_nat_dec_le(x_518, x_518);
if (x_522 == 0)
{
lean_dec(x_517);
lean_dec_ref(x_413);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_523; size_t x_524; size_t x_525; lean_object* x_526; 
x_523 = lean_box(0);
x_524 = 0;
x_525 = lean_usize_of_nat(x_518);
lean_inc_ref(x_7);
x_526 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_517, x_524, x_525, x_523, x_7);
lean_dec(x_517);
if (lean_obj_tag(x_526) == 0)
{
lean_dec_ref(x_526);
lean_dec_ref(x_413);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_502 = x_526;
goto block_503;
}
}
}
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec_ref(x_413);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_527 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22;
x_528 = lean_apply_2(x_7, x_527, lean_box(0));
x_529 = lean_box(0);
x_530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_530, 0, x_529);
return x_530;
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
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; uint8_t x_377; lean_object* x_378; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; lean_object* x_490; lean_object* x_502; uint8_t x_504; lean_object* x_505; lean_object* x_532; uint8_t x_533; 
x_13 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0;
x_411 = l_Lake_ConfigLang_fileExtension(x_5);
x_412 = l_System_FilePath_addExtension(x_13, x_411);
lean_dec_ref(x_411);
lean_inc_ref(x_2);
x_413 = l_Lake_joinRelative(x_2, x_412);
x_504 = l_System_FilePath_pathExists(x_413);
x_532 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_533 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_533 == 0)
{
x_505 = lean_box(0);
goto block_531;
}
else
{
uint8_t x_534; 
x_534 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_534 == 0)
{
x_505 = lean_box(0);
goto block_531;
}
else
{
lean_object* x_535; size_t x_536; size_t x_537; lean_object* x_538; 
x_535 = lean_box(0);
x_536 = 0;
x_537 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_538 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_532, x_536, x_537, x_535, x_1);
if (lean_obj_tag(x_538) == 0)
{
lean_dec_ref(x_538);
x_505 = lean_box(0);
goto block_531;
}
else
{
lean_dec_ref(x_413);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_538;
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
if (lean_obj_tag(x_95) == 0)
{
lean_dec_ref(x_95);
x_44 = x_51;
x_45 = x_54;
x_46 = x_88;
x_47 = lean_box(0);
goto block_50;
}
else
{
lean_dec_ref(x_54);
lean_dec(x_51);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_95;
}
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
block_138:
{
if (lean_obj_tag(x_137) == 0)
{
lean_dec_ref(x_137);
x_51 = x_133;
x_52 = x_134;
x_53 = x_136;
x_54 = x_135;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_dec_ref(x_137);
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = x_136;
x_129 = lean_box(0);
goto block_132;
}
}
block_165:
{
lean_object* x_144; uint8_t x_145; 
x_144 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
x_145 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17;
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_2);
x_148 = l_Lake_GitRepo_checkoutBranch(x_144, x_2, x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_array_get_size(x_149);
x_151 = lean_nat_dec_lt(x_146, x_150);
if (x_151 == 0)
{
lean_dec(x_149);
x_51 = x_139;
x_52 = x_140;
x_53 = x_142;
x_54 = x_141;
x_55 = lean_box(0);
goto block_124;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_150, x_150);
if (x_152 == 0)
{
lean_dec(x_149);
x_51 = x_139;
x_52 = x_140;
x_53 = x_142;
x_54 = x_141;
x_55 = lean_box(0);
goto block_124;
}
else
{
lean_object* x_153; size_t x_154; size_t x_155; lean_object* x_156; 
x_153 = lean_box(0);
x_154 = 0;
x_155 = lean_usize_of_nat(x_150);
lean_inc_ref(x_141);
x_156 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_149, x_154, x_155, x_153, x_141);
lean_dec(x_149);
if (lean_obj_tag(x_156) == 0)
{
lean_dec_ref(x_156);
x_51 = x_139;
x_52 = x_140;
x_53 = x_142;
x_54 = x_141;
x_55 = lean_box(0);
goto block_124;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_156;
goto block_138;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_157 = lean_ctor_get(x_148, 1);
lean_inc(x_157);
lean_dec_ref(x_148);
x_158 = lean_array_get_size(x_157);
x_159 = lean_nat_dec_lt(x_146, x_158);
if (x_159 == 0)
{
lean_dec(x_157);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
uint8_t x_160; 
x_160 = lean_nat_dec_le(x_158, x_158);
if (x_160 == 0)
{
lean_dec(x_157);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_161; size_t x_162; size_t x_163; lean_object* x_164; 
x_161 = lean_box(0);
x_162 = 0;
x_163 = lean_usize_of_nat(x_158);
lean_inc_ref(x_141);
x_164 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_157, x_162, x_163, x_161, x_141);
lean_dec(x_157);
if (lean_obj_tag(x_164) == 0)
{
lean_dec_ref(x_164);
x_125 = x_139;
x_126 = x_140;
x_127 = x_141;
x_128 = x_142;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_133 = x_139;
x_134 = x_140;
x_135 = x_141;
x_136 = x_142;
x_137 = x_164;
goto block_138;
}
}
}
}
}
else
{
x_51 = x_139;
x_52 = x_140;
x_53 = x_142;
x_54 = x_141;
x_55 = lean_box(0);
goto block_124;
}
}
block_171:
{
if (lean_obj_tag(x_170) == 0)
{
lean_dec_ref(x_170);
x_139 = x_166;
x_140 = x_167;
x_141 = x_168;
x_142 = x_169;
x_143 = lean_box(0);
goto block_165;
}
else
{
lean_dec_ref(x_170);
x_125 = x_166;
x_126 = x_167;
x_127 = x_168;
x_128 = x_169;
x_129 = lean_box(0);
goto block_132;
}
}
block_197:
{
if (x_176 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_unsigned_to_nat(0u);
x_179 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_2);
x_180 = l_Lake_GitRepo_quietInit(x_2, x_179);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = lean_ctor_get(x_180, 1);
lean_inc(x_181);
lean_dec_ref(x_180);
x_182 = lean_array_get_size(x_181);
x_183 = lean_nat_dec_lt(x_178, x_182);
if (x_183 == 0)
{
lean_dec(x_181);
x_139 = x_172;
x_140 = x_173;
x_141 = x_174;
x_142 = x_175;
x_143 = lean_box(0);
goto block_165;
}
else
{
uint8_t x_184; 
x_184 = lean_nat_dec_le(x_182, x_182);
if (x_184 == 0)
{
lean_dec(x_181);
x_139 = x_172;
x_140 = x_173;
x_141 = x_174;
x_142 = x_175;
x_143 = lean_box(0);
goto block_165;
}
else
{
lean_object* x_185; size_t x_186; size_t x_187; lean_object* x_188; 
x_185 = lean_box(0);
x_186 = 0;
x_187 = lean_usize_of_nat(x_182);
lean_inc_ref(x_174);
x_188 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_181, x_186, x_187, x_185, x_174);
lean_dec(x_181);
if (lean_obj_tag(x_188) == 0)
{
lean_dec_ref(x_188);
x_139 = x_172;
x_140 = x_173;
x_141 = x_174;
x_142 = x_175;
x_143 = lean_box(0);
goto block_165;
}
else
{
x_166 = x_172;
x_167 = x_173;
x_168 = x_174;
x_169 = x_175;
x_170 = x_188;
goto block_171;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_189 = lean_ctor_get(x_180, 1);
lean_inc(x_189);
lean_dec_ref(x_180);
x_190 = lean_array_get_size(x_189);
x_191 = lean_nat_dec_lt(x_178, x_190);
if (x_191 == 0)
{
lean_dec(x_189);
x_125 = x_172;
x_126 = x_173;
x_127 = x_174;
x_128 = x_175;
x_129 = lean_box(0);
goto block_132;
}
else
{
uint8_t x_192; 
x_192 = lean_nat_dec_le(x_190, x_190);
if (x_192 == 0)
{
lean_dec(x_189);
x_125 = x_172;
x_126 = x_173;
x_127 = x_174;
x_128 = x_175;
x_129 = lean_box(0);
goto block_132;
}
else
{
lean_object* x_193; size_t x_194; size_t x_195; lean_object* x_196; 
x_193 = lean_box(0);
x_194 = 0;
x_195 = lean_usize_of_nat(x_190);
lean_inc_ref(x_174);
x_196 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_189, x_194, x_195, x_193, x_174);
lean_dec(x_189);
if (lean_obj_tag(x_196) == 0)
{
lean_dec_ref(x_196);
x_125 = x_172;
x_126 = x_173;
x_127 = x_174;
x_128 = x_175;
x_129 = lean_box(0);
goto block_132;
}
else
{
x_166 = x_172;
x_167 = x_173;
x_168 = x_174;
x_169 = x_175;
x_170 = x_196;
goto block_171;
}
}
}
}
}
else
{
x_51 = x_172;
x_52 = x_173;
x_53 = x_175;
x_54 = x_174;
x_55 = lean_box(0);
goto block_124;
}
}
block_211:
{
uint8_t x_203; lean_object* x_204; uint8_t x_205; 
lean_inc_ref(x_2);
x_203 = l_Lake_GitRepo_insideWorkTree(x_2);
x_204 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_205 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_205 == 0)
{
x_172 = x_198;
x_173 = x_199;
x_174 = x_201;
x_175 = x_200;
x_176 = x_203;
x_177 = lean_box(0);
goto block_197;
}
else
{
uint8_t x_206; 
x_206 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_206 == 0)
{
x_172 = x_198;
x_173 = x_199;
x_174 = x_201;
x_175 = x_200;
x_176 = x_203;
x_177 = lean_box(0);
goto block_197;
}
else
{
lean_object* x_207; size_t x_208; size_t x_209; lean_object* x_210; 
x_207 = lean_box(0);
x_208 = 0;
x_209 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_201);
x_210 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_204, x_208, x_209, x_207, x_201);
if (lean_obj_tag(x_210) == 0)
{
lean_dec_ref(x_210);
x_172 = x_198;
x_173 = x_199;
x_174 = x_201;
x_175 = x_200;
x_176 = x_203;
x_177 = lean_box(0);
goto block_197;
}
else
{
lean_dec_ref(x_201);
lean_dec_ref(x_200);
lean_dec_ref(x_199);
lean_dec(x_198);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_210;
}
}
}
}
block_234:
{
lean_object* x_219; 
x_219 = l_IO_FS_writeFile(x_216, x_218);
lean_dec_ref(x_218);
lean_dec_ref(x_216);
if (lean_obj_tag(x_219) == 0)
{
lean_dec_ref(x_219);
x_198 = x_213;
x_199 = x_214;
x_200 = x_217;
x_201 = x_215;
x_202 = lean_box(0);
goto block_211;
}
else
{
uint8_t x_220; 
lean_dec_ref(x_217);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_220 = !lean_is_exclusive(x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_221 = lean_ctor_get(x_219, 0);
x_222 = lean_io_error_to_string(x_221);
x_223 = 3;
x_224 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set_uint8(x_224, sizeof(void*)*1, x_223);
x_225 = lean_apply_2(x_215, x_224, lean_box(0));
x_226 = lean_box(0);
lean_ctor_set(x_219, 0, x_226);
return x_219;
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_227 = lean_ctor_get(x_219, 0);
lean_inc(x_227);
lean_dec(x_219);
x_228 = lean_io_error_to_string(x_227);
x_229 = 3;
x_230 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_229);
x_231 = lean_apply_2(x_215, x_230, lean_box(0));
x_232 = lean_box(0);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
return x_233;
}
}
}
block_248:
{
if (x_240 == 0)
{
uint8_t x_242; uint8_t x_243; 
x_242 = 4;
x_243 = l_Lake_instDecidableEqInitTemplate(x_4, x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_245 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_244);
lean_dec_ref(x_244);
x_212 = lean_box(0);
x_213 = x_235;
x_214 = x_236;
x_215 = x_238;
x_216 = x_237;
x_217 = x_239;
x_218 = x_245;
goto block_234;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_247 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_246);
lean_dec_ref(x_246);
x_212 = lean_box(0);
x_213 = x_235;
x_214 = x_236;
x_215 = x_238;
x_216 = x_237;
x_217 = x_239;
x_218 = x_247;
goto block_234;
}
}
else
{
lean_dec_ref(x_237);
lean_dec(x_3);
x_198 = x_235;
x_199 = x_236;
x_200 = x_239;
x_201 = x_238;
x_202 = lean_box(0);
goto block_211;
}
}
block_264:
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; lean_object* x_257; uint8_t x_258; 
x_254 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18;
lean_inc_ref(x_2);
x_255 = l_Lake_joinRelative(x_2, x_254);
x_256 = l_System_FilePath_pathExists(x_255);
x_257 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_258 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_258 == 0)
{
x_235 = x_249;
x_236 = x_250;
x_237 = x_255;
x_238 = x_252;
x_239 = x_251;
x_240 = x_256;
x_241 = lean_box(0);
goto block_248;
}
else
{
uint8_t x_259; 
x_259 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_259 == 0)
{
x_235 = x_249;
x_236 = x_250;
x_237 = x_255;
x_238 = x_252;
x_239 = x_251;
x_240 = x_256;
x_241 = lean_box(0);
goto block_248;
}
else
{
lean_object* x_260; size_t x_261; size_t x_262; lean_object* x_263; 
x_260 = lean_box(0);
x_261 = 0;
x_262 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_252);
x_263 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_257, x_261, x_262, x_260, x_252);
if (lean_obj_tag(x_263) == 0)
{
lean_dec_ref(x_263);
x_235 = x_249;
x_236 = x_250;
x_237 = x_255;
x_238 = x_252;
x_239 = x_251;
x_240 = x_256;
x_241 = lean_box(0);
goto block_248;
}
else
{
lean_dec_ref(x_255);
lean_dec_ref(x_252);
lean_dec_ref(x_251);
lean_dec_ref(x_250);
lean_dec(x_249);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_263;
}
}
}
}
block_307:
{
if (x_271 == 0)
{
uint8_t x_273; uint8_t x_274; 
x_273 = 1;
x_274 = l_Lake_instDecidableEqInitTemplate(x_4, x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_269);
x_276 = l_IO_FS_writeFile(x_265, x_275);
lean_dec_ref(x_275);
lean_dec_ref(x_265);
if (lean_obj_tag(x_276) == 0)
{
lean_dec_ref(x_276);
x_249 = x_266;
x_250 = x_267;
x_251 = x_268;
x_252 = x_270;
x_253 = lean_box(0);
goto block_264;
}
else
{
uint8_t x_277; 
lean_dec_ref(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_276, 0);
x_279 = lean_io_error_to_string(x_278);
x_280 = 3;
x_281 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set_uint8(x_281, sizeof(void*)*1, x_280);
x_282 = lean_apply_2(x_270, x_281, lean_box(0));
x_283 = lean_box(0);
lean_ctor_set(x_276, 0, x_283);
return x_276;
}
else
{
lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_276, 0);
lean_inc(x_284);
lean_dec(x_276);
x_285 = lean_io_error_to_string(x_284);
x_286 = 3;
x_287 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set_uint8(x_287, sizeof(void*)*1, x_286);
x_288 = lean_apply_2(x_270, x_287, lean_box(0));
x_289 = lean_box(0);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
return x_290;
}
}
}
else
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_269);
x_291 = l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
x_292 = l_IO_FS_writeFile(x_265, x_291);
lean_dec_ref(x_265);
if (lean_obj_tag(x_292) == 0)
{
lean_dec_ref(x_292);
x_249 = x_266;
x_250 = x_267;
x_251 = x_268;
x_252 = x_270;
x_253 = lean_box(0);
goto block_264;
}
else
{
uint8_t x_293; 
lean_dec_ref(x_268);
lean_dec_ref(x_267);
lean_dec(x_266);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_293 = !lean_is_exclusive(x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_294 = lean_ctor_get(x_292, 0);
x_295 = lean_io_error_to_string(x_294);
x_296 = 3;
x_297 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_297, 0, x_295);
lean_ctor_set_uint8(x_297, sizeof(void*)*1, x_296);
x_298 = lean_apply_2(x_270, x_297, lean_box(0));
x_299 = lean_box(0);
lean_ctor_set(x_292, 0, x_299);
return x_292;
}
else
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_300 = lean_ctor_get(x_292, 0);
lean_inc(x_300);
lean_dec(x_292);
x_301 = lean_io_error_to_string(x_300);
x_302 = 3;
x_303 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*1, x_302);
x_304 = lean_apply_2(x_270, x_303, lean_box(0));
x_305 = lean_box(0);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_305);
return x_306;
}
}
}
}
else
{
lean_dec(x_269);
lean_dec_ref(x_265);
x_249 = x_266;
x_250 = x_267;
x_251 = x_268;
x_252 = x_270;
x_253 = lean_box(0);
goto block_264;
}
}
block_324:
{
lean_object* x_314; lean_object* x_315; uint8_t x_316; lean_object* x_317; uint8_t x_318; 
x_314 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_2);
x_315 = l_Lake_joinRelative(x_2, x_314);
x_316 = l_System_FilePath_pathExists(x_315);
x_317 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_318 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_318 == 0)
{
x_265 = x_315;
x_266 = x_308;
x_267 = x_309;
x_268 = x_310;
x_269 = x_311;
x_270 = x_313;
x_271 = x_316;
x_272 = lean_box(0);
goto block_307;
}
else
{
uint8_t x_319; 
x_319 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_319 == 0)
{
x_265 = x_315;
x_266 = x_308;
x_267 = x_309;
x_268 = x_310;
x_269 = x_311;
x_270 = x_313;
x_271 = x_316;
x_272 = lean_box(0);
goto block_307;
}
else
{
lean_object* x_320; size_t x_321; size_t x_322; lean_object* x_323; 
x_320 = lean_box(0);
x_321 = 0;
x_322 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_313);
x_323 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_317, x_321, x_322, x_320, x_313);
if (lean_obj_tag(x_323) == 0)
{
lean_dec_ref(x_323);
x_265 = x_315;
x_266 = x_308;
x_267 = x_309;
x_268 = x_310;
x_269 = x_311;
x_270 = x_313;
x_271 = x_316;
x_272 = lean_box(0);
goto block_307;
}
else
{
lean_dec_ref(x_315);
lean_dec_ref(x_313);
lean_dec(x_311);
lean_dec_ref(x_310);
lean_dec_ref(x_309);
lean_dec(x_308);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_323;
}
}
}
}
block_331:
{
switch (x_4) {
case 0:
{
x_308 = x_325;
x_309 = x_326;
x_310 = x_327;
x_311 = x_328;
x_312 = lean_box(0);
x_313 = x_329;
goto block_324;
}
case 1:
{
x_308 = x_325;
x_309 = x_326;
x_310 = x_327;
x_311 = x_328;
x_312 = lean_box(0);
x_313 = x_329;
goto block_324;
}
default: 
{
lean_dec(x_328);
x_249 = x_325;
x_250 = x_326;
x_251 = x_327;
x_252 = x_329;
x_253 = lean_box(0);
goto block_264;
}
}
}
block_355:
{
lean_object* x_340; 
x_340 = l_IO_FS_writeFile(x_336, x_339);
lean_dec_ref(x_339);
lean_dec_ref(x_336);
if (lean_obj_tag(x_340) == 0)
{
lean_dec_ref(x_340);
x_325 = x_333;
x_326 = x_334;
x_327 = x_337;
x_328 = x_338;
x_329 = x_335;
x_330 = lean_box(0);
goto block_331;
}
else
{
uint8_t x_341; 
lean_dec(x_338);
lean_dec_ref(x_337);
lean_dec_ref(x_334);
lean_dec(x_333);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_341 = !lean_is_exclusive(x_340);
if (x_341 == 0)
{
lean_object* x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_342 = lean_ctor_get(x_340, 0);
x_343 = lean_io_error_to_string(x_342);
x_344 = 3;
x_345 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*1, x_344);
x_346 = lean_apply_2(x_335, x_345, lean_box(0));
x_347 = lean_box(0);
lean_ctor_set(x_340, 0, x_347);
return x_340;
}
else
{
lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_348 = lean_ctor_get(x_340, 0);
lean_inc(x_348);
lean_dec(x_340);
x_349 = lean_io_error_to_string(x_348);
x_350 = 3;
x_351 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set_uint8(x_351, sizeof(void*)*1, x_350);
x_352 = lean_apply_2(x_335, x_351, lean_box(0));
x_353 = lean_box(0);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_353);
return x_354;
}
}
}
block_369:
{
uint8_t x_363; uint8_t x_364; 
x_363 = 4;
x_364 = l_Lake_instDecidableEqInitTemplate(x_4, x_363);
if (x_364 == 0)
{
uint8_t x_365; lean_object* x_366; lean_object* x_367; 
x_365 = 1;
lean_inc(x_360);
x_366 = l_Lean_Name_toString(x_360, x_365);
lean_inc(x_360);
x_367 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_366, x_360);
lean_dec_ref(x_366);
x_332 = lean_box(0);
x_333 = x_356;
x_334 = x_358;
x_335 = x_361;
x_336 = x_357;
x_337 = x_359;
x_338 = x_360;
x_339 = x_367;
goto block_355;
}
else
{
lean_object* x_368; 
lean_inc(x_360);
x_368 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_360);
x_332 = lean_box(0);
x_333 = x_356;
x_334 = x_358;
x_335 = x_361;
x_336 = x_357;
x_337 = x_359;
x_338 = x_360;
x_339 = x_368;
goto block_355;
}
}
block_410:
{
if (x_377 == 0)
{
lean_object* x_379; 
x_379 = l_IO_FS_createDirAll(x_370);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; 
lean_dec_ref(x_379);
x_380 = l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
x_381 = l_IO_FS_writeFile(x_376, x_380);
lean_dec_ref(x_376);
if (lean_obj_tag(x_381) == 0)
{
lean_dec_ref(x_381);
x_356 = x_371;
x_357 = x_373;
x_358 = x_372;
x_359 = x_374;
x_360 = x_375;
x_361 = x_1;
x_362 = lean_box(0);
goto block_369;
}
else
{
uint8_t x_382; 
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec_ref(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; uint8_t x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_383 = lean_ctor_get(x_381, 0);
x_384 = lean_io_error_to_string(x_383);
x_385 = 3;
x_386 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set_uint8(x_386, sizeof(void*)*1, x_385);
x_387 = lean_apply_2(x_1, x_386, lean_box(0));
x_388 = lean_box(0);
lean_ctor_set(x_381, 0, x_388);
return x_381;
}
else
{
lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_389 = lean_ctor_get(x_381, 0);
lean_inc(x_389);
lean_dec(x_381);
x_390 = lean_io_error_to_string(x_389);
x_391 = 3;
x_392 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set_uint8(x_392, sizeof(void*)*1, x_391);
x_393 = lean_apply_2(x_1, x_392, lean_box(0));
x_394 = lean_box(0);
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_394);
return x_395;
}
}
}
else
{
uint8_t x_396; 
lean_dec_ref(x_376);
lean_dec(x_375);
lean_dec_ref(x_374);
lean_dec_ref(x_373);
lean_dec_ref(x_372);
lean_dec(x_371);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_396 = !lean_is_exclusive(x_379);
if (x_396 == 0)
{
lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_397 = lean_ctor_get(x_379, 0);
x_398 = lean_io_error_to_string(x_397);
x_399 = 3;
x_400 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set_uint8(x_400, sizeof(void*)*1, x_399);
x_401 = lean_apply_2(x_1, x_400, lean_box(0));
x_402 = lean_box(0);
lean_ctor_set(x_379, 0, x_402);
return x_379;
}
else
{
lean_object* x_403; lean_object* x_404; uint8_t x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_403 = lean_ctor_get(x_379, 0);
lean_inc(x_403);
lean_dec(x_379);
x_404 = lean_io_error_to_string(x_403);
x_405 = 3;
x_406 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set_uint8(x_406, sizeof(void*)*1, x_405);
x_407 = lean_apply_2(x_1, x_406, lean_box(0));
x_408 = lean_box(0);
x_409 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_409, 0, x_408);
return x_409;
}
}
}
else
{
lean_dec_ref(x_376);
lean_dec_ref(x_370);
x_356 = x_371;
x_357 = x_373;
x_358 = x_372;
x_359 = x_374;
x_360 = x_375;
x_361 = x_1;
x_362 = lean_box(0);
goto block_369;
}
}
block_449:
{
lean_object* x_420; lean_object* x_421; 
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_3);
x_420 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_4, x_5, x_3, x_418, x_419);
x_421 = l_IO_FS_writeFile(x_413, x_420);
lean_dec_ref(x_420);
lean_dec_ref(x_413);
if (lean_obj_tag(x_421) == 0)
{
lean_dec_ref(x_421);
if (lean_obj_tag(x_414) == 1)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; uint8_t x_429; 
x_422 = lean_ctor_get(x_414, 0);
lean_inc(x_422);
lean_dec_ref(x_414);
x_423 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
lean_inc(x_422);
x_424 = l_System_FilePath_withExtension(x_422, x_423);
x_425 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19;
lean_inc_ref(x_424);
x_426 = l_Lake_joinRelative(x_424, x_425);
x_427 = l_System_FilePath_pathExists(x_426);
x_428 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_429 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_429 == 0)
{
x_370 = x_424;
x_371 = x_419;
x_372 = x_415;
x_373 = x_422;
x_374 = x_416;
x_375 = x_418;
x_376 = x_426;
x_377 = x_427;
x_378 = lean_box(0);
goto block_410;
}
else
{
uint8_t x_430; 
x_430 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_430 == 0)
{
x_370 = x_424;
x_371 = x_419;
x_372 = x_415;
x_373 = x_422;
x_374 = x_416;
x_375 = x_418;
x_376 = x_426;
x_377 = x_427;
x_378 = lean_box(0);
goto block_410;
}
else
{
lean_object* x_431; size_t x_432; size_t x_433; lean_object* x_434; 
x_431 = lean_box(0);
x_432 = 0;
x_433 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_434 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_428, x_432, x_433, x_431, x_1);
if (lean_obj_tag(x_434) == 0)
{
lean_dec_ref(x_434);
x_370 = x_424;
x_371 = x_419;
x_372 = x_415;
x_373 = x_422;
x_374 = x_416;
x_375 = x_418;
x_376 = x_426;
x_377 = x_427;
x_378 = lean_box(0);
goto block_410;
}
else
{
lean_dec_ref(x_426);
lean_dec_ref(x_424);
lean_dec(x_422);
lean_dec(x_419);
lean_dec(x_418);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_434;
}
}
}
}
else
{
lean_dec(x_414);
x_325 = x_419;
x_326 = x_415;
x_327 = x_416;
x_328 = x_418;
x_329 = x_1;
x_330 = lean_box(0);
goto block_331;
}
}
else
{
uint8_t x_435; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec_ref(x_416);
lean_dec_ref(x_415);
lean_dec(x_414);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_435 = !lean_is_exclusive(x_421);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_436 = lean_ctor_get(x_421, 0);
x_437 = lean_io_error_to_string(x_436);
x_438 = 3;
x_439 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_439, 0, x_437);
lean_ctor_set_uint8(x_439, sizeof(void*)*1, x_438);
x_440 = lean_apply_2(x_1, x_439, lean_box(0));
x_441 = lean_box(0);
lean_ctor_set(x_421, 0, x_441);
return x_421;
}
else
{
lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
x_442 = lean_ctor_get(x_421, 0);
lean_inc(x_442);
lean_dec(x_421);
x_443 = lean_io_error_to_string(x_442);
x_444 = 3;
x_445 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_445, 0, x_443);
lean_ctor_set_uint8(x_445, sizeof(void*)*1, x_444);
x_446 = lean_apply_2(x_1, x_445, lean_box(0));
x_447 = lean_box(0);
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_447);
return x_448;
}
}
}
block_459:
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_6, 1);
x_454 = lean_ctor_get(x_6, 15);
lean_inc_ref(x_454);
x_455 = l_Lake_ToolchainVer_ofString(x_454);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_455, 1);
lean_inc_ref(x_456);
lean_dec_ref(x_455);
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_456);
lean_inc_ref(x_453);
lean_inc_ref(x_454);
x_414 = x_451;
x_415 = x_454;
x_416 = x_453;
x_417 = lean_box(0);
x_418 = x_450;
x_419 = x_457;
goto block_449;
}
else
{
lean_object* x_458; 
lean_dec_ref(x_455);
x_458 = lean_box(0);
lean_inc_ref(x_453);
lean_inc_ref(x_454);
x_414 = x_451;
x_415 = x_454;
x_416 = x_453;
x_417 = lean_box(0);
x_418 = x_450;
x_419 = x_458;
goto block_449;
}
}
block_466:
{
if (x_462 == 0)
{
lean_object* x_464; 
x_464 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_464, 0, x_461);
x_450 = x_460;
x_451 = x_464;
x_452 = lean_box(0);
goto block_459;
}
else
{
lean_object* x_465; 
lean_dec_ref(x_461);
x_465 = lean_box(0);
x_450 = x_460;
x_451 = x_465;
x_452 = lean_box(0);
goto block_459;
}
}
block_482:
{
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; uint8_t x_473; lean_object* x_474; uint8_t x_475; 
lean_dec_ref(x_468);
lean_inc(x_3);
x_471 = l_Lake_toUpperCamelCase(x_3);
lean_inc(x_471);
x_472 = l_Lean_modToFilePath(x_2, x_471, x_467);
lean_dec_ref(x_467);
x_473 = l_System_FilePath_pathExists(x_472);
x_474 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_475 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_475 == 0)
{
x_460 = x_471;
x_461 = x_472;
x_462 = x_473;
x_463 = lean_box(0);
goto block_466;
}
else
{
uint8_t x_476; 
x_476 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_476 == 0)
{
x_460 = x_471;
x_461 = x_472;
x_462 = x_473;
x_463 = lean_box(0);
goto block_466;
}
else
{
lean_object* x_477; size_t x_478; size_t x_479; lean_object* x_480; 
x_477 = lean_box(0);
x_478 = 0;
x_479 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_480 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_474, x_478, x_479, x_477, x_1);
if (lean_obj_tag(x_480) == 0)
{
lean_dec_ref(x_480);
x_460 = x_471;
x_461 = x_472;
x_462 = x_473;
x_463 = lean_box(0);
goto block_466;
}
else
{
lean_dec_ref(x_472);
lean_dec(x_471);
lean_dec_ref(x_413);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_480;
}
}
}
}
else
{
lean_object* x_481; 
lean_dec_ref(x_467);
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_468);
lean_inc(x_3);
x_450 = x_3;
x_451 = x_481;
x_452 = lean_box(0);
goto block_459;
}
}
block_489:
{
uint8_t x_487; uint8_t x_488; 
x_487 = 1;
x_488 = l_Lake_instDecidableEqInitTemplate(x_4, x_487);
if (x_488 == 0)
{
x_467 = x_483;
x_468 = x_484;
x_469 = lean_box(0);
x_470 = x_485;
goto block_482;
}
else
{
x_467 = x_483;
x_468 = x_484;
x_469 = lean_box(0);
x_470 = x_488;
goto block_482;
}
}
block_501:
{
lean_object* x_491; lean_object* x_492; uint8_t x_493; lean_object* x_494; uint8_t x_495; 
x_491 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20;
lean_inc(x_3);
x_492 = l_Lean_modToFilePath(x_2, x_3, x_491);
x_493 = l_System_FilePath_pathExists(x_492);
x_494 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_495 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_495 == 0)
{
x_483 = x_491;
x_484 = x_492;
x_485 = x_493;
x_486 = lean_box(0);
goto block_489;
}
else
{
uint8_t x_496; 
x_496 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_496 == 0)
{
x_483 = x_491;
x_484 = x_492;
x_485 = x_493;
x_486 = lean_box(0);
goto block_489;
}
else
{
lean_object* x_497; size_t x_498; size_t x_499; lean_object* x_500; 
x_497 = lean_box(0);
x_498 = 0;
x_499 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_500 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_494, x_498, x_499, x_497, x_1);
if (lean_obj_tag(x_500) == 0)
{
lean_dec_ref(x_500);
x_483 = x_491;
x_484 = x_492;
x_485 = x_493;
x_486 = lean_box(0);
goto block_489;
}
else
{
lean_dec_ref(x_492);
lean_dec_ref(x_413);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_500;
}
}
}
}
block_503:
{
if (lean_obj_tag(x_502) == 0)
{
lean_dec_ref(x_502);
x_490 = lean_box(0);
goto block_501;
}
else
{
lean_dec_ref(x_413);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_502;
}
}
block_531:
{
if (x_504 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_unsigned_to_nat(0u);
x_507 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_2);
x_508 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_2, x_4, x_507);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; 
x_509 = lean_ctor_get(x_508, 1);
lean_inc(x_509);
lean_dec_ref(x_508);
x_510 = lean_array_get_size(x_509);
x_511 = lean_nat_dec_lt(x_506, x_510);
if (x_511 == 0)
{
lean_dec(x_509);
x_490 = lean_box(0);
goto block_501;
}
else
{
uint8_t x_512; 
x_512 = lean_nat_dec_le(x_510, x_510);
if (x_512 == 0)
{
lean_dec(x_509);
x_490 = lean_box(0);
goto block_501;
}
else
{
lean_object* x_513; size_t x_514; size_t x_515; lean_object* x_516; 
x_513 = lean_box(0);
x_514 = 0;
x_515 = lean_usize_of_nat(x_510);
lean_inc_ref(x_1);
x_516 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_509, x_514, x_515, x_513, x_1);
lean_dec(x_509);
if (lean_obj_tag(x_516) == 0)
{
lean_dec_ref(x_516);
x_490 = lean_box(0);
goto block_501;
}
else
{
x_502 = x_516;
goto block_503;
}
}
}
}
else
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_517 = lean_ctor_get(x_508, 1);
lean_inc(x_517);
lean_dec_ref(x_508);
x_518 = lean_array_get_size(x_517);
x_519 = lean_nat_dec_lt(x_506, x_518);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; 
lean_dec(x_517);
lean_dec_ref(x_413);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_520 = lean_box(0);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
return x_521;
}
else
{
uint8_t x_522; 
x_522 = lean_nat_dec_le(x_518, x_518);
if (x_522 == 0)
{
lean_dec(x_517);
lean_dec_ref(x_413);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_523; size_t x_524; size_t x_525; lean_object* x_526; 
x_523 = lean_box(0);
x_524 = 0;
x_525 = lean_usize_of_nat(x_518);
lean_inc_ref(x_1);
x_526 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_517, x_524, x_525, x_523, x_1);
lean_dec(x_517);
if (lean_obj_tag(x_526) == 0)
{
lean_dec_ref(x_526);
lean_dec_ref(x_413);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_502 = x_526;
goto block_503;
}
}
}
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec_ref(x_413);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_527 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22;
x_528 = lean_apply_2(x_1, x_527, lean_box(0));
x_529 = lean_box(0);
x_530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_530, 0, x_529);
return x_530;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_init(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_33; lean_object* x_34; lean_object* x_36; lean_object* x_37; lean_object* x_67; uint8_t x_68; 
x_67 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
x_68 = lean_string_dec_eq(x_1, x_67);
if (x_68 == 0)
{
x_36 = x_1;
x_37 = lean_box(0);
goto block_66;
}
else
{
lean_object* x_69; 
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_69 = lean_io_realpath(x_5);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = l_System_FilePath_fileName(x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_73 = l_Lake_init___closed__0;
x_74 = lean_string_append(x_73, x_71);
lean_dec(x_71);
x_75 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
x_76 = lean_string_append(x_74, x_75);
x_77 = 3;
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
x_79 = lean_apply_2(x_7, x_78, lean_box(0));
x_80 = lean_box(0);
lean_ctor_set_tag(x_69, 1);
lean_ctor_set(x_69, 0, x_80);
return x_69;
}
else
{
lean_object* x_81; 
lean_free_object(x_69);
lean_dec(x_71);
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
lean_dec_ref(x_72);
x_36 = x_81;
x_37 = lean_box(0);
goto block_66;
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_69, 0);
lean_inc(x_82);
lean_dec(x_69);
lean_inc(x_82);
x_83 = l_System_FilePath_fileName(x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_84 = l_Lake_init___closed__0;
x_85 = lean_string_append(x_84, x_82);
lean_dec(x_82);
x_86 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
x_87 = lean_string_append(x_85, x_86);
x_88 = 3;
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_88);
x_90 = lean_apply_2(x_7, x_89, lean_box(0));
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
else
{
lean_object* x_93; 
lean_dec(x_82);
x_93 = lean_ctor_get(x_83, 0);
lean_inc(x_93);
lean_dec_ref(x_83);
x_36 = x_93;
x_37 = lean_box(0);
goto block_66;
}
}
}
else
{
uint8_t x_94; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_94 = !lean_is_exclusive(x_69);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_69, 0);
x_96 = lean_io_error_to_string(x_95);
x_97 = 3;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_apply_2(x_7, x_98, lean_box(0));
x_100 = lean_box(0);
lean_ctor_set(x_69, 0, x_100);
return x_69;
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_69, 0);
lean_inc(x_101);
lean_dec(x_69);
x_102 = lean_io_error_to_string(x_101);
x_103 = 3;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_apply_2(x_7, x_104, lean_box(0));
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
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
block_35:
{
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_34);
x_13 = x_33;
x_14 = lean_box(0);
goto block_32;
}
else
{
lean_dec_ref(x_33);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_34;
}
}
block_66:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_string_utf8_byte_size(x_36);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = l_String_Slice_trimAscii(x_40);
lean_dec_ref(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 2);
lean_inc(x_44);
lean_dec_ref(x_41);
x_45 = lean_string_utf8_extract(x_42, x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
lean_dec_ref(x_42);
x_46 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_45);
x_47 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_45, x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = lean_array_get_size(x_48);
x_50 = lean_nat_dec_lt(x_38, x_49);
if (x_50 == 0)
{
lean_dec(x_48);
x_13 = x_45;
x_14 = lean_box(0);
goto block_32;
}
else
{
uint8_t x_51; 
x_51 = lean_nat_dec_le(x_49, x_49);
if (x_51 == 0)
{
lean_dec(x_48);
x_13 = x_45;
x_14 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; 
x_52 = lean_box(0);
x_53 = 0;
x_54 = lean_usize_of_nat(x_49);
lean_inc_ref(x_7);
x_55 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_48, x_53, x_54, x_52, x_7);
lean_dec(x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_dec_ref(x_55);
x_13 = x_45;
x_14 = lean_box(0);
goto block_32;
}
else
{
x_33 = x_45;
x_34 = x_55;
goto block_35;
}
}
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_ctor_get(x_47, 1);
lean_inc(x_56);
lean_dec_ref(x_47);
x_57 = lean_array_get_size(x_56);
x_58 = lean_nat_dec_lt(x_38, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
lean_dec(x_56);
lean_dec_ref(x_45);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_57, x_57);
if (x_61 == 0)
{
lean_dec(x_56);
lean_dec_ref(x_45);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_62; size_t x_63; size_t x_64; lean_object* x_65; 
x_62 = lean_box(0);
x_63 = 0;
x_64 = lean_usize_of_nat(x_57);
lean_inc_ref(x_7);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_56, x_63, x_64, x_62, x_7);
lean_dec(x_56);
if (lean_obj_tag(x_65) == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_45);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_33 = x_45;
x_34 = x_65;
goto block_35;
}
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
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_42; lean_object* x_44; lean_object* x_45; 
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
x_44 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_20);
x_45 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_20, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_array_get_size(x_46);
x_48 = lean_nat_dec_lt(x_13, x_47);
if (x_48 == 0)
{
lean_dec(x_46);
x_21 = lean_box(0);
goto block_41;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_47, x_47);
if (x_49 == 0)
{
lean_dec(x_46);
x_21 = lean_box(0);
goto block_41;
}
else
{
lean_object* x_50; size_t x_51; size_t x_52; lean_object* x_53; 
x_50 = lean_box(0);
x_51 = 0;
x_52 = lean_usize_of_nat(x_47);
lean_inc_ref(x_7);
x_53 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_46, x_51, x_52, x_50, x_7);
lean_dec(x_46);
if (lean_obj_tag(x_53) == 0)
{
lean_dec_ref(x_53);
x_21 = lean_box(0);
goto block_41;
}
else
{
x_42 = x_53;
goto block_43;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_45, 1);
lean_inc(x_54);
lean_dec_ref(x_45);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_13, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_54);
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_55, x_55);
if (x_59 == 0)
{
lean_dec(x_54);
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; 
x_60 = lean_box(0);
x_61 = 0;
x_62 = lean_usize_of_nat(x_55);
lean_inc_ref(x_7);
x_63 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_54, x_61, x_62, x_60, x_7);
lean_dec(x_54);
if (lean_obj_tag(x_63) == 0)
{
lean_dec_ref(x_63);
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_9 = lean_box(0);
goto block_12;
}
else
{
x_42 = x_63;
goto block_43;
}
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
block_43:
{
if (lean_obj_tag(x_42) == 0)
{
lean_dec_ref(x_42);
x_21 = lean_box(0);
goto block_41;
}
else
{
lean_dec_ref(x_20);
lean_dec_ref(x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_42;
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
