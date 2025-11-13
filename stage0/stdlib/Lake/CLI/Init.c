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
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___00Lake_init_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxLeanConfigFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorIdx___boxed(lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object*);
lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprInitTemplate___closed__0;
extern lean_object* l_Lake_toolchainFileName;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents;
static lean_object* l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2;
static lean_object* l_Lake_defaultExeRoot___closed__1;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libLeanConfigFileContents(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__3;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__10;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__12;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___boxed(lean_object*);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__4;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___lam__0___boxed(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___boxed(lean_object*, lean_object*);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___lam__0(lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathLaxTomlConfigFileContents___closed__2;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__8;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__0;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__3;
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdTomlConfigFileContents___closed__2;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_toLower(uint32_t);
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
static lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___00Lake_init_spec__0(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_libRootFileContents___closed__2;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object*);
lean_object* l_System_FilePath_fileName(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__2(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__10;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__2;
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileContents___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_readmeFileContents(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___00Lake_init_spec__1(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__4;
static lean_object* l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2___boxed__const__1;
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
static uint8_t l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint32_t l_Lean_idEndEscape;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__4;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__2;
extern lean_object* l_Lean_NameSet_empty;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_stdLeanConfigFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1___boxed__const__1;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__14;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_instReprInitTemplate_repr___closed__7;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__6;
static lean_object* l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__15;
static lean_object* l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__9;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_dotlessName_spec__0(lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_libTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__5;
LEAN_EXPORT lean_object* l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_exeTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mainFileName___closed__2;
static lean_object* l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1;
static lean_object* l_Lake_instReprInitTemplate_repr___closed__3;
static lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19;
LEAN_EXPORT lean_object* l_Lake_init(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___00Lake_init_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__0;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT uint8_t l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_defaultExeRoot___closed__0;
lean_object* l_Char_utf8Size(uint32_t);
static lean_object* l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__0;
lean_object* l_Lake_GitRepo_quietInit(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg___boxed(lean_object*);
static lean_object* l___private_Lake_CLI_Init_0__Lake_mathBuildActionWorkflowContents___closed__0;
static lean_object* l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_dotlessName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_createReleaseActionWorkflowContents;
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_basicFileContents;
LEAN_EXPORT lean_object* l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_std_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_exe_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_lib_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_mathLax_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_math_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = l_Lake_InitTemplate_ctorIdx(x_1);
x_4 = l_Lake_InitTemplate_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_alloc_closure((void*)(l_Lake_InitTemplate_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_InitTemplate_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_InitTemplate_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_Lake_InitTemplate_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
x_6 = lean_unbox(x_3);
x_7 = l_Lake_InitTemplate_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
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
lean_dec(x_9);
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
lean_dec(x_3);
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
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_477; uint8_t x_489; lean_object* x_490; lean_object* x_517; uint8_t x_518; 
x_13 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0;
x_398 = l_Lake_ConfigLang_fileExtension(x_4);
x_399 = l_System_FilePath_addExtension(x_13, x_398);
lean_dec_ref(x_398);
lean_inc_ref(x_1);
x_400 = l_Lake_joinRelative(x_1, x_399);
x_489 = l_System_FilePath_pathExists(x_400);
x_517 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_518 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_518 == 0)
{
x_490 = lean_box(0);
goto block_516;
}
else
{
uint8_t x_519; 
x_519 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_519 == 0)
{
x_490 = lean_box(0);
goto block_516;
}
else
{
lean_object* x_520; size_t x_521; size_t x_522; lean_object* x_523; 
x_520 = lean_box(0);
x_521 = 0;
x_522 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_523 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_517, x_521, x_522, x_520, x_7);
lean_dec_ref(x_523);
x_490 = lean_box(0);
goto block_516;
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
block_30:
{
if (x_6 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
lean_inc_ref(x_1);
x_19 = l_Lake_joinRelative(x_1, x_18);
lean_inc_ref(x_19);
x_20 = l_Lake_joinRelative(x_19, x_13);
x_21 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1;
x_22 = lean_box(1);
x_23 = lean_box(0);
x_24 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
x_25 = lean_alloc_ctor(0, 13, 3);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_1);
lean_ctor_set(x_25, 3, x_17);
lean_ctor_set(x_25, 4, x_18);
lean_ctor_set(x_25, 5, x_19);
lean_ctor_set(x_25, 6, x_13);
lean_ctor_set(x_25, 7, x_20);
lean_ctor_set(x_25, 8, x_21);
lean_ctor_set(x_25, 9, x_22);
lean_ctor_set(x_25, 10, x_23);
lean_ctor_set(x_25, 11, x_24);
lean_ctor_set(x_25, 12, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*13, x_6);
lean_ctor_set_uint8(x_25, sizeof(void*)*13 + 1, x_6);
lean_ctor_set_uint8(x_25, sizeof(void*)*13 + 2, x_6);
x_26 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2;
x_27 = l_Lake_updateManifest(x_25, x_26, x_14);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_14);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
block_36:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4;
lean_inc_ref(x_33);
x_35 = lean_apply_2(x_33, x_34, lean_box(0));
x_14 = x_33;
x_15 = lean_box(0);
goto block_30;
}
else
{
lean_dec_ref(x_32);
x_14 = x_33;
x_15 = lean_box(0);
goto block_30;
}
}
block_42:
{
switch (x_3) {
case 3:
{
x_31 = lean_box(0);
x_32 = x_37;
x_33 = x_38;
goto block_36;
}
case 4:
{
x_31 = lean_box(0);
x_32 = x_37;
x_33 = x_38;
goto block_36;
}
default: 
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
block_49:
{
if (x_45 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
lean_inc_ref(x_43);
x_48 = lean_apply_2(x_43, x_47, lean_box(0));
x_37 = x_44;
x_38 = x_43;
x_39 = lean_box(0);
goto block_42;
}
else
{
x_37 = x_44;
x_38 = x_43;
x_39 = lean_box(0);
goto block_42;
}
}
block_123:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_55 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7;
lean_inc_ref(x_1);
x_56 = l_Lake_joinRelative(x_1, x_55);
x_57 = 4;
x_58 = lean_io_prim_handle_mk(x_56, x_57);
lean_dec_ref(x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
x_61 = lean_io_prim_handle_put_str(x_59, x_60);
lean_dec(x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec_ref(x_61);
x_62 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8;
lean_inc_ref(x_1);
x_63 = l_Lake_joinRelative(x_1, x_62);
x_64 = lean_string_utf8_byte_size(x_50);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_52);
x_67 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
x_68 = lean_string_append(x_50, x_67);
x_69 = l_IO_FS_writeFile(x_63, x_68);
lean_dec_ref(x_68);
lean_dec_ref(x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_dec_ref(x_69);
x_37 = x_51;
x_38 = x_53;
x_39 = lean_box(0);
goto block_42;
}
else
{
uint8_t x_70; 
lean_dec(x_51);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_io_error_to_string(x_71);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_apply_2(x_53, x_74, lean_box(0));
x_76 = lean_box(0);
lean_ctor_set(x_69, 0, x_76);
return x_69;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_io_error_to_string(x_77);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_apply_2(x_53, x_80, lean_box(0));
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec_ref(x_50);
x_84 = lean_ctor_get(x_52, 1);
lean_inc_ref(x_84);
lean_dec_ref(x_52);
x_85 = lean_string_utf8_byte_size(x_84);
lean_dec_ref(x_84);
x_86 = lean_nat_dec_eq(x_85, x_65);
lean_dec(x_85);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_System_FilePath_pathExists(x_63);
lean_dec_ref(x_63);
x_88 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_89 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_89 == 0)
{
x_43 = x_53;
x_44 = x_51;
x_45 = x_87;
x_46 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_90; 
x_90 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_90 == 0)
{
x_43 = x_53;
x_44 = x_51;
x_45 = x_87;
x_46 = lean_box(0);
goto block_49;
}
else
{
lean_object* x_91; size_t x_92; size_t x_93; lean_object* x_94; 
x_91 = lean_box(0);
x_92 = 0;
x_93 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_53);
x_94 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_88, x_92, x_93, x_91, x_53);
lean_dec_ref(x_94);
x_43 = x_53;
x_44 = x_51;
x_45 = x_87;
x_46 = lean_box(0);
goto block_49;
}
}
}
else
{
lean_dec_ref(x_63);
x_37 = x_51;
x_38 = x_53;
x_39 = lean_box(0);
goto block_42;
}
}
}
else
{
uint8_t x_95; 
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_61);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_61, 0);
x_97 = lean_io_error_to_string(x_96);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_apply_2(x_53, x_99, lean_box(0));
x_101 = lean_box(0);
lean_ctor_set(x_61, 0, x_101);
return x_61;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_61, 0);
lean_inc(x_102);
lean_dec(x_61);
x_103 = lean_io_error_to_string(x_102);
x_104 = 3;
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
x_106 = lean_apply_2(x_53, x_105, lean_box(0));
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec_ref(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_58);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_58, 0);
x_111 = lean_io_error_to_string(x_110);
x_112 = 3;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
x_114 = lean_apply_2(x_53, x_113, lean_box(0));
x_115 = lean_box(0);
lean_ctor_set(x_58, 0, x_115);
return x_58;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_58, 0);
lean_inc(x_116);
lean_dec(x_58);
x_117 = lean_io_error_to_string(x_116);
x_118 = 3;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = lean_apply_2(x_53, x_119, lean_box(0));
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
block_131:
{
lean_object* x_129; lean_object* x_130; 
x_129 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15;
lean_inc_ref(x_126);
x_130 = lean_apply_2(x_126, x_129, lean_box(0));
x_50 = x_124;
x_51 = x_125;
x_52 = x_127;
x_53 = x_126;
x_54 = lean_box(0);
goto block_123;
}
block_158:
{
lean_object* x_137; uint8_t x_138; 
x_137 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
x_138 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17;
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_unsigned_to_nat(0u);
x_140 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_1);
x_141 = l_Lake_GitRepo_checkoutBranch(x_137, x_1, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = lean_array_get_size(x_142);
x_144 = lean_nat_dec_lt(x_139, x_143);
if (x_144 == 0)
{
lean_dec(x_143);
lean_dec(x_142);
x_50 = x_132;
x_51 = x_133;
x_52 = x_135;
x_53 = x_134;
x_54 = lean_box(0);
goto block_123;
}
else
{
uint8_t x_145; 
x_145 = lean_nat_dec_le(x_143, x_143);
if (x_145 == 0)
{
lean_dec(x_143);
lean_dec(x_142);
x_50 = x_132;
x_51 = x_133;
x_52 = x_135;
x_53 = x_134;
x_54 = lean_box(0);
goto block_123;
}
else
{
lean_object* x_146; size_t x_147; size_t x_148; lean_object* x_149; 
x_146 = lean_box(0);
x_147 = 0;
x_148 = lean_usize_of_nat(x_143);
lean_dec(x_143);
lean_inc_ref(x_134);
x_149 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_142, x_147, x_148, x_146, x_134);
lean_dec(x_142);
lean_dec_ref(x_149);
x_50 = x_132;
x_51 = x_133;
x_52 = x_135;
x_53 = x_134;
x_54 = lean_box(0);
goto block_123;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_ctor_get(x_141, 1);
lean_inc(x_150);
lean_dec_ref(x_141);
x_151 = lean_array_get_size(x_150);
x_152 = lean_nat_dec_lt(x_139, x_151);
if (x_152 == 0)
{
lean_dec(x_151);
lean_dec(x_150);
x_124 = x_132;
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = lean_box(0);
goto block_131;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_151, x_151);
if (x_153 == 0)
{
lean_dec(x_151);
lean_dec(x_150);
x_124 = x_132;
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = lean_box(0);
goto block_131;
}
else
{
lean_object* x_154; size_t x_155; size_t x_156; lean_object* x_157; 
x_154 = lean_box(0);
x_155 = 0;
x_156 = lean_usize_of_nat(x_151);
lean_dec(x_151);
lean_inc_ref(x_134);
x_157 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_150, x_155, x_156, x_154, x_134);
lean_dec(x_150);
lean_dec_ref(x_157);
x_124 = x_132;
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = lean_box(0);
goto block_131;
}
}
}
}
else
{
x_50 = x_132;
x_51 = x_133;
x_52 = x_135;
x_53 = x_134;
x_54 = lean_box(0);
goto block_123;
}
}
block_184:
{
if (x_163 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_unsigned_to_nat(0u);
x_166 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_1);
x_167 = l_Lake_GitRepo_quietInit(x_1, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = lean_array_get_size(x_168);
x_170 = lean_nat_dec_lt(x_165, x_169);
if (x_170 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = lean_box(0);
goto block_158;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_le(x_169, x_169);
if (x_171 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = lean_box(0);
goto block_158;
}
else
{
lean_object* x_172; size_t x_173; size_t x_174; lean_object* x_175; 
x_172 = lean_box(0);
x_173 = 0;
x_174 = lean_usize_of_nat(x_169);
lean_dec(x_169);
lean_inc_ref(x_161);
x_175 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_168, x_173, x_174, x_172, x_161);
lean_dec(x_168);
lean_dec_ref(x_175);
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = lean_box(0);
goto block_158;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_167, 1);
lean_inc(x_176);
lean_dec_ref(x_167);
x_177 = lean_array_get_size(x_176);
x_178 = lean_nat_dec_lt(x_165, x_177);
if (x_178 == 0)
{
lean_dec(x_177);
lean_dec(x_176);
x_124 = x_159;
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = lean_box(0);
goto block_131;
}
else
{
uint8_t x_179; 
x_179 = lean_nat_dec_le(x_177, x_177);
if (x_179 == 0)
{
lean_dec(x_177);
lean_dec(x_176);
x_124 = x_159;
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = lean_box(0);
goto block_131;
}
else
{
lean_object* x_180; size_t x_181; size_t x_182; lean_object* x_183; 
x_180 = lean_box(0);
x_181 = 0;
x_182 = lean_usize_of_nat(x_177);
lean_dec(x_177);
lean_inc_ref(x_161);
x_183 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_176, x_181, x_182, x_180, x_161);
lean_dec(x_176);
lean_dec_ref(x_183);
x_124 = x_159;
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = lean_box(0);
goto block_131;
}
}
}
}
else
{
x_50 = x_159;
x_51 = x_160;
x_52 = x_162;
x_53 = x_161;
x_54 = lean_box(0);
goto block_123;
}
}
block_198:
{
uint8_t x_190; lean_object* x_191; uint8_t x_192; 
lean_inc_ref(x_1);
x_190 = l_Lake_GitRepo_insideWorkTree(x_1);
x_191 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_192 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_192 == 0)
{
x_159 = x_185;
x_160 = x_186;
x_161 = x_188;
x_162 = x_187;
x_163 = x_190;
x_164 = lean_box(0);
goto block_184;
}
else
{
uint8_t x_193; 
x_193 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_193 == 0)
{
x_159 = x_185;
x_160 = x_186;
x_161 = x_188;
x_162 = x_187;
x_163 = x_190;
x_164 = lean_box(0);
goto block_184;
}
else
{
lean_object* x_194; size_t x_195; size_t x_196; lean_object* x_197; 
x_194 = lean_box(0);
x_195 = 0;
x_196 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_188);
x_197 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_191, x_195, x_196, x_194, x_188);
lean_dec_ref(x_197);
x_159 = x_185;
x_160 = x_186;
x_161 = x_188;
x_162 = x_187;
x_163 = x_190;
x_164 = lean_box(0);
goto block_184;
}
}
}
block_221:
{
lean_object* x_206; 
x_206 = l_IO_FS_writeFile(x_202, x_205);
lean_dec_ref(x_205);
lean_dec_ref(x_202);
if (lean_obj_tag(x_206) == 0)
{
lean_dec_ref(x_206);
x_185 = x_199;
x_186 = x_201;
x_187 = x_203;
x_188 = x_204;
x_189 = lean_box(0);
goto block_198;
}
else
{
uint8_t x_207; 
lean_dec_ref(x_203);
lean_dec(x_201);
lean_dec_ref(x_199);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_206, 0);
x_209 = lean_io_error_to_string(x_208);
x_210 = 3;
x_211 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*1, x_210);
x_212 = lean_apply_2(x_204, x_211, lean_box(0));
x_213 = lean_box(0);
lean_ctor_set(x_206, 0, x_213);
return x_206;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_206, 0);
lean_inc(x_214);
lean_dec(x_206);
x_215 = lean_io_error_to_string(x_214);
x_216 = 3;
x_217 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set_uint8(x_217, sizeof(void*)*1, x_216);
x_218 = lean_apply_2(x_204, x_217, lean_box(0));
x_219 = lean_box(0);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
}
}
block_235:
{
if (x_227 == 0)
{
uint8_t x_229; uint8_t x_230; 
x_229 = 4;
x_230 = l_Lake_instDecidableEqInitTemplate(x_3, x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_232 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_231);
lean_dec_ref(x_231);
x_199 = x_222;
x_200 = lean_box(0);
x_201 = x_223;
x_202 = x_224;
x_203 = x_226;
x_204 = x_225;
x_205 = x_232;
goto block_221;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_2);
x_234 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_233);
lean_dec_ref(x_233);
x_199 = x_222;
x_200 = lean_box(0);
x_201 = x_223;
x_202 = x_224;
x_203 = x_226;
x_204 = x_225;
x_205 = x_234;
goto block_221;
}
}
else
{
lean_dec_ref(x_224);
lean_dec(x_2);
x_185 = x_222;
x_186 = x_223;
x_187 = x_226;
x_188 = x_225;
x_189 = lean_box(0);
goto block_198;
}
}
block_251:
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; uint8_t x_245; 
x_241 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18;
lean_inc_ref(x_1);
x_242 = l_Lake_joinRelative(x_1, x_241);
x_243 = l_System_FilePath_pathExists(x_242);
x_244 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_245 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_245 == 0)
{
x_222 = x_236;
x_223 = x_237;
x_224 = x_242;
x_225 = x_239;
x_226 = x_238;
x_227 = x_243;
x_228 = lean_box(0);
goto block_235;
}
else
{
uint8_t x_246; 
x_246 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_246 == 0)
{
x_222 = x_236;
x_223 = x_237;
x_224 = x_242;
x_225 = x_239;
x_226 = x_238;
x_227 = x_243;
x_228 = lean_box(0);
goto block_235;
}
else
{
lean_object* x_247; size_t x_248; size_t x_249; lean_object* x_250; 
x_247 = lean_box(0);
x_248 = 0;
x_249 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_239);
x_250 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_244, x_248, x_249, x_247, x_239);
lean_dec_ref(x_250);
x_222 = x_236;
x_223 = x_237;
x_224 = x_242;
x_225 = x_239;
x_226 = x_238;
x_227 = x_243;
x_228 = lean_box(0);
goto block_235;
}
}
}
block_294:
{
if (x_258 == 0)
{
uint8_t x_260; uint8_t x_261; 
x_260 = 1;
x_261 = l_Lake_instDecidableEqInitTemplate(x_3, x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_253);
x_263 = l_IO_FS_writeFile(x_254, x_262);
lean_dec_ref(x_262);
lean_dec_ref(x_254);
if (lean_obj_tag(x_263) == 0)
{
lean_dec_ref(x_263);
x_236 = x_252;
x_237 = x_256;
x_238 = x_257;
x_239 = x_255;
x_240 = lean_box(0);
goto block_251;
}
else
{
uint8_t x_264; 
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_252);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = lean_io_error_to_string(x_265);
x_267 = 3;
x_268 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set_uint8(x_268, sizeof(void*)*1, x_267);
x_269 = lean_apply_2(x_255, x_268, lean_box(0));
x_270 = lean_box(0);
lean_ctor_set(x_263, 0, x_270);
return x_263;
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_271 = lean_ctor_get(x_263, 0);
lean_inc(x_271);
lean_dec(x_263);
x_272 = lean_io_error_to_string(x_271);
x_273 = 3;
x_274 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*1, x_273);
x_275 = lean_apply_2(x_255, x_274, lean_box(0));
x_276 = lean_box(0);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_253);
x_278 = l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
x_279 = l_IO_FS_writeFile(x_254, x_278);
lean_dec_ref(x_254);
if (lean_obj_tag(x_279) == 0)
{
lean_dec_ref(x_279);
x_236 = x_252;
x_237 = x_256;
x_238 = x_257;
x_239 = x_255;
x_240 = lean_box(0);
goto block_251;
}
else
{
uint8_t x_280; 
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_252);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_281 = lean_ctor_get(x_279, 0);
x_282 = lean_io_error_to_string(x_281);
x_283 = 3;
x_284 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_283);
x_285 = lean_apply_2(x_255, x_284, lean_box(0));
x_286 = lean_box(0);
lean_ctor_set(x_279, 0, x_286);
return x_279;
}
else
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_279, 0);
lean_inc(x_287);
lean_dec(x_279);
x_288 = lean_io_error_to_string(x_287);
x_289 = 3;
x_290 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set_uint8(x_290, sizeof(void*)*1, x_289);
x_291 = lean_apply_2(x_255, x_290, lean_box(0));
x_292 = lean_box(0);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
return x_293;
}
}
}
}
else
{
lean_dec_ref(x_254);
lean_dec(x_253);
x_236 = x_252;
x_237 = x_256;
x_238 = x_257;
x_239 = x_255;
x_240 = lean_box(0);
goto block_251;
}
}
block_311:
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; uint8_t x_305; 
x_301 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_1);
x_302 = l_Lake_joinRelative(x_1, x_301);
x_303 = l_System_FilePath_pathExists(x_302);
x_304 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_305 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_305 == 0)
{
x_252 = x_296;
x_253 = x_295;
x_254 = x_302;
x_255 = x_297;
x_256 = x_298;
x_257 = x_300;
x_258 = x_303;
x_259 = lean_box(0);
goto block_294;
}
else
{
uint8_t x_306; 
x_306 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_306 == 0)
{
x_252 = x_296;
x_253 = x_295;
x_254 = x_302;
x_255 = x_297;
x_256 = x_298;
x_257 = x_300;
x_258 = x_303;
x_259 = lean_box(0);
goto block_294;
}
else
{
lean_object* x_307; size_t x_308; size_t x_309; lean_object* x_310; 
x_307 = lean_box(0);
x_308 = 0;
x_309 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_297);
x_310 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_304, x_308, x_309, x_307, x_297);
lean_dec_ref(x_310);
x_252 = x_296;
x_253 = x_295;
x_254 = x_302;
x_255 = x_297;
x_256 = x_298;
x_257 = x_300;
x_258 = x_303;
x_259 = lean_box(0);
goto block_294;
}
}
}
block_318:
{
switch (x_3) {
case 0:
{
x_295 = x_313;
x_296 = x_312;
x_297 = x_316;
x_298 = x_314;
x_299 = lean_box(0);
x_300 = x_315;
goto block_311;
}
case 1:
{
x_295 = x_313;
x_296 = x_312;
x_297 = x_316;
x_298 = x_314;
x_299 = lean_box(0);
x_300 = x_315;
goto block_311;
}
default: 
{
lean_dec(x_313);
x_236 = x_312;
x_237 = x_314;
x_238 = x_315;
x_239 = x_316;
x_240 = lean_box(0);
goto block_251;
}
}
}
block_342:
{
lean_object* x_327; 
x_327 = l_IO_FS_writeFile(x_322, x_326);
lean_dec_ref(x_326);
lean_dec_ref(x_322);
if (lean_obj_tag(x_327) == 0)
{
lean_dec_ref(x_327);
x_312 = x_320;
x_313 = x_319;
x_314 = x_323;
x_315 = x_325;
x_316 = x_324;
x_317 = lean_box(0);
goto block_318;
}
else
{
uint8_t x_328; 
lean_dec_ref(x_325);
lean_dec(x_323);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_329 = lean_ctor_get(x_327, 0);
x_330 = lean_io_error_to_string(x_329);
x_331 = 3;
x_332 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set_uint8(x_332, sizeof(void*)*1, x_331);
x_333 = lean_apply_2(x_324, x_332, lean_box(0));
x_334 = lean_box(0);
lean_ctor_set(x_327, 0, x_334);
return x_327;
}
else
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_335 = lean_ctor_get(x_327, 0);
lean_inc(x_335);
lean_dec(x_327);
x_336 = lean_io_error_to_string(x_335);
x_337 = 3;
x_338 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*1, x_337);
x_339 = lean_apply_2(x_324, x_338, lean_box(0));
x_340 = lean_box(0);
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_340);
return x_341;
}
}
}
block_356:
{
uint8_t x_350; uint8_t x_351; 
x_350 = 4;
x_351 = l_Lake_instDecidableEqInitTemplate(x_3, x_350);
if (x_351 == 0)
{
uint8_t x_352; lean_object* x_353; lean_object* x_354; 
x_352 = 1;
lean_inc(x_344);
x_353 = l_Lean_Name_toString(x_344, x_352);
lean_inc(x_344);
x_354 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_353, x_344);
lean_dec_ref(x_353);
x_319 = x_344;
x_320 = x_343;
x_321 = lean_box(0);
x_322 = x_345;
x_323 = x_346;
x_324 = x_348;
x_325 = x_347;
x_326 = x_354;
goto block_342;
}
else
{
lean_object* x_355; 
lean_inc(x_344);
x_355 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_344);
x_319 = x_344;
x_320 = x_343;
x_321 = lean_box(0);
x_322 = x_345;
x_323 = x_346;
x_324 = x_348;
x_325 = x_347;
x_326 = x_355;
goto block_342;
}
}
block_397:
{
if (x_364 == 0)
{
lean_object* x_366; 
x_366 = l_IO_FS_createDirAll(x_362);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; 
lean_dec_ref(x_366);
x_367 = l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
x_368 = l_IO_FS_writeFile(x_357, x_367);
lean_dec_ref(x_357);
if (lean_obj_tag(x_368) == 0)
{
lean_dec_ref(x_368);
x_343 = x_359;
x_344 = x_358;
x_345 = x_360;
x_346 = x_361;
x_347 = x_363;
x_348 = x_7;
x_349 = lean_box(0);
goto block_356;
}
else
{
uint8_t x_369; 
lean_dec_ref(x_363);
lean_dec(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec(x_358);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_369 = !lean_is_exclusive(x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_370 = lean_ctor_get(x_368, 0);
x_371 = lean_io_error_to_string(x_370);
x_372 = 3;
x_373 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set_uint8(x_373, sizeof(void*)*1, x_372);
x_374 = lean_apply_2(x_7, x_373, lean_box(0));
x_375 = lean_box(0);
lean_ctor_set(x_368, 0, x_375);
return x_368;
}
else
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_376 = lean_ctor_get(x_368, 0);
lean_inc(x_376);
lean_dec(x_368);
x_377 = lean_io_error_to_string(x_376);
x_378 = 3;
x_379 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set_uint8(x_379, sizeof(void*)*1, x_378);
x_380 = lean_apply_2(x_7, x_379, lean_box(0));
x_381 = lean_box(0);
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_381);
return x_382;
}
}
}
else
{
uint8_t x_383; 
lean_dec_ref(x_363);
lean_dec(x_361);
lean_dec_ref(x_360);
lean_dec_ref(x_359);
lean_dec(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_383 = !lean_is_exclusive(x_366);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_384 = lean_ctor_get(x_366, 0);
x_385 = lean_io_error_to_string(x_384);
x_386 = 3;
x_387 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set_uint8(x_387, sizeof(void*)*1, x_386);
x_388 = lean_apply_2(x_7, x_387, lean_box(0));
x_389 = lean_box(0);
lean_ctor_set(x_366, 0, x_389);
return x_366;
}
else
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_390 = lean_ctor_get(x_366, 0);
lean_inc(x_390);
lean_dec(x_366);
x_391 = lean_io_error_to_string(x_390);
x_392 = 3;
x_393 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set_uint8(x_393, sizeof(void*)*1, x_392);
x_394 = lean_apply_2(x_7, x_393, lean_box(0));
x_395 = lean_box(0);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_395);
return x_396;
}
}
}
else
{
lean_dec_ref(x_362);
lean_dec_ref(x_357);
x_343 = x_359;
x_344 = x_358;
x_345 = x_360;
x_346 = x_361;
x_347 = x_363;
x_348 = x_7;
x_349 = lean_box(0);
goto block_356;
}
}
block_436:
{
lean_object* x_407; lean_object* x_408; 
lean_inc(x_406);
lean_inc(x_401);
lean_inc(x_2);
x_407 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_3, x_4, x_2, x_401, x_406);
x_408 = l_IO_FS_writeFile(x_400, x_407);
lean_dec_ref(x_407);
lean_dec_ref(x_400);
if (lean_obj_tag(x_408) == 0)
{
lean_dec_ref(x_408);
if (lean_obj_tag(x_403) == 1)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; uint8_t x_416; 
x_409 = lean_ctor_get(x_403, 0);
lean_inc(x_409);
lean_dec_ref(x_403);
x_410 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
lean_inc(x_409);
x_411 = l_System_FilePath_withExtension(x_409, x_410);
x_412 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19;
lean_inc_ref(x_411);
x_413 = l_Lake_joinRelative(x_411, x_412);
x_414 = l_System_FilePath_pathExists(x_413);
x_415 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_416 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_416 == 0)
{
x_357 = x_413;
x_358 = x_401;
x_359 = x_402;
x_360 = x_409;
x_361 = x_406;
x_362 = x_411;
x_363 = x_405;
x_364 = x_414;
x_365 = lean_box(0);
goto block_397;
}
else
{
uint8_t x_417; 
x_417 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_417 == 0)
{
x_357 = x_413;
x_358 = x_401;
x_359 = x_402;
x_360 = x_409;
x_361 = x_406;
x_362 = x_411;
x_363 = x_405;
x_364 = x_414;
x_365 = lean_box(0);
goto block_397;
}
else
{
lean_object* x_418; size_t x_419; size_t x_420; lean_object* x_421; 
x_418 = lean_box(0);
x_419 = 0;
x_420 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_421 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_415, x_419, x_420, x_418, x_7);
lean_dec_ref(x_421);
x_357 = x_413;
x_358 = x_401;
x_359 = x_402;
x_360 = x_409;
x_361 = x_406;
x_362 = x_411;
x_363 = x_405;
x_364 = x_414;
x_365 = lean_box(0);
goto block_397;
}
}
}
else
{
lean_dec(x_403);
x_312 = x_402;
x_313 = x_401;
x_314 = x_406;
x_315 = x_405;
x_316 = x_7;
x_317 = lean_box(0);
goto block_318;
}
}
else
{
uint8_t x_422; 
lean_dec(x_406);
lean_dec_ref(x_405);
lean_dec(x_403);
lean_dec_ref(x_402);
lean_dec(x_401);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_422 = !lean_is_exclusive(x_408);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_423 = lean_ctor_get(x_408, 0);
x_424 = lean_io_error_to_string(x_423);
x_425 = 3;
x_426 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set_uint8(x_426, sizeof(void*)*1, x_425);
x_427 = lean_apply_2(x_7, x_426, lean_box(0));
x_428 = lean_box(0);
lean_ctor_set(x_408, 0, x_428);
return x_408;
}
else
{
lean_object* x_429; lean_object* x_430; uint8_t x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_429 = lean_ctor_get(x_408, 0);
lean_inc(x_429);
lean_dec(x_408);
x_430 = lean_io_error_to_string(x_429);
x_431 = 3;
x_432 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*1, x_431);
x_433 = lean_apply_2(x_7, x_432, lean_box(0));
x_434 = lean_box(0);
x_435 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
}
}
block_446:
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_5, 1);
x_441 = lean_ctor_get(x_5, 15);
lean_inc_ref(x_441);
x_442 = l_Lake_ToolchainVer_ofString(x_441);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc_ref(x_443);
lean_dec_ref(x_442);
x_444 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_444, 0, x_443);
lean_inc_ref(x_440);
lean_inc_ref(x_441);
x_401 = x_437;
x_402 = x_441;
x_403 = x_438;
x_404 = lean_box(0);
x_405 = x_440;
x_406 = x_444;
goto block_436;
}
else
{
lean_object* x_445; 
lean_dec_ref(x_442);
x_445 = lean_box(0);
lean_inc_ref(x_440);
lean_inc_ref(x_441);
x_401 = x_437;
x_402 = x_441;
x_403 = x_438;
x_404 = lean_box(0);
x_405 = x_440;
x_406 = x_445;
goto block_436;
}
}
block_453:
{
if (x_449 == 0)
{
lean_object* x_451; 
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_448);
x_437 = x_447;
x_438 = x_451;
x_439 = lean_box(0);
goto block_446;
}
else
{
lean_object* x_452; 
lean_dec_ref(x_448);
x_452 = lean_box(0);
x_437 = x_447;
x_438 = x_452;
x_439 = lean_box(0);
goto block_446;
}
}
block_469:
{
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; uint8_t x_460; lean_object* x_461; uint8_t x_462; 
lean_dec_ref(x_455);
x_458 = l_Lake_toUpperCamelCase(x_2);
lean_inc(x_458);
x_459 = l_Lean_modToFilePath(x_1, x_458, x_454);
lean_dec_ref(x_454);
x_460 = l_System_FilePath_pathExists(x_459);
x_461 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_462 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_462 == 0)
{
x_447 = x_458;
x_448 = x_459;
x_449 = x_460;
x_450 = lean_box(0);
goto block_453;
}
else
{
uint8_t x_463; 
x_463 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_463 == 0)
{
x_447 = x_458;
x_448 = x_459;
x_449 = x_460;
x_450 = lean_box(0);
goto block_453;
}
else
{
lean_object* x_464; size_t x_465; size_t x_466; lean_object* x_467; 
x_464 = lean_box(0);
x_465 = 0;
x_466 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_467 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_461, x_465, x_466, x_464, x_7);
lean_dec_ref(x_467);
x_447 = x_458;
x_448 = x_459;
x_449 = x_460;
x_450 = lean_box(0);
goto block_453;
}
}
}
else
{
lean_object* x_468; 
lean_dec_ref(x_454);
x_468 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_468, 0, x_455);
lean_inc(x_2);
x_437 = x_2;
x_438 = x_468;
x_439 = lean_box(0);
goto block_446;
}
}
block_476:
{
uint8_t x_474; uint8_t x_475; 
x_474 = 1;
x_475 = l_Lake_instDecidableEqInitTemplate(x_3, x_474);
if (x_475 == 0)
{
x_454 = x_470;
x_455 = x_471;
x_456 = lean_box(0);
x_457 = x_472;
goto block_469;
}
else
{
x_454 = x_470;
x_455 = x_471;
x_456 = lean_box(0);
x_457 = x_475;
goto block_469;
}
}
block_488:
{
lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; uint8_t x_482; 
x_478 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20;
lean_inc(x_2);
x_479 = l_Lean_modToFilePath(x_1, x_2, x_478);
x_480 = l_System_FilePath_pathExists(x_479);
x_481 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_482 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_482 == 0)
{
x_470 = x_478;
x_471 = x_479;
x_472 = x_480;
x_473 = lean_box(0);
goto block_476;
}
else
{
uint8_t x_483; 
x_483 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_483 == 0)
{
x_470 = x_478;
x_471 = x_479;
x_472 = x_480;
x_473 = lean_box(0);
goto block_476;
}
else
{
lean_object* x_484; size_t x_485; size_t x_486; lean_object* x_487; 
x_484 = lean_box(0);
x_485 = 0;
x_486 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_7);
x_487 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_481, x_485, x_486, x_484, x_7);
lean_dec_ref(x_487);
x_470 = x_478;
x_471 = x_479;
x_472 = x_480;
x_473 = lean_box(0);
goto block_476;
}
}
}
block_516:
{
if (x_489 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_unsigned_to_nat(0u);
x_492 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_1);
x_493 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_1, x_3, x_492);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec_ref(x_493);
x_495 = lean_array_get_size(x_494);
x_496 = lean_nat_dec_lt(x_491, x_495);
if (x_496 == 0)
{
lean_dec(x_495);
lean_dec(x_494);
x_477 = lean_box(0);
goto block_488;
}
else
{
uint8_t x_497; 
x_497 = lean_nat_dec_le(x_495, x_495);
if (x_497 == 0)
{
lean_dec(x_495);
lean_dec(x_494);
x_477 = lean_box(0);
goto block_488;
}
else
{
lean_object* x_498; size_t x_499; size_t x_500; lean_object* x_501; 
x_498 = lean_box(0);
x_499 = 0;
x_500 = lean_usize_of_nat(x_495);
lean_dec(x_495);
lean_inc_ref(x_7);
x_501 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_494, x_499, x_500, x_498, x_7);
lean_dec(x_494);
lean_dec_ref(x_501);
x_477 = lean_box(0);
goto block_488;
}
}
}
else
{
lean_object* x_502; lean_object* x_503; uint8_t x_504; 
lean_dec_ref(x_400);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_502 = lean_ctor_get(x_493, 1);
lean_inc(x_502);
lean_dec_ref(x_493);
x_503 = lean_array_get_size(x_502);
x_504 = lean_nat_dec_lt(x_491, x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec_ref(x_7);
x_505 = lean_box(0);
x_506 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_506, 0, x_505);
return x_506;
}
else
{
uint8_t x_507; 
x_507 = lean_nat_dec_le(x_503, x_503);
if (x_507 == 0)
{
lean_dec(x_503);
lean_dec(x_502);
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_508; size_t x_509; size_t x_510; lean_object* x_511; 
x_508 = lean_box(0);
x_509 = 0;
x_510 = lean_usize_of_nat(x_503);
lean_dec(x_503);
x_511 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_502, x_509, x_510, x_508, x_7);
lean_dec(x_502);
lean_dec_ref(x_511);
x_9 = lean_box(0);
goto block_12;
}
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec_ref(x_400);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_512 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22;
x_513 = lean_apply_2(x_7, x_512, lean_box(0));
x_514 = lean_box(0);
x_515 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_515, 0, x_514);
return x_515;
}
}
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_CLI_Init_0__Lake_initPkg___elam__0___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0_spec__0(x_1, x_2, x_3);
return x_5;
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
static lean_object* _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
x_2 = l_instBEqOfDecidableEq___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1;
x_2 = l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_string_utf8_get(x_1, x_3);
x_6 = l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__0;
x_7 = l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2;
x_8 = lean_box_uint32(x_5);
x_9 = l_List_elem___redArg(x_6, x_8, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_dec(x_3);
return x_9;
}
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_2, x_4);
x_7 = 46;
x_8 = lean_uint32_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_1 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_9;
goto _start;
}
else
{
lean_dec(x_4);
return x_1;
}
}
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
uint8_t x_14; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_string_utf8_byte_size(x_1);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_dec_eq(x_29, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(x_31, x_1, x_29, x_30);
lean_dec(x_29);
if (x_32 == 0)
{
goto block_13;
}
else
{
x_14 = x_31;
goto block_28;
}
}
else
{
lean_dec(x_29);
x_14 = x_31;
goto block_28;
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
block_28:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_string_utf8_byte_size(x_1);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(x_1, x_15, x_16);
lean_dec(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__1;
x_19 = l_String_mapAux___at___00__private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents_spec__0(x_1, x_16);
x_20 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__8;
x_21 = l_List_elem___redArg(x_18, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l___private_Lake_CLI_Init_0__Lake_validatePkgName___closed__10;
x_25 = lean_array_get_size(x_2);
x_26 = lean_array_push(x_2, x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
LEAN_EXPORT lean_object* l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
x_6 = l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___00Lake_init_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_3, x_2);
if (x_9 == 0)
{
return x_3;
}
else
{
uint32_t x_10; uint8_t x_11; uint32_t x_17; uint8_t x_18; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_10, x_19);
x_11 = x_20;
goto block_16;
}
else
{
x_11 = x_18;
goto block_16;
}
block_16:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 13;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 10;
x_15 = lean_uint32_dec_eq(x_10, x_14);
x_7 = x_15;
goto block_8;
}
else
{
x_7 = x_13;
goto block_8;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_8:
{
if (x_7 == 0)
{
return x_3;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___00Lake_init_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; uint8_t x_6; uint32_t x_9; uint8_t x_10; uint32_t x_17; uint8_t x_18; 
x_5 = lean_string_utf8_prev(x_1, x_3);
x_9 = lean_string_utf8_get(x_1, x_5);
x_17 = 32;
x_18 = lean_uint32_dec_eq(x_9, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 9;
x_20 = lean_uint32_dec_eq(x_9, x_19);
x_10 = x_20;
goto block_16;
}
else
{
x_10 = x_18;
goto block_16;
}
block_8:
{
if (x_6 == 0)
{
lean_dec(x_5);
return x_3;
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
block_16:
{
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 13;
x_12 = lean_uint32_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 10;
x_14 = lean_uint32_dec_eq(x_9, x_13);
x_6 = x_14;
goto block_8;
}
else
{
x_6 = x_12;
goto block_8;
}
}
else
{
lean_dec(x_3);
x_3 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_447; lean_object* x_448; uint8_t x_449; lean_object* x_450; lean_object* x_454; lean_object* x_455; lean_object* x_456; uint8_t x_457; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_477; uint8_t x_489; lean_object* x_490; lean_object* x_517; uint8_t x_518; 
x_13 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__0;
x_398 = l_Lake_ConfigLang_fileExtension(x_5);
x_399 = l_System_FilePath_addExtension(x_13, x_398);
lean_dec_ref(x_398);
lean_inc_ref(x_2);
x_400 = l_Lake_joinRelative(x_2, x_399);
x_489 = l_System_FilePath_pathExists(x_400);
x_517 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_518 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_518 == 0)
{
x_490 = lean_box(0);
goto block_516;
}
else
{
uint8_t x_519; 
x_519 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_519 == 0)
{
x_490 = lean_box(0);
goto block_516;
}
else
{
lean_object* x_520; size_t x_521; size_t x_522; lean_object* x_523; 
x_520 = lean_box(0);
x_521 = 0;
x_522 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_523 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_517, x_521, x_522, x_520, x_1);
lean_dec_ref(x_523);
x_490 = lean_box(0);
goto block_516;
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
block_30:
{
if (x_7 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_box(0);
x_17 = lean_box(0);
x_18 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
lean_inc_ref(x_2);
x_19 = l_Lake_joinRelative(x_2, x_18);
lean_inc_ref(x_19);
x_20 = l_Lake_joinRelative(x_19, x_13);
x_21 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__1;
x_22 = lean_box(1);
x_23 = lean_box(0);
x_24 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
x_25 = lean_alloc_ctor(0, 13, 3);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_16);
lean_ctor_set(x_25, 2, x_2);
lean_ctor_set(x_25, 3, x_17);
lean_ctor_set(x_25, 4, x_18);
lean_ctor_set(x_25, 5, x_19);
lean_ctor_set(x_25, 6, x_13);
lean_ctor_set(x_25, 7, x_20);
lean_ctor_set(x_25, 8, x_21);
lean_ctor_set(x_25, 9, x_22);
lean_ctor_set(x_25, 10, x_23);
lean_ctor_set(x_25, 11, x_24);
lean_ctor_set(x_25, 12, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*13, x_7);
lean_ctor_set_uint8(x_25, sizeof(void*)*13 + 1, x_7);
lean_ctor_set_uint8(x_25, sizeof(void*)*13 + 2, x_7);
x_26 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__2;
x_27 = l_Lake_updateManifest(x_25, x_26, x_14);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec_ref(x_14);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
block_36:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__4;
lean_inc_ref(x_32);
x_35 = lean_apply_2(x_32, x_34, lean_box(0));
x_14 = x_32;
x_15 = lean_box(0);
goto block_30;
}
else
{
lean_dec_ref(x_31);
x_14 = x_32;
x_15 = lean_box(0);
goto block_30;
}
}
block_42:
{
switch (x_4) {
case 3:
{
x_31 = x_37;
x_32 = x_38;
x_33 = lean_box(0);
goto block_36;
}
case 4:
{
x_31 = x_37;
x_32 = x_38;
x_33 = lean_box(0);
goto block_36;
}
default: 
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_38);
lean_dec(x_37);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
block_49:
{
if (x_45 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__6;
lean_inc_ref(x_43);
x_48 = lean_apply_2(x_43, x_47, lean_box(0));
x_37 = x_44;
x_38 = x_43;
x_39 = lean_box(0);
goto block_42;
}
else
{
x_37 = x_44;
x_38 = x_43;
x_39 = lean_box(0);
goto block_42;
}
}
block_123:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_55 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__7;
lean_inc_ref(x_2);
x_56 = l_Lake_joinRelative(x_2, x_55);
x_57 = 4;
x_58 = lean_io_prim_handle_mk(x_56, x_57);
lean_dec_ref(x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents;
x_61 = lean_io_prim_handle_put_str(x_59, x_60);
lean_dec(x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec_ref(x_61);
x_62 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__8;
lean_inc_ref(x_2);
x_63 = l_Lake_joinRelative(x_2, x_62);
x_64 = lean_string_utf8_byte_size(x_51);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_eq(x_64, x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_50);
x_67 = l___private_Lake_CLI_Init_0__Lake_gitignoreContents___closed__3;
x_68 = lean_string_append(x_51, x_67);
x_69 = l_IO_FS_writeFile(x_63, x_68);
lean_dec_ref(x_68);
lean_dec_ref(x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_dec_ref(x_69);
x_37 = x_52;
x_38 = x_53;
x_39 = lean_box(0);
goto block_42;
}
else
{
uint8_t x_70; 
lean_dec(x_52);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_io_error_to_string(x_71);
x_73 = 3;
x_74 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_73);
x_75 = lean_apply_2(x_53, x_74, lean_box(0));
x_76 = lean_box(0);
lean_ctor_set(x_69, 0, x_76);
return x_69;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_io_error_to_string(x_77);
x_79 = 3;
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_79);
x_81 = lean_apply_2(x_53, x_80, lean_box(0));
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec_ref(x_51);
x_84 = lean_ctor_get(x_50, 1);
lean_inc_ref(x_84);
lean_dec_ref(x_50);
x_85 = lean_string_utf8_byte_size(x_84);
lean_dec_ref(x_84);
x_86 = lean_nat_dec_eq(x_85, x_65);
lean_dec(x_85);
if (x_86 == 0)
{
uint8_t x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_System_FilePath_pathExists(x_63);
lean_dec_ref(x_63);
x_88 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_89 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_89 == 0)
{
x_43 = x_53;
x_44 = x_52;
x_45 = x_87;
x_46 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_90; 
x_90 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_90 == 0)
{
x_43 = x_53;
x_44 = x_52;
x_45 = x_87;
x_46 = lean_box(0);
goto block_49;
}
else
{
lean_object* x_91; size_t x_92; size_t x_93; lean_object* x_94; 
x_91 = lean_box(0);
x_92 = 0;
x_93 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_53);
x_94 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_88, x_92, x_93, x_91, x_53);
lean_dec_ref(x_94);
x_43 = x_53;
x_44 = x_52;
x_45 = x_87;
x_46 = lean_box(0);
goto block_49;
}
}
}
else
{
lean_dec_ref(x_63);
x_37 = x_52;
x_38 = x_53;
x_39 = lean_box(0);
goto block_42;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_95 = !lean_is_exclusive(x_61);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_61, 0);
x_97 = lean_io_error_to_string(x_96);
x_98 = 3;
x_99 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*1, x_98);
x_100 = lean_apply_2(x_53, x_99, lean_box(0));
x_101 = lean_box(0);
lean_ctor_set(x_61, 0, x_101);
return x_61;
}
else
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_102 = lean_ctor_get(x_61, 0);
lean_inc(x_102);
lean_dec(x_61);
x_103 = lean_io_error_to_string(x_102);
x_104 = 3;
x_105 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set_uint8(x_105, sizeof(void*)*1, x_104);
x_106 = lean_apply_2(x_53, x_105, lean_box(0));
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_109 = !lean_is_exclusive(x_58);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_110 = lean_ctor_get(x_58, 0);
x_111 = lean_io_error_to_string(x_110);
x_112 = 3;
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_112);
x_114 = lean_apply_2(x_53, x_113, lean_box(0));
x_115 = lean_box(0);
lean_ctor_set(x_58, 0, x_115);
return x_58;
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_116 = lean_ctor_get(x_58, 0);
lean_inc(x_116);
lean_dec(x_58);
x_117 = lean_io_error_to_string(x_116);
x_118 = 3;
x_119 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set_uint8(x_119, sizeof(void*)*1, x_118);
x_120 = lean_apply_2(x_53, x_119, lean_box(0));
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
return x_122;
}
}
}
block_131:
{
lean_object* x_129; lean_object* x_130; 
x_129 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__15;
lean_inc_ref(x_124);
x_130 = lean_apply_2(x_124, x_129, lean_box(0));
x_50 = x_125;
x_51 = x_126;
x_52 = x_127;
x_53 = x_124;
x_54 = lean_box(0);
goto block_123;
}
block_158:
{
lean_object* x_137; uint8_t x_138; 
x_137 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__16;
x_138 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__17;
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_unsigned_to_nat(0u);
x_140 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_2);
x_141 = l_Lake_GitRepo_checkoutBranch(x_137, x_2, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = lean_array_get_size(x_142);
x_144 = lean_nat_dec_lt(x_139, x_143);
if (x_144 == 0)
{
lean_dec(x_143);
lean_dec(x_142);
x_50 = x_133;
x_51 = x_134;
x_52 = x_135;
x_53 = x_132;
x_54 = lean_box(0);
goto block_123;
}
else
{
uint8_t x_145; 
x_145 = lean_nat_dec_le(x_143, x_143);
if (x_145 == 0)
{
lean_dec(x_143);
lean_dec(x_142);
x_50 = x_133;
x_51 = x_134;
x_52 = x_135;
x_53 = x_132;
x_54 = lean_box(0);
goto block_123;
}
else
{
lean_object* x_146; size_t x_147; size_t x_148; lean_object* x_149; 
x_146 = lean_box(0);
x_147 = 0;
x_148 = lean_usize_of_nat(x_143);
lean_dec(x_143);
lean_inc_ref(x_132);
x_149 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_142, x_147, x_148, x_146, x_132);
lean_dec(x_142);
lean_dec_ref(x_149);
x_50 = x_133;
x_51 = x_134;
x_52 = x_135;
x_53 = x_132;
x_54 = lean_box(0);
goto block_123;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_ctor_get(x_141, 1);
lean_inc(x_150);
lean_dec_ref(x_141);
x_151 = lean_array_get_size(x_150);
x_152 = lean_nat_dec_lt(x_139, x_151);
if (x_152 == 0)
{
lean_dec(x_151);
lean_dec(x_150);
x_124 = x_132;
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = lean_box(0);
goto block_131;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_le(x_151, x_151);
if (x_153 == 0)
{
lean_dec(x_151);
lean_dec(x_150);
x_124 = x_132;
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = lean_box(0);
goto block_131;
}
else
{
lean_object* x_154; size_t x_155; size_t x_156; lean_object* x_157; 
x_154 = lean_box(0);
x_155 = 0;
x_156 = lean_usize_of_nat(x_151);
lean_dec(x_151);
lean_inc_ref(x_132);
x_157 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_150, x_155, x_156, x_154, x_132);
lean_dec(x_150);
lean_dec_ref(x_157);
x_124 = x_132;
x_125 = x_133;
x_126 = x_134;
x_127 = x_135;
x_128 = lean_box(0);
goto block_131;
}
}
}
}
else
{
x_50 = x_133;
x_51 = x_134;
x_52 = x_135;
x_53 = x_132;
x_54 = lean_box(0);
goto block_123;
}
}
block_184:
{
if (x_163 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_unsigned_to_nat(0u);
x_166 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_2);
x_167 = l_Lake_GitRepo_quietInit(x_2, x_166);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = lean_array_get_size(x_168);
x_170 = lean_nat_dec_lt(x_165, x_169);
if (x_170 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = lean_box(0);
goto block_158;
}
else
{
uint8_t x_171; 
x_171 = lean_nat_dec_le(x_169, x_169);
if (x_171 == 0)
{
lean_dec(x_169);
lean_dec(x_168);
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = lean_box(0);
goto block_158;
}
else
{
lean_object* x_172; size_t x_173; size_t x_174; lean_object* x_175; 
x_172 = lean_box(0);
x_173 = 0;
x_174 = lean_usize_of_nat(x_169);
lean_dec(x_169);
lean_inc_ref(x_159);
x_175 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_168, x_173, x_174, x_172, x_159);
lean_dec(x_168);
lean_dec_ref(x_175);
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = lean_box(0);
goto block_158;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_167, 1);
lean_inc(x_176);
lean_dec_ref(x_167);
x_177 = lean_array_get_size(x_176);
x_178 = lean_nat_dec_lt(x_165, x_177);
if (x_178 == 0)
{
lean_dec(x_177);
lean_dec(x_176);
x_124 = x_159;
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = lean_box(0);
goto block_131;
}
else
{
uint8_t x_179; 
x_179 = lean_nat_dec_le(x_177, x_177);
if (x_179 == 0)
{
lean_dec(x_177);
lean_dec(x_176);
x_124 = x_159;
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = lean_box(0);
goto block_131;
}
else
{
lean_object* x_180; size_t x_181; size_t x_182; lean_object* x_183; 
x_180 = lean_box(0);
x_181 = 0;
x_182 = lean_usize_of_nat(x_177);
lean_dec(x_177);
lean_inc_ref(x_159);
x_183 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_176, x_181, x_182, x_180, x_159);
lean_dec(x_176);
lean_dec_ref(x_183);
x_124 = x_159;
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = lean_box(0);
goto block_131;
}
}
}
}
else
{
x_50 = x_160;
x_51 = x_161;
x_52 = x_162;
x_53 = x_159;
x_54 = lean_box(0);
goto block_123;
}
}
block_198:
{
uint8_t x_190; lean_object* x_191; uint8_t x_192; 
lean_inc_ref(x_2);
x_190 = l_Lake_GitRepo_insideWorkTree(x_2);
x_191 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_192 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_192 == 0)
{
x_159 = x_188;
x_160 = x_185;
x_161 = x_186;
x_162 = x_187;
x_163 = x_190;
x_164 = lean_box(0);
goto block_184;
}
else
{
uint8_t x_193; 
x_193 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_193 == 0)
{
x_159 = x_188;
x_160 = x_185;
x_161 = x_186;
x_162 = x_187;
x_163 = x_190;
x_164 = lean_box(0);
goto block_184;
}
else
{
lean_object* x_194; size_t x_195; size_t x_196; lean_object* x_197; 
x_194 = lean_box(0);
x_195 = 0;
x_196 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_188);
x_197 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_191, x_195, x_196, x_194, x_188);
lean_dec_ref(x_197);
x_159 = x_188;
x_160 = x_185;
x_161 = x_186;
x_162 = x_187;
x_163 = x_190;
x_164 = lean_box(0);
goto block_184;
}
}
}
block_221:
{
lean_object* x_206; 
x_206 = l_IO_FS_writeFile(x_204, x_205);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
if (lean_obj_tag(x_206) == 0)
{
lean_dec_ref(x_206);
x_185 = x_199;
x_186 = x_200;
x_187 = x_201;
x_188 = x_202;
x_189 = lean_box(0);
goto block_198;
}
else
{
uint8_t x_207; 
lean_dec(x_201);
lean_dec_ref(x_200);
lean_dec_ref(x_199);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_207 = !lean_is_exclusive(x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_208 = lean_ctor_get(x_206, 0);
x_209 = lean_io_error_to_string(x_208);
x_210 = 3;
x_211 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set_uint8(x_211, sizeof(void*)*1, x_210);
x_212 = lean_apply_2(x_202, x_211, lean_box(0));
x_213 = lean_box(0);
lean_ctor_set(x_206, 0, x_213);
return x_206;
}
else
{
lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_206, 0);
lean_inc(x_214);
lean_dec(x_206);
x_215 = lean_io_error_to_string(x_214);
x_216 = 3;
x_217 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set_uint8(x_217, sizeof(void*)*1, x_216);
x_218 = lean_apply_2(x_202, x_217, lean_box(0));
x_219 = lean_box(0);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
return x_220;
}
}
}
block_235:
{
if (x_227 == 0)
{
uint8_t x_229; uint8_t x_230; 
x_229 = 4;
x_230 = l_Lake_instDecidableEqInitTemplate(x_4, x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; 
x_231 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_232 = l___private_Lake_CLI_Init_0__Lake_readmeFileContents(x_231);
lean_dec_ref(x_231);
x_199 = x_222;
x_200 = x_223;
x_201 = x_224;
x_202 = x_225;
x_203 = lean_box(0);
x_204 = x_226;
x_205 = x_232;
goto block_221;
}
else
{
lean_object* x_233; lean_object* x_234; 
x_233 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_3);
x_234 = l___private_Lake_CLI_Init_0__Lake_mathReadmeFileContents(x_233);
lean_dec_ref(x_233);
x_199 = x_222;
x_200 = x_223;
x_201 = x_224;
x_202 = x_225;
x_203 = lean_box(0);
x_204 = x_226;
x_205 = x_234;
goto block_221;
}
}
else
{
lean_dec_ref(x_226);
lean_dec(x_3);
x_185 = x_222;
x_186 = x_223;
x_187 = x_224;
x_188 = x_225;
x_189 = lean_box(0);
goto block_198;
}
}
block_251:
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; lean_object* x_244; uint8_t x_245; 
x_241 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__18;
lean_inc_ref(x_2);
x_242 = l_Lake_joinRelative(x_2, x_241);
x_243 = l_System_FilePath_pathExists(x_242);
x_244 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_245 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_245 == 0)
{
x_222 = x_236;
x_223 = x_237;
x_224 = x_238;
x_225 = x_239;
x_226 = x_242;
x_227 = x_243;
x_228 = lean_box(0);
goto block_235;
}
else
{
uint8_t x_246; 
x_246 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_246 == 0)
{
x_222 = x_236;
x_223 = x_237;
x_224 = x_238;
x_225 = x_239;
x_226 = x_242;
x_227 = x_243;
x_228 = lean_box(0);
goto block_235;
}
else
{
lean_object* x_247; size_t x_248; size_t x_249; lean_object* x_250; 
x_247 = lean_box(0);
x_248 = 0;
x_249 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_239);
x_250 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_244, x_248, x_249, x_247, x_239);
lean_dec_ref(x_250);
x_222 = x_236;
x_223 = x_237;
x_224 = x_238;
x_225 = x_239;
x_226 = x_242;
x_227 = x_243;
x_228 = lean_box(0);
goto block_235;
}
}
}
block_294:
{
if (x_258 == 0)
{
uint8_t x_260; uint8_t x_261; 
x_260 = 1;
x_261 = l_Lake_instDecidableEqInitTemplate(x_4, x_260);
if (x_261 == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = l___private_Lake_CLI_Init_0__Lake_mainFileContents(x_257);
x_263 = l_IO_FS_writeFile(x_254, x_262);
lean_dec_ref(x_262);
lean_dec_ref(x_254);
if (lean_obj_tag(x_263) == 0)
{
lean_dec_ref(x_263);
x_236 = x_252;
x_237 = x_253;
x_238 = x_255;
x_239 = x_256;
x_240 = lean_box(0);
goto block_251;
}
else
{
uint8_t x_264; 
lean_dec(x_255);
lean_dec_ref(x_253);
lean_dec_ref(x_252);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_265 = lean_ctor_get(x_263, 0);
x_266 = lean_io_error_to_string(x_265);
x_267 = 3;
x_268 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set_uint8(x_268, sizeof(void*)*1, x_267);
x_269 = lean_apply_2(x_256, x_268, lean_box(0));
x_270 = lean_box(0);
lean_ctor_set(x_263, 0, x_270);
return x_263;
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_271 = lean_ctor_get(x_263, 0);
lean_inc(x_271);
lean_dec(x_263);
x_272 = lean_io_error_to_string(x_271);
x_273 = 3;
x_274 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*1, x_273);
x_275 = lean_apply_2(x_256, x_274, lean_box(0));
x_276 = lean_box(0);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; 
lean_dec(x_257);
x_278 = l___private_Lake_CLI_Init_0__Lake_exeFileContents___closed__0;
x_279 = l_IO_FS_writeFile(x_254, x_278);
lean_dec_ref(x_254);
if (lean_obj_tag(x_279) == 0)
{
lean_dec_ref(x_279);
x_236 = x_252;
x_237 = x_253;
x_238 = x_255;
x_239 = x_256;
x_240 = lean_box(0);
goto block_251;
}
else
{
uint8_t x_280; 
lean_dec(x_255);
lean_dec_ref(x_253);
lean_dec_ref(x_252);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_280 = !lean_is_exclusive(x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; uint8_t x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_281 = lean_ctor_get(x_279, 0);
x_282 = lean_io_error_to_string(x_281);
x_283 = 3;
x_284 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set_uint8(x_284, sizeof(void*)*1, x_283);
x_285 = lean_apply_2(x_256, x_284, lean_box(0));
x_286 = lean_box(0);
lean_ctor_set(x_279, 0, x_286);
return x_279;
}
else
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_279, 0);
lean_inc(x_287);
lean_dec(x_279);
x_288 = lean_io_error_to_string(x_287);
x_289 = 3;
x_290 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set_uint8(x_290, sizeof(void*)*1, x_289);
x_291 = lean_apply_2(x_256, x_290, lean_box(0));
x_292 = lean_box(0);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
return x_293;
}
}
}
}
else
{
lean_dec(x_257);
lean_dec_ref(x_254);
x_236 = x_252;
x_237 = x_253;
x_238 = x_255;
x_239 = x_256;
x_240 = lean_box(0);
goto block_251;
}
}
block_311:
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; uint8_t x_305; 
x_301 = l___private_Lake_CLI_Init_0__Lake_mainFileName;
lean_inc_ref(x_2);
x_302 = l_Lake_joinRelative(x_2, x_301);
x_303 = l_System_FilePath_pathExists(x_302);
x_304 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_305 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_305 == 0)
{
x_252 = x_295;
x_253 = x_296;
x_254 = x_302;
x_255 = x_297;
x_256 = x_299;
x_257 = x_298;
x_258 = x_303;
x_259 = lean_box(0);
goto block_294;
}
else
{
uint8_t x_306; 
x_306 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_306 == 0)
{
x_252 = x_295;
x_253 = x_296;
x_254 = x_302;
x_255 = x_297;
x_256 = x_299;
x_257 = x_298;
x_258 = x_303;
x_259 = lean_box(0);
goto block_294;
}
else
{
lean_object* x_307; size_t x_308; size_t x_309; lean_object* x_310; 
x_307 = lean_box(0);
x_308 = 0;
x_309 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_299);
x_310 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_304, x_308, x_309, x_307, x_299);
lean_dec_ref(x_310);
x_252 = x_295;
x_253 = x_296;
x_254 = x_302;
x_255 = x_297;
x_256 = x_299;
x_257 = x_298;
x_258 = x_303;
x_259 = lean_box(0);
goto block_294;
}
}
}
block_318:
{
switch (x_4) {
case 0:
{
x_295 = x_312;
x_296 = x_313;
x_297 = x_314;
x_298 = x_315;
x_299 = x_316;
x_300 = lean_box(0);
goto block_311;
}
case 1:
{
x_295 = x_312;
x_296 = x_313;
x_297 = x_314;
x_298 = x_315;
x_299 = x_316;
x_300 = lean_box(0);
goto block_311;
}
default: 
{
lean_dec(x_315);
x_236 = x_312;
x_237 = x_313;
x_238 = x_314;
x_239 = x_316;
x_240 = lean_box(0);
goto block_251;
}
}
}
block_342:
{
lean_object* x_327; 
x_327 = l_IO_FS_writeFile(x_323, x_326);
lean_dec_ref(x_326);
lean_dec_ref(x_323);
if (lean_obj_tag(x_327) == 0)
{
lean_dec_ref(x_327);
x_312 = x_320;
x_313 = x_321;
x_314 = x_322;
x_315 = x_324;
x_316 = x_325;
x_317 = lean_box(0);
goto block_318;
}
else
{
uint8_t x_328; 
lean_dec(x_324);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; uint8_t x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_329 = lean_ctor_get(x_327, 0);
x_330 = lean_io_error_to_string(x_329);
x_331 = 3;
x_332 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set_uint8(x_332, sizeof(void*)*1, x_331);
x_333 = lean_apply_2(x_325, x_332, lean_box(0));
x_334 = lean_box(0);
lean_ctor_set(x_327, 0, x_334);
return x_327;
}
else
{
lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_335 = lean_ctor_get(x_327, 0);
lean_inc(x_335);
lean_dec(x_327);
x_336 = lean_io_error_to_string(x_335);
x_337 = 3;
x_338 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*1, x_337);
x_339 = lean_apply_2(x_325, x_338, lean_box(0));
x_340 = lean_box(0);
x_341 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_341, 0, x_340);
return x_341;
}
}
}
block_356:
{
uint8_t x_350; uint8_t x_351; 
x_350 = 4;
x_351 = l_Lake_instDecidableEqInitTemplate(x_4, x_350);
if (x_351 == 0)
{
uint8_t x_352; lean_object* x_353; lean_object* x_354; 
x_352 = 1;
lean_inc(x_347);
x_353 = l_Lean_Name_toString(x_347, x_352);
lean_inc(x_347);
x_354 = l___private_Lake_CLI_Init_0__Lake_libRootFileContents(x_353, x_347);
lean_dec_ref(x_353);
x_319 = lean_box(0);
x_320 = x_343;
x_321 = x_344;
x_322 = x_345;
x_323 = x_346;
x_324 = x_347;
x_325 = x_348;
x_326 = x_354;
goto block_342;
}
else
{
lean_object* x_355; 
lean_inc(x_347);
x_355 = l___private_Lake_CLI_Init_0__Lake_mathLibRootFileContents(x_347);
x_319 = lean_box(0);
x_320 = x_343;
x_321 = x_344;
x_322 = x_345;
x_323 = x_346;
x_324 = x_347;
x_325 = x_348;
x_326 = x_355;
goto block_342;
}
}
block_397:
{
if (x_364 == 0)
{
lean_object* x_366; 
x_366 = l_IO_FS_createDirAll(x_359);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; 
lean_dec_ref(x_366);
x_367 = l___private_Lake_CLI_Init_0__Lake_basicFileContents___closed__0;
x_368 = l_IO_FS_writeFile(x_363, x_367);
lean_dec_ref(x_363);
if (lean_obj_tag(x_368) == 0)
{
lean_dec_ref(x_368);
x_343 = x_357;
x_344 = x_358;
x_345 = x_360;
x_346 = x_361;
x_347 = x_362;
x_348 = x_1;
x_349 = lean_box(0);
goto block_356;
}
else
{
uint8_t x_369; 
lean_dec(x_362);
lean_dec_ref(x_361);
lean_dec(x_360);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_369 = !lean_is_exclusive(x_368);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_370 = lean_ctor_get(x_368, 0);
x_371 = lean_io_error_to_string(x_370);
x_372 = 3;
x_373 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set_uint8(x_373, sizeof(void*)*1, x_372);
x_374 = lean_apply_2(x_1, x_373, lean_box(0));
x_375 = lean_box(0);
lean_ctor_set(x_368, 0, x_375);
return x_368;
}
else
{
lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_376 = lean_ctor_get(x_368, 0);
lean_inc(x_376);
lean_dec(x_368);
x_377 = lean_io_error_to_string(x_376);
x_378 = 3;
x_379 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set_uint8(x_379, sizeof(void*)*1, x_378);
x_380 = lean_apply_2(x_1, x_379, lean_box(0));
x_381 = lean_box(0);
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_381);
return x_382;
}
}
}
else
{
uint8_t x_383; 
lean_dec_ref(x_363);
lean_dec(x_362);
lean_dec_ref(x_361);
lean_dec(x_360);
lean_dec_ref(x_358);
lean_dec_ref(x_357);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_383 = !lean_is_exclusive(x_366);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_384 = lean_ctor_get(x_366, 0);
x_385 = lean_io_error_to_string(x_384);
x_386 = 3;
x_387 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set_uint8(x_387, sizeof(void*)*1, x_386);
x_388 = lean_apply_2(x_1, x_387, lean_box(0));
x_389 = lean_box(0);
lean_ctor_set(x_366, 0, x_389);
return x_366;
}
else
{
lean_object* x_390; lean_object* x_391; uint8_t x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_390 = lean_ctor_get(x_366, 0);
lean_inc(x_390);
lean_dec(x_366);
x_391 = lean_io_error_to_string(x_390);
x_392 = 3;
x_393 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_393, 0, x_391);
lean_ctor_set_uint8(x_393, sizeof(void*)*1, x_392);
x_394 = lean_apply_2(x_1, x_393, lean_box(0));
x_395 = lean_box(0);
x_396 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_396, 0, x_395);
return x_396;
}
}
}
else
{
lean_dec_ref(x_363);
lean_dec_ref(x_359);
x_343 = x_357;
x_344 = x_358;
x_345 = x_360;
x_346 = x_361;
x_347 = x_362;
x_348 = x_1;
x_349 = lean_box(0);
goto block_356;
}
}
block_436:
{
lean_object* x_407; lean_object* x_408; 
lean_inc(x_406);
lean_inc(x_405);
lean_inc(x_3);
x_407 = l___private_Lake_CLI_Init_0__Lake_InitTemplate_configFileContents(x_4, x_5, x_3, x_405, x_406);
x_408 = l_IO_FS_writeFile(x_400, x_407);
lean_dec_ref(x_407);
lean_dec_ref(x_400);
if (lean_obj_tag(x_408) == 0)
{
lean_dec_ref(x_408);
if (lean_obj_tag(x_404) == 1)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; lean_object* x_415; uint8_t x_416; 
x_409 = lean_ctor_get(x_404, 0);
lean_inc(x_409);
lean_dec_ref(x_404);
x_410 = l___private_Lake_CLI_Init_0__Lake_escapeIdent___closed__1;
lean_inc(x_409);
x_411 = l_System_FilePath_withExtension(x_409, x_410);
x_412 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__19;
lean_inc_ref(x_411);
x_413 = l_Lake_joinRelative(x_411, x_412);
x_414 = l_System_FilePath_pathExists(x_413);
x_415 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_416 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_416 == 0)
{
x_357 = x_401;
x_358 = x_402;
x_359 = x_411;
x_360 = x_406;
x_361 = x_409;
x_362 = x_405;
x_363 = x_413;
x_364 = x_414;
x_365 = lean_box(0);
goto block_397;
}
else
{
uint8_t x_417; 
x_417 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_417 == 0)
{
x_357 = x_401;
x_358 = x_402;
x_359 = x_411;
x_360 = x_406;
x_361 = x_409;
x_362 = x_405;
x_363 = x_413;
x_364 = x_414;
x_365 = lean_box(0);
goto block_397;
}
else
{
lean_object* x_418; size_t x_419; size_t x_420; lean_object* x_421; 
x_418 = lean_box(0);
x_419 = 0;
x_420 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_421 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_415, x_419, x_420, x_418, x_1);
lean_dec_ref(x_421);
x_357 = x_401;
x_358 = x_402;
x_359 = x_411;
x_360 = x_406;
x_361 = x_409;
x_362 = x_405;
x_363 = x_413;
x_364 = x_414;
x_365 = lean_box(0);
goto block_397;
}
}
}
else
{
lean_dec(x_404);
x_312 = x_401;
x_313 = x_402;
x_314 = x_406;
x_315 = x_405;
x_316 = x_1;
x_317 = lean_box(0);
goto block_318;
}
}
else
{
uint8_t x_422; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec_ref(x_402);
lean_dec_ref(x_401);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_422 = !lean_is_exclusive(x_408);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_423 = lean_ctor_get(x_408, 0);
x_424 = lean_io_error_to_string(x_423);
x_425 = 3;
x_426 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set_uint8(x_426, sizeof(void*)*1, x_425);
x_427 = lean_apply_2(x_1, x_426, lean_box(0));
x_428 = lean_box(0);
lean_ctor_set(x_408, 0, x_428);
return x_408;
}
else
{
lean_object* x_429; lean_object* x_430; uint8_t x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_429 = lean_ctor_get(x_408, 0);
lean_inc(x_429);
lean_dec(x_408);
x_430 = lean_io_error_to_string(x_429);
x_431 = 3;
x_432 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*1, x_431);
x_433 = lean_apply_2(x_1, x_432, lean_box(0));
x_434 = lean_box(0);
x_435 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
}
}
block_446:
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_6, 1);
x_441 = lean_ctor_get(x_6, 15);
lean_inc_ref(x_441);
x_442 = l_Lake_ToolchainVer_ofString(x_441);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; 
x_443 = lean_ctor_get(x_442, 1);
lean_inc_ref(x_443);
lean_dec_ref(x_442);
x_444 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_444, 0, x_443);
lean_inc_ref(x_441);
lean_inc_ref(x_440);
x_401 = x_440;
x_402 = x_441;
x_403 = lean_box(0);
x_404 = x_438;
x_405 = x_437;
x_406 = x_444;
goto block_436;
}
else
{
lean_object* x_445; 
lean_dec_ref(x_442);
x_445 = lean_box(0);
lean_inc_ref(x_441);
lean_inc_ref(x_440);
x_401 = x_440;
x_402 = x_441;
x_403 = lean_box(0);
x_404 = x_438;
x_405 = x_437;
x_406 = x_445;
goto block_436;
}
}
block_453:
{
if (x_449 == 0)
{
lean_object* x_451; 
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_447);
x_437 = x_448;
x_438 = x_451;
x_439 = lean_box(0);
goto block_446;
}
else
{
lean_object* x_452; 
lean_dec_ref(x_447);
x_452 = lean_box(0);
x_437 = x_448;
x_438 = x_452;
x_439 = lean_box(0);
goto block_446;
}
}
block_469:
{
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; uint8_t x_460; lean_object* x_461; uint8_t x_462; 
lean_dec_ref(x_454);
x_458 = l_Lake_toUpperCamelCase(x_3);
lean_inc(x_458);
x_459 = l_Lean_modToFilePath(x_2, x_458, x_456);
lean_dec_ref(x_456);
x_460 = l_System_FilePath_pathExists(x_459);
x_461 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_462 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_462 == 0)
{
x_447 = x_459;
x_448 = x_458;
x_449 = x_460;
x_450 = lean_box(0);
goto block_453;
}
else
{
uint8_t x_463; 
x_463 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_463 == 0)
{
x_447 = x_459;
x_448 = x_458;
x_449 = x_460;
x_450 = lean_box(0);
goto block_453;
}
else
{
lean_object* x_464; size_t x_465; size_t x_466; lean_object* x_467; 
x_464 = lean_box(0);
x_465 = 0;
x_466 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_467 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_461, x_465, x_466, x_464, x_1);
lean_dec_ref(x_467);
x_447 = x_459;
x_448 = x_458;
x_449 = x_460;
x_450 = lean_box(0);
goto block_453;
}
}
}
else
{
lean_object* x_468; 
lean_dec_ref(x_456);
x_468 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_468, 0, x_454);
lean_inc(x_3);
x_437 = x_3;
x_438 = x_468;
x_439 = lean_box(0);
goto block_446;
}
}
block_476:
{
uint8_t x_474; uint8_t x_475; 
x_474 = 1;
x_475 = l_Lake_instDecidableEqInitTemplate(x_4, x_474);
if (x_475 == 0)
{
x_454 = x_471;
x_455 = lean_box(0);
x_456 = x_470;
x_457 = x_472;
goto block_469;
}
else
{
x_454 = x_471;
x_455 = lean_box(0);
x_456 = x_470;
x_457 = x_475;
goto block_469;
}
}
block_488:
{
lean_object* x_478; lean_object* x_479; uint8_t x_480; lean_object* x_481; uint8_t x_482; 
x_478 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__20;
lean_inc(x_3);
x_479 = l_Lean_modToFilePath(x_2, x_3, x_478);
x_480 = l_System_FilePath_pathExists(x_479);
x_481 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
x_482 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__11;
if (x_482 == 0)
{
x_470 = x_478;
x_471 = x_479;
x_472 = x_480;
x_473 = lean_box(0);
goto block_476;
}
else
{
uint8_t x_483; 
x_483 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__12;
if (x_483 == 0)
{
x_470 = x_478;
x_471 = x_479;
x_472 = x_480;
x_473 = lean_box(0);
goto block_476;
}
else
{
lean_object* x_484; size_t x_485; size_t x_486; lean_object* x_487; 
x_484 = lean_box(0);
x_485 = 0;
x_486 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__13;
lean_inc_ref(x_1);
x_487 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_481, x_485, x_486, x_484, x_1);
lean_dec_ref(x_487);
x_470 = x_478;
x_471 = x_479;
x_472 = x_480;
x_473 = lean_box(0);
goto block_476;
}
}
}
block_516:
{
if (x_489 == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_unsigned_to_nat(0u);
x_492 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_2);
x_493 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow(x_2, x_4, x_492);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_494 = lean_ctor_get(x_493, 1);
lean_inc(x_494);
lean_dec_ref(x_493);
x_495 = lean_array_get_size(x_494);
x_496 = lean_nat_dec_lt(x_491, x_495);
if (x_496 == 0)
{
lean_dec(x_495);
lean_dec(x_494);
x_477 = lean_box(0);
goto block_488;
}
else
{
uint8_t x_497; 
x_497 = lean_nat_dec_le(x_495, x_495);
if (x_497 == 0)
{
lean_dec(x_495);
lean_dec(x_494);
x_477 = lean_box(0);
goto block_488;
}
else
{
lean_object* x_498; size_t x_499; size_t x_500; lean_object* x_501; 
x_498 = lean_box(0);
x_499 = 0;
x_500 = lean_usize_of_nat(x_495);
lean_dec(x_495);
lean_inc_ref(x_1);
x_501 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_494, x_499, x_500, x_498, x_1);
lean_dec(x_494);
lean_dec_ref(x_501);
x_477 = lean_box(0);
goto block_488;
}
}
}
else
{
lean_object* x_502; lean_object* x_503; uint8_t x_504; 
lean_dec_ref(x_400);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_502 = lean_ctor_get(x_493, 1);
lean_inc(x_502);
lean_dec_ref(x_493);
x_503 = lean_array_get_size(x_502);
x_504 = lean_nat_dec_lt(x_491, x_503);
if (x_504 == 0)
{
lean_object* x_505; lean_object* x_506; 
lean_dec(x_503);
lean_dec(x_502);
lean_dec_ref(x_1);
x_505 = lean_box(0);
x_506 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_506, 0, x_505);
return x_506;
}
else
{
uint8_t x_507; 
x_507 = lean_nat_dec_le(x_503, x_503);
if (x_507 == 0)
{
lean_dec(x_503);
lean_dec(x_502);
lean_dec_ref(x_1);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_508; size_t x_509; size_t x_510; lean_object* x_511; 
x_508 = lean_box(0);
x_509 = 0;
x_510 = lean_usize_of_nat(x_503);
lean_dec(x_503);
x_511 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_502, x_509, x_510, x_508, x_1);
lean_dec(x_502);
lean_dec_ref(x_511);
x_9 = lean_box(0);
goto block_12;
}
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec_ref(x_400);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_2);
x_512 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__22;
x_513 = lean_apply_2(x_1, x_512, lean_box(0));
x_514 = lean_box(0);
x_515 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_515, 0, x_514);
return x_515;
}
}
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
LEAN_EXPORT lean_object* l_Lake_init(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_33; lean_object* x_34; lean_object* x_61; uint8_t x_62; 
x_61 = l___private_Lake_CLI_Init_0__Lake_escapeName_x21___closed__4;
x_62 = lean_string_dec_eq(x_1, x_61);
if (x_62 == 0)
{
x_33 = x_1;
x_34 = lean_box(0);
goto block_60;
}
else
{
lean_object* x_63; 
lean_dec_ref(x_1);
lean_inc_ref(x_5);
x_63 = lean_io_realpath(x_5);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = l_System_FilePath_fileName(x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_67 = l_Lake_init___closed__0;
x_68 = lean_string_append(x_67, x_65);
lean_dec(x_65);
x_69 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
x_70 = lean_string_append(x_68, x_69);
x_71 = 3;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_apply_2(x_7, x_72, lean_box(0));
x_74 = lean_box(0);
lean_ctor_set_tag(x_63, 1);
lean_ctor_set(x_63, 0, x_74);
return x_63;
}
else
{
lean_object* x_75; 
lean_free_object(x_63);
lean_dec(x_65);
x_75 = lean_ctor_get(x_66, 0);
lean_inc(x_75);
lean_dec_ref(x_66);
x_33 = x_75;
x_34 = lean_box(0);
goto block_60;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_63, 0);
lean_inc(x_76);
lean_dec(x_63);
lean_inc(x_76);
x_77 = l_System_FilePath_fileName(x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_78 = l_Lake_init___closed__0;
x_79 = lean_string_append(x_78, x_76);
lean_dec(x_76);
x_80 = l___private_Lake_CLI_Init_0__Lake_createLeanActionWorkflow___closed__6;
x_81 = lean_string_append(x_79, x_80);
x_82 = 3;
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_82);
x_84 = lean_apply_2(x_7, x_83, lean_box(0));
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
else
{
lean_object* x_87; 
lean_dec(x_76);
x_87 = lean_ctor_get(x_77, 0);
lean_inc(x_87);
lean_dec_ref(x_77);
x_33 = x_87;
x_34 = lean_box(0);
goto block_60;
}
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_88 = !lean_is_exclusive(x_63);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_63, 0);
x_90 = lean_io_error_to_string(x_89);
x_91 = 3;
x_92 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*1, x_91);
x_93 = lean_apply_2(x_7, x_92, lean_box(0));
x_94 = lean_box(0);
lean_ctor_set(x_63, 0, x_94);
return x_63;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_63, 0);
lean_inc(x_95);
lean_dec(x_63);
x_96 = lean_io_error_to_string(x_95);
x_97 = 3;
x_98 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set_uint8(x_98, sizeof(void*)*1, x_97);
x_99 = lean_apply_2(x_7, x_98, lean_box(0));
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
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
x_17 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__2(x_7, x_5, x_16, x_2, x_3, x_4, x_6);
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
block_60:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_string_utf8_byte_size(x_33);
x_37 = l_Substring_takeWhileAux___at___00Lake_init_spec__0(x_33, x_36, x_35);
x_38 = l_Substring_takeRightWhileAux___at___00Lake_init_spec__1(x_33, x_37, x_36);
x_39 = lean_string_utf8_extract(x_33, x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_33);
x_40 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_39);
x_41 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_39, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_35, x_43);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
x_13 = x_39;
x_14 = lean_box(0);
goto block_32;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_43, x_43);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
x_13 = x_39;
x_14 = lean_box(0);
goto block_32;
}
else
{
lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; 
x_46 = lean_box(0);
x_47 = 0;
x_48 = lean_usize_of_nat(x_43);
lean_dec(x_43);
lean_inc_ref(x_7);
x_49 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_42, x_47, x_48, x_46, x_7);
lean_dec(x_42);
lean_dec_ref(x_49);
x_13 = x_39;
x_14 = lean_box(0);
goto block_32;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec_ref(x_39);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_dec_ref(x_41);
x_51 = lean_array_get_size(x_50);
x_52 = lean_nat_dec_lt(x_35, x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec_ref(x_7);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_51, x_51);
if (x_55 == 0)
{
lean_dec(x_51);
lean_dec(x_50);
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; 
x_56 = lean_box(0);
x_57 = 0;
x_58 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_59 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_50, x_57, x_58, x_56, x_7);
lean_dec(x_50);
lean_dec_ref(x_59);
x_9 = lean_box(0);
goto block_12;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___00Lake_init_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeWhileAux___at___00Lake_init_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Substring_takeRightWhileAux___at___00Lake_init_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Substring_takeRightWhileAux___at___00Lake_init_spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_unbox(x_4);
x_10 = lean_unbox(x_5);
x_11 = lean_unbox(x_7);
x_12 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__2(x_1, x_2, x_3, x_9, x_10, x_6, x_11);
return x_12;
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
LEAN_EXPORT lean_object* l_Lake_new(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_39; lean_object* x_40; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_string_utf8_byte_size(x_1);
x_15 = l_Substring_takeWhileAux___at___00Lake_init_spec__0(x_1, x_14, x_13);
x_16 = l_Substring_takeRightWhileAux___at___00Lake_init_spec__1(x_1, x_15, x_14);
x_17 = lean_string_utf8_extract(x_1, x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_39 = l___private_Lake_CLI_Init_0__Lake_initPkg___closed__9;
lean_inc_ref(x_17);
x_40 = l___private_Lake_CLI_Init_0__Lake_validatePkgName(x_17, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_array_get_size(x_41);
x_43 = lean_nat_dec_lt(x_13, x_42);
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
x_18 = lean_box(0);
goto block_38;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_42, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
x_18 = lean_box(0);
goto block_38;
}
else
{
lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; 
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_usize_of_nat(x_42);
lean_dec(x_42);
lean_inc_ref(x_7);
x_48 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_41, x_46, x_47, x_45, x_7);
lean_dec(x_41);
lean_dec_ref(x_48);
x_18 = lean_box(0);
goto block_38;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_dec_ref(x_17);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_dec_ref(x_40);
x_50 = lean_array_get_size(x_49);
x_51 = lean_nat_dec_lt(x_13, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_7);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_50, x_50);
if (x_54 == 0)
{
lean_dec(x_50);
lean_dec(x_49);
lean_dec_ref(x_7);
x_9 = lean_box(0);
goto block_12;
}
else
{
lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; 
x_55 = lean_box(0);
x_56 = 0;
x_57 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lake_CLI_Init_0__Lake_initPkg_spec__0(x_49, x_56, x_57, x_55, x_7);
lean_dec(x_49);
lean_dec_ref(x_58);
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
block_38:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lake_stringToLegalOrSimpleName(x_17);
lean_inc(x_19);
x_20 = l___private_Lake_CLI_Init_0__Lake_dotlessName(x_19);
x_21 = l_Lake_joinRelative(x_5, x_20);
lean_inc_ref(x_21);
x_22 = l_IO_FS_createDirAll(x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
lean_dec_ref(x_22);
x_23 = l___private_Lake_CLI_Init_0__Lake_initPkg___at___00Lake_init_spec__2(x_7, x_21, x_19, x_2, x_3, x_4, x_6);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec_ref(x_21);
lean_dec(x_19);
lean_dec_ref(x_4);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_io_error_to_string(x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_apply_2(x_7, x_28, lean_box(0));
x_30 = lean_box(0);
lean_ctor_set(x_22, 0, x_30);
return x_22;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_io_error_to_string(x_31);
x_33 = 3;
x_34 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_33);
x_35 = lean_apply_2(x_7, x_34, lean_box(0));
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
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
lean_dec_ref(x_1);
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
l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__0 = _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__0();
lean_mark_persistent(l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__0);
l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1___boxed__const__1 = _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1___boxed__const__1();
lean_mark_persistent(l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1___boxed__const__1);
l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1 = _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1();
lean_mark_persistent(l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__1);
l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2___boxed__const__1 = _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2___boxed__const__1();
lean_mark_persistent(l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2___boxed__const__1);
l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2 = _init_l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2();
lean_mark_persistent(l_String_anyAux___at___00__private_Lake_CLI_Init_0__Lake_validatePkgName_spec__0___closed__2);
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
