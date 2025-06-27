// Lean compiler output
// Module: Lake.CLI.Init
// Imports: Lake.Util.Git Lake.Util.Sugar Lake.Util.Version Lake.Config.Lang Lake.Config.Package Lake.Config.Workspace Lake.Load.Config Lake.Load.Workspace Lake.Build.Actions
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
LEAN_EXPORT lean_object* l_Lake_defaultExeRoot;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validatePkgName___closed__6;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__29;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_stdLeanConfigFileContents___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_escapeName_x21___closed__1;
lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_leanActionWorkflowContents;
LEAN_EXPORT lean_object* l_Lake_initPkg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_updateManifest(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_escapeName_x21___closed__0;
static lean_object* l_Lake_instReprInitTemplate___closed__0;
LEAN_EXPORT lean_object* l_Lake_libRootFileContents(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_createLeanActionWorkflow(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_defaultExeRoot___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_escapeName_x21___closed__3;
static lean_object* l_Lake_mathTomlConfigFileContents___closed__0;
static lean_object* l_Lake_createLeanActionWorkflow___closed__7;
static lean_object* l_Lake_mathToolchainBlobUrl___closed__0;
static size_t l_Lake_initPkg___elam__16___redArg___closed__9;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__41;
static lean_object* l_Lake_createLeanActionWorkflow___closed__4;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__16;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__3;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_mainFileName___closed__0;
static lean_object* l_Lake_mathLaxLeanConfigFileContents___closed__1;
static lean_object* l_Lake_validatePkgName___closed__8;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lake_stdTomlConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mathLaxLeanConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__19;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lake_stdTomlConfigFileContents___closed__4;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_escapeName_x21___boxed(lean_object*);
static lean_object* l_Lake_basicFileContents___closed__0;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__17;
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__13;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Lake_initPkg___closed__0;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__35;
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___boxed(lean_object**);
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__15;
static lean_object* l_Lake_init___closed__0;
LEAN_EXPORT lean_object* l_Lake_createReleaseActionWorkflowContents;
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate;
static lean_object* l_Lake_createLeanActionWorkflow___closed__16;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__4;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f___boxed(lean_object*);
static lean_object* l_Lake_validatePkgName___closed__4;
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__5;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__3;
lean_object* l_System_FilePath_pathExists(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_dotlessName___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___lam__0(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__0;
LEAN_EXPORT uint8_t l_Lake_instInhabitedInitTemplate;
LEAN_EXPORT lean_object* l_Lake_mathToolchainUrl;
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__27;
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_mathTomlConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__8;
static lean_object* l_Lake_stdTomlConfigFileContents___closed__3;
static lean_object* l_Lake_libTomlConfigFileContents___closed__0;
static lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__0;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2___boxed__const__1;
static lean_object* l_Lake_escapeName_x21___closed__4;
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validatePkgName___closed__7;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_configFileContents(uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__22;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object*, lean_object*);
static lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__24;
LEAN_EXPORT lean_object* l_Lake_gitignoreContents;
LEAN_EXPORT lean_object* l_Lake_escapeIdent___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_524_;
static lean_object* l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_524_;
static lean_object* l_Lake_mathUpdateActionWorkflowContents___closed__0;
static lean_object* l_Lake_exeTomlConfigFileContents___closed__0;
static lean_object* l_Lake_createLeanActionWorkflow___closed__3;
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dotlessName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_libTomlConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__20;
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__21;
LEAN_EXPORT lean_object* l_Lake_initPkg___at___Lake_init_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_readmeFileContents___boxed(lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
static lean_object* l_Lake_initPkg___closed__2;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__26;
static lean_object* l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
static lean_object* l_Lake_libLeanConfigFileContents___closed__0;
static lean_object* l_Lake_validatePkgName___closed__5;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__11;
static lean_object* l_Lake_mathLeanConfigFileContents___closed__0;
lean_object* l_System_FilePath_fileName(lean_object*);
lean_object* l_String_mapAux___at___Lake_envToBool_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mainFileName;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__5;
static lean_object* l_Lake_mathToolchainUrl___closed__0;
static lean_object* l_Lake_createLeanActionWorkflow___closed__15;
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_validatePkgName_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__30;
LEAN_EXPORT lean_object* l_Lake_stdLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_createLeanActionWorkflow___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_initPkg___elam__16___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lake_mathReadmeFileContents(lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__28;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__23;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__36;
LEAN_EXPORT lean_object* l_Lake_mathLaxTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_libRootFileContents___closed__0;
static lean_object* l_Lake_createLeanActionWorkflow___closed__6;
static lean_object* l_Lake_validatePkgName___closed__1;
static lean_object* l_Lake_createLeanActionWorkflow___closed__1;
static lean_object* l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_524_;
static lean_object* l_Lake_stdLeanConfigFileContents___closed__2;
LEAN_EXPORT uint8_t l_Lake_libRootFileContents___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_initPkg___closed__4;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__1;
static lean_object* l_Lake_mathLaxTomlConfigFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_initPkg___at___Lake_init_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_524_;
LEAN_EXPORT lean_object* l_Lake_mathLibRootFileContents(lean_object*);
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lake_exeLeanConfigFileContents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_escapeIdent(lean_object*);
static lean_object* l_Lake_escapeName_x21___closed__5;
static lean_object* l_Lake_initPkg___closed__1;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__34;
LEAN_EXPORT lean_object* l_Lake_basicFileContents;
static lean_object* l_Lake_mathLibRootFileContents___closed__1;
static lean_object* l_Lake_stdLeanConfigFileContents___closed__1;
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdTomlConfigFileContents___closed__1;
LEAN_EXPORT lean_object* l_Lake_libRootFileContents___lam__0___boxed(lean_object*);
static lean_object* l_Lake_escapeIdent___closed__2;
static lean_object* l_Lake_mathReadmeFileContents___closed__0;
lean_object* l_Lake_testProc(lean_object*, lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_524_;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lake_mathLaxLeanConfigFileContents(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_initPkg___lam__0(uint8_t, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__14;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__12;
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mainFileName___closed__1;
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__0;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__2;
static lean_object* l_Lake_createReleaseActionWorkflowContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_mathLeanConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_validatePkgName___closed__3;
LEAN_EXPORT lean_object* l_Lake_mathLaxTomlConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__9;
lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
static lean_object* l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_524_;
static lean_object* l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_524_;
LEAN_EXPORT lean_object* l_Lake_libLeanConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__10;
static lean_object* l_Lake_stdTomlConfigFileContents___closed__2;
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_exeLeanConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_escapeIdent___closed__1;
static lean_object* l_Lake_validatePkgName___closed__2;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_configFileContents___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_initPkg___elam__16___redArg___closed__39;
static lean_object* l_Lake_mainFileContents___closed__0;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_524_(uint8_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_stdLeanConfigFileContents___closed__0;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_initPkg___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__33;
LEAN_EXPORT lean_object* l_Lake_exeFileContents;
static lean_object* l_Lake_createLeanActionWorkflow___closed__2;
static uint8_t l_Lake_initPkg___elam__16___redArg___closed__38;
LEAN_EXPORT lean_object* l_Lake_mathLeanConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_validatePkgName___closed__0;
static lean_object* l_Lake_mathLaxTomlConfigFileContents___closed__1;
lean_object* lean_io_realpath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validatePkgName(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__14;
LEAN_EXPORT lean_object* l_Lake_stdLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__12;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__32;
LEAN_EXPORT lean_object* l_Lake_libRootFileContents___boxed(lean_object*, lean_object*);
static size_t l_Lake_initPkg___elam__16___redArg___closed__40;
static lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_stdTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___closed__3;
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mainFileContents(lean_object*);
static lean_object* l_Lake_mathLaxLeanConfigFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_524_;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_libRootFileContents___closed__1;
LEAN_EXPORT lean_object* l_Lake_mathToolchainBlobUrl;
LEAN_EXPORT lean_object* l_Lake_init(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_exeFileContents___closed__0;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__0;
lean_object* l_panic___at___System_Uri_UriEscape_decodeUri_spec__1(lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_524_;
lean_object* l_Lake_toUpperCamelCase(lean_object*);
static lean_object* l_Lake_gitignoreContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_escapeName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lake_libLeanConfigFileContents(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mathReadmeFileContents___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lake_libTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_readmeFileContents___closed__0;
lean_object* l_Lake_Env_toolchain(lean_object*);
static lean_object* l_Lake_libRootFileContents___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_readmeFileContents(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_exeTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__1;
static lean_object* l_Lake_validatePkgName___closed__9;
LEAN_EXPORT lean_object* l_Lake_mathBuildActionWorkflowContents;
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
static uint8_t l_Lake_initPkg___elam__16___redArg___closed__8;
static lean_object* l_Lake_mainFileName___closed__2;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__11;
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_exeLeanConfigFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_524_;
static lean_object* l_Lake_libLeanConfigFileContents___closed__1;
static lean_object* l_Lake_leanActionWorkflowContents___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_defaultExeRoot___closed__0;
LEAN_EXPORT lean_object* l_Lake_dotlessName___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mathUpdateActionWorkflowContents;
LEAN_EXPORT lean_object* l_Lake_exeTomlConfigFileContents___boxed(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__8;
static uint8_t l_Lake_initPkg___elam__16___redArg___closed__18;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__13;
static lean_object* l_Lake_mathBuildActionWorkflowContents___closed__0;
static lean_object* l_Lake_mathLibRootFileContents___closed__0;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__31;
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_validatePkgName_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg(uint8_t, uint8_t);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__37;
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__25;
LEAN_EXPORT lean_object* l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_524____boxed(lean_object*, lean_object*);
static lean_object* l_Lake_escapeIdent___closed__0;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__7;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__9;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx___boxed(lean_object*);
static lean_object* l_Lake_initPkg___at___Lake_init_spec__0___closed__0;
LEAN_EXPORT lean_object* l_Lake_mathTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_escapeName_x21___closed__2;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_stdTomlConfigFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx(uint8_t);
static lean_object* l_Lake_initPkg___elam__16___redArg___closed__5;
LEAN_EXPORT lean_object* l_String_mapAux___at___Lake_dotlessName_spec__0(lean_object*, lean_object*);
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
static lean_object* _init_l_Lake_gitignoreContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("/.lake\n", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_gitignoreContents() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_gitignoreContents___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_basicFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def hello := \"world\"\n", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_basicFileContents() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_basicFileContents___closed__0;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_libRootFileContents___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_libRootFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-- This module serves as the root of the `", 42, 42);
return x_1;
}
}
static lean_object* _init_l_Lake_libRootFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("` library.\n-- Import modules here that should be built as part of the library.\nimport ", 86, 86);
return x_1;
}
}
static lean_object* _init_l_Lake_libRootFileContents___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".Basic\n", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_libRootFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_3 = lean_alloc_closure((void*)(l_Lake_libRootFileContents___lam__0___boxed), 1, 0);
x_4 = l_Lake_libRootFileContents___closed__0;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Lake_libRootFileContents___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Name_toString(x_2, x_9, x_3);
x_11 = lean_string_append(x_7, x_10);
lean_dec(x_10);
x_12 = l_Lake_libRootFileContents___closed__2;
x_13 = lean_string_append(x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_libRootFileContents___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_libRootFileContents___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_libRootFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_libRootFileContents(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mathLibRootFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_libRootFileContents___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mathLibRootFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import ", 7, 7);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mathLibRootFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lake_mathLibRootFileContents___closed__0;
x_3 = l_Lake_mathLibRootFileContents___closed__1;
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Name_toString(x_1, x_5, x_2);
x_7 = lean_string_append(x_3, x_6);
lean_dec(x_6);
x_8 = l_Lake_libRootFileContents___closed__2;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lake_mainFileName___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lake_mathLibRootFileContents___closed__0;
x_2 = lean_box(1);
x_3 = l_Lake_defaultExeRoot;
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Name_toString(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_mainFileName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lean", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_mainFileName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_mainFileName___closed__1;
x_2 = l_Lake_mainFileName___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mainFileName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_mainFileName___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_mainFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\ndef main : IO Unit :=\n  IO.println s!\"Hello, {hello}!\"\n", 57, 57);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mainFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Lake_mathLibRootFileContents___closed__0;
x_3 = l_Lake_mathLibRootFileContents___closed__1;
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Name_toString(x_1, x_5, x_2);
x_7 = lean_string_append(x_3, x_6);
lean_dec(x_6);
x_8 = l_Lake_mainFileContents___closed__0;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lake_exeFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("def main : IO Unit :=\n  IO.println s!\"Hello, world!\"\n", 53, 53);
return x_1;
}
}
static lean_object* _init_l_Lake_exeFileContents() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_exeFileContents___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_stdLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import Lake\nopen Lake DSL\n\npackage ", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lake_stdLeanConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n\nlean_lib ", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lake_stdLeanConfigFileContents___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  -- add library configuration options here\n\n@[default_target]\nlean_exe ", 79, 79);
return x_1;
}
}
static lean_object* _init_l_Lake_stdLeanConfigFileContents___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  root := `Main\n", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdLeanConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_4 = l_Lake_stdLeanConfigFileContents___closed__0;
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_unsigned_to_nat(120u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec(x_9);
x_11 = l_Lake_stdLeanConfigFileContents___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = lean_string_append(x_12, x_2);
x_14 = l_Lake_stdLeanConfigFileContents___closed__2;
x_15 = lean_string_append(x_13, x_14);
x_16 = l_String_quote(x_3);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_format_pretty(x_17, x_7, x_8, x_8);
x_19 = lean_string_append(x_15, x_18);
lean_dec(x_18);
x_20 = l_Lake_stdLeanConfigFileContents___closed__3;
x_21 = lean_string_append(x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_stdLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_stdLeanConfigFileContents(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_stdTomlConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name = ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_stdTomlConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nversion = \"0.1.0\"\ndefaultTargets = [", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lake_stdTomlConfigFileContents___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]\n\n[[lean_lib]]\nname = ", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lake_stdTomlConfigFileContents___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n[[lean_exe]]\nname = ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_stdTomlConfigFileContents___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nroot = \"Main\"\n", 15, 15);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_stdTomlConfigFileContents(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_4 = l_Lake_stdTomlConfigFileContents___closed__0;
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_unsigned_to_nat(120u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_format_pretty(x_6, x_7, x_8, x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec(x_9);
x_11 = l_Lake_stdTomlConfigFileContents___closed__1;
x_12 = lean_string_append(x_10, x_11);
x_13 = l_String_quote(x_3);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_format_pretty(x_14, x_7, x_8, x_8);
x_16 = lean_string_append(x_12, x_15);
x_17 = l_Lake_stdTomlConfigFileContents___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = l_String_quote(x_2);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_format_pretty(x_20, x_7, x_8, x_8);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
x_23 = l_Lake_stdTomlConfigFileContents___closed__3;
x_24 = lean_string_append(x_22, x_23);
x_25 = lean_string_append(x_24, x_15);
lean_dec(x_15);
x_26 = l_Lake_stdTomlConfigFileContents___closed__4;
x_27 = lean_string_append(x_25, x_26);
return x_27;
}
}
LEAN_EXPORT lean_object* l_Lake_stdTomlConfigFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_stdTomlConfigFileContents(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_exeLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n\n@[default_target]\nlean_exe ", 58, 58);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_exeLeanConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = l_Lake_stdLeanConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lake_exeLeanConfigFileContents___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
lean_dec(x_14);
x_16 = l_Lake_stdLeanConfigFileContents___closed__3;
x_17 = lean_string_append(x_15, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_exeLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_exeLeanConfigFileContents(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_exeTomlConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]\n\n[[lean_exe]]\nname = ", 23, 23);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_exeTomlConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = l_Lake_stdTomlConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lake_stdTomlConfigFileContents___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
x_16 = l_Lake_exeTomlConfigFileContents___closed__0;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_14);
lean_dec(x_14);
x_19 = l_Lake_stdTomlConfigFileContents___closed__4;
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_exeTomlConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_exeTomlConfigFileContents(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_libLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n\n@[default_target]\nlean_lib ", 58, 58);
return x_1;
}
}
static lean_object* _init_l_Lake_libLeanConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  -- add library configuration options here\n", 51, 51);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_libLeanConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_Lake_stdLeanConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lake_libLeanConfigFileContents___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lake_libLeanConfigFileContents___closed__1;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_libLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_libLeanConfigFileContents(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_libTomlConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_libTomlConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = l_Lake_stdTomlConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lake_stdTomlConfigFileContents___closed__1;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
x_16 = l_Lake_stdTomlConfigFileContents___closed__2;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_14);
lean_dec(x_14);
x_19 = l_Lake_libTomlConfigFileContents___closed__0;
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_libTomlConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_libTomlConfigFileContents(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mathLaxLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n  keywords := #[\"math\"]\n  leanOptions := #[\n    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`\n  ]\n\nrequire \"leanprover-community\" / \"mathlib\"\n\n@[default_target]\nlean_lib ", 213, 207);
return x_1;
}
}
static lean_object* _init_l_Lake_mathLaxLeanConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  -- add any library configuration options here\n", 55, 55);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mathLaxLeanConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_Lake_stdLeanConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lake_mathLaxLeanConfigFileContents___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lake_mathLaxLeanConfigFileContents___closed__1;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_mathLaxLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mathLaxLeanConfigFileContents(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mathLaxTomlConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nversion = \"0.1.0\"\nkeywords = [\"math\"]\ndefaultTargets = [", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lake_mathLaxTomlConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]\n\n[leanOptions]\npp.unicode.fun = true # pretty-prints `fun a ↦ b`\n\n[[require]]\nname = \"mathlib\"\nscope = \"leanprover-community\"\n\n[[lean_lib]]\nname = ", 151, 149);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mathLaxTomlConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = l_Lake_stdTomlConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lake_mathLaxTomlConfigFileContents___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
x_16 = l_Lake_mathLaxTomlConfigFileContents___closed__1;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_14);
lean_dec(x_14);
x_19 = l_Lake_libTomlConfigFileContents___closed__0;
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_mathLaxTomlConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mathLaxTomlConfigFileContents(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mathLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n  keywords := #[\"math\"]\n  leanOptions := #[\n    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`\n    ⟨`autoImplicit, false⟩,\n    ⟨`relaxedAutoImplicit, false⟩,\n    ⟨`maxSynthPendingDepth, .ofNat 3⟩,\n    ⟨`weak.linter.mathlibStandardSet, true⟩,\n  ]\n\nrequire \"leanprover-community\" / \"mathlib\"\n\n@[default_target]\nlean_lib ", 377, 355);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mathLeanConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_3 = l_Lake_stdLeanConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lake_mathLeanConfigFileContents___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = lean_string_append(x_11, x_2);
x_13 = l_Lake_mathLaxLeanConfigFileContents___closed__1;
x_14 = lean_string_append(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lake_mathLeanConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mathLeanConfigFileContents(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mathTomlConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]\n\n[leanOptions]\npp.unicode.fun = true # pretty-prints `fun a ↦ b`\nautoImplicit = false\nrelaxedAutoImplicit = false\nweak.linter.mathlibStandardSet = true\nmaxSynthPendingDepth = 3\n\n[[require]]\nname = \"mathlib\"\nscope = \"leanprover-community\"\n\n[[lean_lib]]\nname = ", 263, 261);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mathTomlConfigFileContents(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_3 = l_Lake_stdTomlConfigFileContents___closed__0;
x_4 = l_String_quote(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_unsigned_to_nat(120u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_format_pretty(x_5, x_6, x_7, x_7);
x_9 = lean_string_append(x_3, x_8);
lean_dec(x_8);
x_10 = l_Lake_mathLaxTomlConfigFileContents___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
x_16 = l_Lake_mathTomlConfigFileContents___closed__0;
x_17 = lean_string_append(x_15, x_16);
x_18 = lean_string_append(x_17, x_14);
lean_dec(x_14);
x_19 = l_Lake_libTomlConfigFileContents___closed__0;
x_20 = lean_string_append(x_18, x_19);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_mathTomlConfigFileContents___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_mathTomlConfigFileContents(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_readmeFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("# ", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_readmeFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_readmeFileContents___closed__0;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_readmeFileContents___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_readmeFileContents(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mathReadmeFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n\n## GitHub configuration\n\nTo set up your new GitHub repository, follow these steps:\n\n* Under your repository name, click **Settings**.\n* In the **Actions** section of the sidebar, click \"General\".\n* Check the box **Allow GitHub Actions to create and approve pull requests**.\n* Click the **Pages** section of the settings sidebar.\n* In the **Source** dropdown menu, select \"GitHub Actions\".\n\nAfter following the steps above, you can remove this section from the README file.\n", 475, 475);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_mathReadmeFileContents(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_readmeFileContents___closed__0;
x_3 = lean_string_append(x_2, x_1);
x_4 = l_Lake_mathReadmeFileContents___closed__0;
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_mathReadmeFileContents___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_mathReadmeFileContents(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_mathToolchainBlobUrl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain", 85, 85);
return x_1;
}
}
static lean_object* _init_l_Lake_mathToolchainBlobUrl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_mathToolchainBlobUrl___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_mathToolchainUrl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("https://github.com/leanprover-community/mathlib4/blob/master/lean-toolchain", 75, 75);
return x_1;
}
}
static lean_object* _init_l_Lake_mathToolchainUrl() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_mathToolchainUrl___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_leanActionWorkflowContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v4\n      - uses: leanprover/lean-action@v1\n", 200, 200);
return x_1;
}
}
static lean_object* _init_l_Lake_leanActionWorkflowContents() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_leanActionWorkflowContents___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_mathBuildActionWorkflowContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: Lean Action CI\n\non:\n  push:\n  pull_request:\n  workflow_dispatch:\n\n# Sets permissions of the GITHUB_TOKEN to allow deployment to GitHub Pages\npermissions:\n  contents: read # Read access to repository contents\n  pages: write # Write access to GitHub Pages\n  id-token: write # Write access to ID tokens\n\njobs:\n  build:\n    runs-on: ubuntu-latest\n\n    steps:\n      - uses: actions/checkout@v4\n      - uses: leanprover/lean-action@v1\n      - uses: leanprover-community/docgen-action@v1\n", 487, 487);
return x_1;
}
}
static lean_object* _init_l_Lake_mathBuildActionWorkflowContents() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_mathBuildActionWorkflowContents___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_mathUpdateActionWorkflowContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: Update Dependencies\n\non:\n  # schedule:             # Sets a schedule to trigger the workflow\n  #   - cron: \"0 8 * * *\" # Every day at 08:00 AM UTC (see https://docs.github.com/en/actions/writing-workflows/choosing-when-your-workflow-runs/events-that-trigger-workflows#schedule)\n  workflow_dispatch:    # Allows the workflow to be triggered manually via the GitHub interface\n\njobs:\n  check-for-updates: # Determines which updates to apply.\n    runs-on: ubuntu-latest\n    outputs:\n      is-update-available: ${{ steps.check-for-updates.outputs.is-update-available }}\n      new-tags: ${{ steps.check-for-updates.outputs.new-tags }}\n    steps:\n      - name: Run the action\n        id: check-for-updates\n        uses: leanprover-community/mathlib-update-action@v1\n        # START CONFIGURATION BLOCK 1\n        # END CONFIGURATION BLOCK 1\n  do-update: # Runs the upgrade, tests it, and makes a PR/issue/commit.\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write      # Grants permission to push changes to the repository\n      issues: write        # Grants permission to create or update issues\n      pull-requests: write # Grants permission to create or update pull requests\n    needs: check-for-updates\n    if: ${{ needs.check-for-updates.outputs.is-update-available }}\n    strategy: # Runs for each update discovered by the `check-for-updates` job.\n      max-parallel: 1 # Ensures that the PRs/issues are created in order.\n      matrix:\n        tag: ${{ fromJSON(needs.check-for-updates.outputs.new-tags) }}\n    steps:\n      - name: Run the action\n        id: update-the-repo\n        uses: leanprover-community/mathlib-update-action/do-update@v1\n        with:\n          tag: ${{ matrix.tag }}\n          # START CONFIGURATION BLOCK 2\n          on_update_succeeds: pr # Create a pull request if the update succeeds\n          on_update_fails: issue # Create an issue if the update fails\n          # END CONFIGURATION BLOCK 2\n", 1940, 1940);
return x_1;
}
}
static lean_object* _init_l_Lake_mathUpdateActionWorkflowContents() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_mathUpdateActionWorkflowContents___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_createReleaseActionWorkflowContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("name: Create Release\n\non:\n  push:\n    branches:\n      - 'main'\n      - 'master'\n    paths:\n      - 'lean-toolchain'\n\njobs:\n  lean-release-tag:\n    name: Add Lean release tag\n    runs-on: ubuntu-latest\n    permissions:\n      contents: write\n    steps:\n    - name: lean-release-tag action\n      uses: leanprover-community/lean-release-tag@v1\n      with:\n        do-release: true\n        GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}\n", 427, 427);
return x_1;
}
}
static lean_object* _init_l_Lake_createReleaseActionWorkflowContents() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_createReleaseActionWorkflowContents___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_InitTemplate_toCtorIdx(x_2);
return x_3;
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
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_InitTemplate_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
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
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_InitTemplate_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lake_InitTemplate_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.std", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_524_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.exe", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_524_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.lib", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_524_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.mathLax", 25, 25);
return x_1;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_524_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.math", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_524_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_524_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; lean_object* x_19; lean_object* x_27; lean_object* x_35; 
switch (x_1) {
case 0:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_43, x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_3 = x_45;
goto block_10;
}
else
{
lean_object* x_46; 
x_46 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
x_3 = x_46;
goto block_10;
}
}
case 1:
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(1024u);
x_48 = lean_nat_dec_le(x_47, x_2);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_11 = x_49;
goto block_18;
}
else
{
lean_object* x_50; 
x_50 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
x_11 = x_50;
goto block_18;
}
}
case 2:
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_unsigned_to_nat(1024u);
x_52 = lean_nat_dec_le(x_51, x_2);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_19 = x_53;
goto block_26;
}
else
{
lean_object* x_54; 
x_54 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
x_19 = x_54;
goto block_26;
}
}
case 3:
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_unsigned_to_nat(1024u);
x_56 = lean_nat_dec_le(x_55, x_2);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_27 = x_57;
goto block_34;
}
else
{
lean_object* x_58; 
x_58 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
x_27 = x_58;
goto block_34;
}
}
default: 
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_unsigned_to_nat(1024u);
x_60 = lean_nat_dec_le(x_59, x_2);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_35 = x_61;
goto block_42;
}
else
{
lean_object* x_62; 
x_62 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
x_35 = x_62;
goto block_42;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_524_;
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_8);
x_9 = l_Repr_addAppParen(x_7, x_2);
return x_9;
}
block_18:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_12 = l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_524_;
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_524_;
x_21 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = l_Repr_addAppParen(x_23, x_2);
return x_25;
}
block_34:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_524_;
x_29 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*1, x_32);
x_33 = l_Repr_addAppParen(x_31, x_2);
return x_33;
}
block_42:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_36 = l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_524_;
x_37 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_unbox(x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*1, x_40);
x_41 = l_Repr_addAppParen(x_39, x_2);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_524____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_524_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_524____boxed), 2, 0);
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
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_dec_le(x_10, x_1);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(2);
x_13 = lean_unbox(x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_1, x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(4);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(3);
x_18 = lean_unbox(x_17);
return x_18;
}
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
x_3 = l_Lake_InitTemplate_toCtorIdx(x_1);
x_4 = l_Lake_InitTemplate_toCtorIdx(x_2);
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
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instDecidableEqInitTemplate(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint8_t _init_l_Lake_instInhabitedInitTemplate() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(4);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(3);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(2);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
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
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_escapeIdent___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_escapeIdent___closed__1() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 171;
x_2 = l_Lake_escapeIdent___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_escapeIdent___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 187;
x_2 = l_Lake_escapeIdent___closed__0;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_escapeIdent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lake_escapeIdent___closed__1;
x_3 = lean_string_append(x_2, x_1);
x_4 = l_Lake_escapeIdent___closed__2;
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_escapeIdent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_escapeIdent(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_escapeName_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CLI.Init", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_escapeName_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.escapeName!", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_escapeName_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lake_escapeName_x21___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_escapeName_x21___closed__2;
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_unsigned_to_nat(358u);
x_4 = l_Lake_escapeName_x21___closed__1;
x_5 = l_Lake_escapeName_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_escapeName_x21___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_escapeName_x21___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_escapeName_x21___closed__2;
x_2 = lean_unsigned_to_nat(23u);
x_3 = lean_unsigned_to_nat(361u);
x_4 = l_Lake_escapeName_x21___closed__1;
x_5 = l_Lake_escapeName_x21___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_escapeName_x21(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_escapeName_x21___closed__3;
x_3 = l_panic___at___System_Uri_UriEscape_decodeUri_spec__1(x_2);
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
x_6 = l_Lake_escapeIdent(x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = l_Lake_escapeName_x21(x_4);
x_9 = l_Lake_escapeName_x21___closed__4;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lake_escapeIdent(x_7);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
return x_12;
}
}
default: 
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lake_escapeName_x21___closed__5;
x_14 = l_panic___at___System_Uri_UriEscape_decodeUri_spec__1(x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_escapeName_x21___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_escapeName_x21(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___Lake_dotlessName_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_2, x_1);
if (x_8 == 0)
{
uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_string_utf8_get(x_2, x_1);
x_10 = 46;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
x_3 = x_9;
goto block_7;
}
else
{
uint32_t x_12; 
x_12 = 45;
x_3 = x_12;
goto block_7;
}
}
else
{
lean_dec(x_1);
return x_2;
}
block_7:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_set(x_2, x_1, x_3);
x_5 = lean_string_utf8_next(x_4, x_1);
lean_dec(x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Lake_dotlessName___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_dotlessName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_box(0);
x_3 = lean_alloc_closure((void*)(l_Lake_dotlessName___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Name_toString(x_1, x_4, x_3);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_String_mapAux___at___Lake_dotlessName_spec__0(x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_dotlessName___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_dotlessName___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_configFileContents(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_dotlessName(x_3);
switch (x_1) {
case 0:
{
if (x_2 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_8 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_7, x_5);
x_9 = l_Lake_stdLeanConfigFileContents(x_5, x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lake_mathLibRootFileContents___closed__0;
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Name_toString(x_4, x_12, x_10);
x_14 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_15 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_14, x_5);
x_16 = l_Lake_stdTomlConfigFileContents(x_5, x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_5);
return x_16;
}
}
case 1:
{
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_18 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_17, x_5);
x_19 = l_Lake_exeLeanConfigFileContents(x_5, x_18);
lean_dec(x_18);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_21 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_20, x_5);
x_22 = l_Lake_exeTomlConfigFileContents(x_5, x_21);
lean_dec(x_21);
lean_dec(x_5);
return x_22;
}
}
case 2:
{
if (x_2 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_24 = l_Lake_libLeanConfigFileContents(x_5, x_23);
lean_dec(x_23);
lean_dec(x_5);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = l_Lake_mathLibRootFileContents___closed__0;
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Name_toString(x_4, x_27, x_25);
x_29 = l_Lake_libTomlConfigFileContents(x_5, x_28);
lean_dec(x_28);
lean_dec(x_5);
return x_29;
}
}
case 3:
{
if (x_2 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_31 = l_Lake_mathLaxLeanConfigFileContents(x_5, x_30);
lean_dec(x_30);
lean_dec(x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lake_mathLibRootFileContents___closed__0;
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_Name_toString(x_4, x_34, x_32);
x_36 = l_Lake_mathLaxTomlConfigFileContents(x_5, x_35);
lean_dec(x_35);
lean_dec(x_5);
return x_36;
}
}
default: 
{
if (x_2 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_38 = l_Lake_mathLeanConfigFileContents(x_5, x_37);
lean_dec(x_37);
lean_dec(x_5);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_39 = l_Lake_mathLibRootFileContents___closed__0;
x_40 = lean_box(1);
x_41 = lean_unbox(x_40);
x_42 = l_Lean_Name_toString(x_4, x_41, x_39);
x_43 = l_Lake_mathTomlConfigFileContents(x_5, x_42);
lean_dec(x_42);
lean_dec(x_5);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_InitTemplate_configFileContents___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lake_InitTemplate_configFileContents(x_5, x_6, x_3, x_4);
return x_7;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("creating lean-action CI workflow", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_createLeanActionWorkflow___closed__0;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".github", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("workflows", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_action_ci.yml", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("created lean-action CI workflow at '", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("update.yml", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("create-release.yml", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("created Mathlib update CI workflow at '", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("created create-release CI workflow at '", 39, 39);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("create-release CI workflow already exists", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_createLeanActionWorkflow___closed__11;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Mathlib update CI workflow already exists", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_createLeanActionWorkflow___closed__13;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean-action CI workflow already exists", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_createLeanActionWorkflow___closed__15;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_createLeanActionWorkflow(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_box(0);
x_6 = l_Lake_createLeanActionWorkflow___closed__1;
x_7 = lean_array_push(x_3, x_6);
x_8 = l_Lake_createLeanActionWorkflow___closed__2;
x_9 = l_Lake_joinRelative(x_1, x_8);
x_10 = l_Lake_createLeanActionWorkflow___closed__3;
x_11 = l_Lake_joinRelative(x_9, x_10);
x_12 = l_IO_FS_createDirAll(x_11, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_14 = x_12;
} else {
 lean_dec_ref(x_12);
 x_14 = lean_box(0);
}
x_15 = l_Lake_createLeanActionWorkflow___closed__4;
lean_inc(x_11);
x_16 = l_Lake_joinRelative(x_11, x_15);
x_169 = l_System_FilePath_pathExists(x_16, x_13);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_unbox(x_170);
lean_dec(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; uint8_t x_174; uint8_t x_175; 
x_172 = lean_ctor_get(x_169, 1);
lean_inc(x_172);
lean_dec(x_169);
x_173 = lean_box(4);
x_174 = lean_unbox(x_173);
x_175 = l_Lake_instDecidableEqInitTemplate(x_2, x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = l_Lake_leanActionWorkflowContents___closed__0;
x_177 = l_IO_FS_writeFile(x_16, x_176, x_172);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_17 = x_7;
x_18 = x_178;
goto block_168;
}
else
{
uint8_t x_179; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
x_179 = !lean_is_exclusive(x_177);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_180 = lean_ctor_get(x_177, 0);
x_181 = lean_io_error_to_string(x_180);
x_182 = lean_box(3);
x_183 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_183, 0, x_181);
x_184 = lean_unbox(x_182);
lean_ctor_set_uint8(x_183, sizeof(void*)*1, x_184);
x_185 = lean_array_get_size(x_7);
x_186 = lean_array_push(x_7, x_183);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
lean_ctor_set_tag(x_177, 0);
lean_ctor_set(x_177, 0, x_187);
return x_177;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_188 = lean_ctor_get(x_177, 0);
x_189 = lean_ctor_get(x_177, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_177);
x_190 = lean_io_error_to_string(x_188);
x_191 = lean_box(3);
x_192 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_192, 0, x_190);
x_193 = lean_unbox(x_191);
lean_ctor_set_uint8(x_192, sizeof(void*)*1, x_193);
x_194 = lean_array_get_size(x_7);
x_195 = lean_array_push(x_7, x_192);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_189);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Lake_mathBuildActionWorkflowContents___closed__0;
x_199 = l_IO_FS_writeFile(x_16, x_198, x_172);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_17 = x_7;
x_18 = x_200;
goto block_168;
}
else
{
uint8_t x_201; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
x_201 = !lean_is_exclusive(x_199);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_199, 0);
x_203 = lean_io_error_to_string(x_202);
x_204 = lean_box(3);
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
x_206 = lean_unbox(x_204);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_206);
x_207 = lean_array_get_size(x_7);
x_208 = lean_array_push(x_7, x_205);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set_tag(x_199, 0);
lean_ctor_set(x_199, 0, x_209);
return x_199;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_210 = lean_ctor_get(x_199, 0);
x_211 = lean_ctor_get(x_199, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_199);
x_212 = lean_io_error_to_string(x_210);
x_213 = lean_box(3);
x_214 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_214, 0, x_212);
x_215 = lean_unbox(x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_215);
x_216 = lean_array_get_size(x_7);
x_217 = lean_array_push(x_7, x_214);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_211);
return x_219;
}
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
x_220 = !lean_is_exclusive(x_169);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_169, 0);
lean_dec(x_221);
x_222 = l_Lake_createLeanActionWorkflow___closed__16;
x_223 = lean_array_push(x_7, x_222);
x_224 = lean_box(0);
x_225 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_223);
lean_ctor_set(x_169, 0, x_225);
return x_169;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_226 = lean_ctor_get(x_169, 1);
lean_inc(x_226);
lean_dec(x_169);
x_227 = l_Lake_createLeanActionWorkflow___closed__16;
x_228 = lean_array_push(x_7, x_227);
x_229 = lean_box(0);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_228);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_226);
return x_231;
}
}
block_168:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_19 = l_Lake_createLeanActionWorkflow___closed__5;
x_20 = lean_string_append(x_19, x_16);
lean_dec(x_16);
x_21 = l_Lake_createLeanActionWorkflow___closed__6;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_unbox(x_5);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
x_25 = lean_array_push(x_17, x_23);
x_26 = lean_box(4);
x_27 = lean_unbox(x_26);
x_28 = l_Lake_instDecidableEqInitTemplate(x_2, x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_25);
if (lean_is_scalar(x_14)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_14;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_18);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_14);
x_32 = l_Lake_createLeanActionWorkflow___closed__7;
lean_inc(x_11);
x_33 = l_Lake_joinRelative(x_11, x_32);
x_34 = l_System_FilePath_pathExists(x_33, x_18);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lake_mathUpdateActionWorkflowContents___closed__0;
x_39 = l_IO_FS_writeFile(x_33, x_38, x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lake_createLeanActionWorkflow___closed__8;
x_42 = l_Lake_joinRelative(x_11, x_41);
x_43 = l_System_FilePath_pathExists(x_42, x_40);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; uint8_t x_53; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = l_Lake_createLeanActionWorkflow___closed__9;
x_48 = lean_string_append(x_47, x_33);
lean_dec(x_33);
x_49 = lean_string_append(x_48, x_21);
x_50 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_unbox(x_5);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_51);
x_52 = lean_array_push(x_25, x_50);
x_53 = lean_unbox(x_45);
lean_dec(x_45);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_free_object(x_43);
x_54 = l_Lake_createReleaseActionWorkflowContents___closed__0;
x_55 = l_IO_FS_writeFile(x_42, x_54, x_46);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = l_Lake_createLeanActionWorkflow___closed__10;
x_59 = lean_string_append(x_58, x_42);
lean_dec(x_42);
x_60 = lean_string_append(x_59, x_21);
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_unbox(x_5);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_62);
x_63 = lean_box(0);
x_64 = lean_array_push(x_52, x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_55, 0, x_65);
return x_55;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
lean_dec(x_55);
x_67 = l_Lake_createLeanActionWorkflow___closed__10;
x_68 = lean_string_append(x_67, x_42);
lean_dec(x_42);
x_69 = lean_string_append(x_68, x_21);
x_70 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_unbox(x_5);
lean_ctor_set_uint8(x_70, sizeof(void*)*1, x_71);
x_72 = lean_box(0);
x_73 = lean_array_push(x_52, x_70);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_66);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_dec(x_42);
x_76 = !lean_is_exclusive(x_55);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_77 = lean_ctor_get(x_55, 0);
x_78 = lean_io_error_to_string(x_77);
x_79 = lean_box(3);
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_78);
x_81 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_81);
x_82 = lean_array_get_size(x_52);
x_83 = lean_array_push(x_52, x_80);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set_tag(x_55, 0);
lean_ctor_set(x_55, 0, x_84);
return x_55;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_85 = lean_ctor_get(x_55, 0);
x_86 = lean_ctor_get(x_55, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_55);
x_87 = lean_io_error_to_string(x_85);
x_88 = lean_box(3);
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_90);
x_91 = lean_array_get_size(x_52);
x_92 = lean_array_push(x_52, x_89);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_86);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_42);
x_95 = l_Lake_createLeanActionWorkflow___closed__12;
x_96 = lean_array_push(x_52, x_95);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_96);
lean_ctor_set(x_43, 0, x_98);
return x_43;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; uint8_t x_107; 
x_99 = lean_ctor_get(x_43, 0);
x_100 = lean_ctor_get(x_43, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_43);
x_101 = l_Lake_createLeanActionWorkflow___closed__9;
x_102 = lean_string_append(x_101, x_33);
lean_dec(x_33);
x_103 = lean_string_append(x_102, x_21);
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_unbox(x_5);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_105);
x_106 = lean_array_push(x_25, x_104);
x_107 = lean_unbox(x_99);
lean_dec(x_99);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lake_createReleaseActionWorkflowContents___closed__0;
x_109 = l_IO_FS_writeFile(x_42, x_108, x_100);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_111 = x_109;
} else {
 lean_dec_ref(x_109);
 x_111 = lean_box(0);
}
x_112 = l_Lake_createLeanActionWorkflow___closed__10;
x_113 = lean_string_append(x_112, x_42);
lean_dec(x_42);
x_114 = lean_string_append(x_113, x_21);
x_115 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_unbox(x_5);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_116);
x_117 = lean_box(0);
x_118 = lean_array_push(x_106, x_115);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
if (lean_is_scalar(x_111)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_111;
}
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_110);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_42);
x_121 = lean_ctor_get(x_109, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_109, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_123 = x_109;
} else {
 lean_dec_ref(x_109);
 x_123 = lean_box(0);
}
x_124 = lean_io_error_to_string(x_121);
x_125 = lean_box(3);
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
x_127 = lean_unbox(x_125);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_127);
x_128 = lean_array_get_size(x_106);
x_129 = lean_array_push(x_106, x_126);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
if (lean_is_scalar(x_123)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_123;
 lean_ctor_set_tag(x_131, 0);
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_122);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_42);
x_132 = l_Lake_createLeanActionWorkflow___closed__12;
x_133 = lean_array_push(x_106, x_132);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_100);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_33);
lean_dec(x_11);
x_137 = !lean_is_exclusive(x_39);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = lean_ctor_get(x_39, 0);
x_139 = lean_io_error_to_string(x_138);
x_140 = lean_box(3);
x_141 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_141, 0, x_139);
x_142 = lean_unbox(x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*1, x_142);
x_143 = lean_array_get_size(x_25);
x_144 = lean_array_push(x_25, x_141);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set_tag(x_39, 0);
lean_ctor_set(x_39, 0, x_145);
return x_39;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_146 = lean_ctor_get(x_39, 0);
x_147 = lean_ctor_get(x_39, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_39);
x_148 = lean_io_error_to_string(x_146);
x_149 = lean_box(3);
x_150 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_150, 0, x_148);
x_151 = lean_unbox(x_149);
lean_ctor_set_uint8(x_150, sizeof(void*)*1, x_151);
x_152 = lean_array_get_size(x_25);
x_153 = lean_array_push(x_25, x_150);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_147);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_33);
lean_dec(x_11);
x_156 = !lean_is_exclusive(x_34);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_157 = lean_ctor_get(x_34, 0);
lean_dec(x_157);
x_158 = l_Lake_createLeanActionWorkflow___closed__14;
x_159 = lean_array_push(x_25, x_158);
x_160 = lean_box(0);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_159);
lean_ctor_set(x_34, 0, x_161);
return x_34;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_162 = lean_ctor_get(x_34, 1);
lean_inc(x_162);
lean_dec(x_34);
x_163 = l_Lake_createLeanActionWorkflow___closed__14;
x_164 = lean_array_push(x_25, x_163);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_162);
return x_167;
}
}
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_11);
x_232 = !lean_is_exclusive(x_12);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_233 = lean_ctor_get(x_12, 0);
x_234 = lean_io_error_to_string(x_233);
x_235 = lean_box(3);
x_236 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_236, 0, x_234);
x_237 = lean_unbox(x_235);
lean_ctor_set_uint8(x_236, sizeof(void*)*1, x_237);
x_238 = lean_array_get_size(x_7);
x_239 = lean_array_push(x_7, x_236);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_240);
return x_12;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_241 = lean_ctor_get(x_12, 0);
x_242 = lean_ctor_get(x_12, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_12);
x_243 = lean_io_error_to_string(x_241);
x_244 = lean_box(3);
x_245 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_245, 0, x_243);
x_246 = lean_unbox(x_244);
lean_ctor_set_uint8(x_245, sizeof(void*)*1, x_246);
x_247 = lean_array_get_size(x_7);
x_248 = lean_array_push(x_7, x_245);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_242);
return x_250;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_createLeanActionWorkflow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_createLeanActionWorkflow(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_2, x_1, x_3);
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
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_initPkg___elam__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not create a `lean-toolchain` file for the new package; no known toolchain name for the current Elan/Lean/Lake", 116, 116);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__1;
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to download mathlib 'lean-toolchain' file; you can manually copy it from:\n  {mathToolchainUrl}", 101, 101);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__3;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_initPkg___elam__16___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__6;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Lake_initPkg___elam__16___redArg___closed__8() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__6;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lake_initPkg___elam__16___redArg___closed__9() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__6;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("downloading mathlib `lean-toolchain` file", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__10;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".gitignore", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean-toolchain", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to initialize git repository", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__15;
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("master", 6, 6);
return x_1;
}
}
static uint8_t _init_l_Lake_initPkg___elam__16___redArg___closed__18() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__17;
x_2 = lean_string_dec_eq(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkout", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-B", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__19;
x_2 = l_Lake_initPkg___elam__16___redArg___closed__21;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__20;
x_2 = l_Lake_initPkg___elam__16___redArg___closed__22;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__17;
x_2 = l_Lake_initPkg___elam__16___redArg___closed__23;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(0, 0, 3);
x_3 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 0, x_3);
x_4 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 1, x_4);
x_5 = lean_unbox(x_1);
lean_ctor_set_uint8(x_2, 2, x_5);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-q", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__27;
x_2 = l_Lake_initPkg___elam__16___redArg___closed__29;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__28;
x_2 = l_Lake_initPkg___elam__16___redArg___closed__30;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev-parse", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--is-inside-work-tree", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__32;
x_2 = l_Lake_initPkg___elam__16___redArg___closed__29;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__33;
x_2 = l_Lake_initPkg___elam__16___redArg___closed__34;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__36;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_initPkg___elam__16___redArg___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__37;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_lt(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l_Lake_initPkg___elam__16___redArg___closed__39() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__37;
x_2 = lean_nat_dec_le(x_1, x_1);
return x_2;
}
}
static size_t _init_l_Lake_initPkg___elam__16___redArg___closed__40() {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__37;
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___elam__16___redArg___closed__41() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("README.md", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_36; lean_object* x_37; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_62; lean_object* x_63; lean_object* x_66; lean_object* x_67; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_145; lean_object* x_146; lean_object* x_192; lean_object* x_193; lean_object* x_198; lean_object* x_199; uint8_t x_203; lean_object* x_204; lean_object* x_205; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_282; lean_object* x_283; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_338; lean_object* x_339; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_413; 
x_413 = lean_box(x_5);
switch (lean_obj_tag(x_413)) {
case 0:
{
goto block_412;
}
case 1:
{
goto block_412;
}
default: 
{
lean_dec(x_413);
lean_dec(x_17);
lean_dec(x_16);
x_338 = x_18;
x_339 = x_19;
goto block_356;
}
}
block_35:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_box(0);
x_26 = l_Lake_escapeName_x21___closed__4;
lean_inc(x_1);
x_27 = l_Lake_joinRelative(x_1, x_26);
lean_inc(x_27);
x_28 = l_Lake_joinRelative(x_27, x_2);
x_29 = l_Lake_initPkg___elam__16___redArg___closed__0;
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = l_Lake_escapeIdent___closed__0;
x_33 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_33, 0, x_3);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_1);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_2);
lean_ctor_set(x_33, 6, x_28);
lean_ctor_set(x_33, 7, x_29);
lean_ctor_set(x_33, 8, x_30);
lean_ctor_set(x_33, 9, x_31);
lean_ctor_set(x_33, 10, x_32);
lean_ctor_set(x_33, 11, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*12, x_4);
lean_ctor_set_uint8(x_33, sizeof(void*)*12 + 1, x_4);
lean_ctor_set_uint8(x_33, sizeof(void*)*12 + 2, x_22);
x_34 = l_Lake_updateManifest(x_33, x_30, x_20, x_21);
return x_34;
}
}
block_44:
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; 
x_38 = lean_box(3);
x_39 = lean_unbox(x_38);
x_40 = l_Lake_instDecidableEqInitTemplate(x_5, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_41 = lean_box(4);
x_42 = lean_unbox(x_41);
x_43 = l_Lake_instDecidableEqInitTemplate(x_5, x_42);
x_20 = x_36;
x_21 = x_37;
x_22 = x_43;
goto block_35;
}
else
{
x_20 = x_36;
x_21 = x_37;
x_22 = x_40;
goto block_35;
}
}
block_51:
{
if (x_46 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = l_Lake_initPkg___elam__16___redArg___closed__2;
lean_inc(x_45);
x_49 = lean_apply_2(x_45, x_48, x_47);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_36 = x_45;
x_37 = x_50;
goto block_44;
}
else
{
x_36 = x_45;
x_37 = x_47;
goto block_44;
}
}
block_61:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Lake_initPkg___elam__16___redArg___closed__4;
x_56 = lean_apply_2(x_52, x_55, x_54);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_53);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
block_65:
{
lean_object* x_64; 
x_64 = lean_box(0);
x_52 = x_62;
x_53 = x_64;
x_54 = x_63;
goto block_61;
}
block_71:
{
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_36 = x_66;
x_37 = x_68;
goto block_44;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_52 = x_66;
x_53 = x_69;
x_54 = x_70;
goto block_61;
}
}
block_144:
{
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_8);
lean_dec(x_7);
x_76 = l_Lake_Env_toolchain(x_3);
x_77 = lean_string_utf8_byte_size(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_6);
x_80 = l_Lake_libTomlConfigFileContents___closed__0;
x_81 = lean_string_append(x_76, x_80);
x_82 = l_IO_FS_writeFile(x_72, x_81, x_74);
lean_dec(x_81);
lean_dec(x_72);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_36 = x_73;
x_37 = x_83;
goto block_44;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_io_error_to_string(x_84);
x_87 = lean_box(3);
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
x_89 = lean_unbox(x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_89);
x_90 = lean_apply_2(x_73, x_88, x_85);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_76);
x_97 = lean_ctor_get(x_3, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_string_utf8_byte_size(x_98);
lean_dec(x_98);
x_100 = lean_nat_dec_eq(x_99, x_78);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = l_System_FilePath_pathExists(x_72, x_74);
lean_dec(x_72);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_105 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_105 == 0)
{
uint8_t x_106; 
lean_dec(x_6);
x_106 = lean_unbox(x_102);
lean_dec(x_102);
x_45 = x_73;
x_46 = x_106;
x_47 = x_103;
goto block_51;
}
else
{
uint8_t x_107; 
x_107 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_6);
x_108 = lean_unbox(x_102);
lean_dec(x_102);
x_45 = x_73;
x_46 = x_108;
x_47 = x_103;
goto block_51;
}
else
{
lean_object* x_109; size_t x_110; size_t x_111; lean_object* x_112; 
x_109 = lean_box(0);
x_110 = 0;
x_111 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_73);
x_112 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_6, x_104, x_110, x_111, x_109, x_73, x_103);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_unbox(x_102);
lean_dec(x_102);
x_45 = x_73;
x_46 = x_114;
x_47 = x_113;
goto block_51;
}
else
{
lean_dec(x_102);
lean_dec(x_73);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_112;
}
}
}
}
else
{
lean_dec(x_72);
lean_dec(x_6);
x_36 = x_73;
x_37 = x_74;
goto block_44;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_6);
x_115 = l_Lake_initPkg___elam__16___redArg___closed__11;
lean_inc(x_73);
x_116 = lean_apply_2(x_73, x_115, x_74);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lake_mathToolchainBlobUrl___closed__0;
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lake_initPkg___elam__16___redArg___closed__12;
x_121 = l_Lake_download(x_118, x_72, x_120, x_120, x_117);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_8);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_array_get_size(x_124);
x_126 = lean_nat_dec_lt(x_119, x_125);
if (x_126 == 0)
{
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_7);
x_36 = x_73;
x_37 = x_123;
goto block_44;
}
else
{
uint8_t x_127; 
x_127 = lean_nat_dec_le(x_125, x_125);
if (x_127 == 0)
{
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_7);
x_36 = x_73;
x_37 = x_123;
goto block_44;
}
else
{
lean_object* x_128; size_t x_129; size_t x_130; lean_object* x_131; 
x_128 = lean_box(0);
x_129 = 0;
x_130 = lean_usize_of_nat(x_125);
lean_dec(x_125);
lean_inc(x_73);
x_131 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_7, x_124, x_129, x_130, x_128, x_73, x_123);
lean_dec(x_124);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_36 = x_73;
x_37 = x_132;
goto block_44;
}
else
{
x_66 = x_73;
x_67 = x_131;
goto block_71;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_7);
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
lean_dec(x_121);
x_134 = lean_ctor_get(x_122, 1);
lean_inc(x_134);
lean_dec(x_122);
x_135 = lean_array_get_size(x_134);
x_136 = lean_nat_dec_lt(x_119, x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = lean_box(0);
x_52 = x_73;
x_53 = x_137;
x_54 = x_133;
goto block_61;
}
else
{
uint8_t x_138; 
x_138 = lean_nat_dec_le(x_135, x_135);
if (x_138 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = x_73;
x_63 = x_133;
goto block_65;
}
else
{
lean_object* x_139; size_t x_140; size_t x_141; lean_object* x_142; 
x_139 = lean_box(0);
x_140 = 0;
x_141 = lean_usize_of_nat(x_135);
lean_dec(x_135);
lean_inc(x_73);
x_142 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_8, x_134, x_140, x_141, x_139, x_73, x_133);
lean_dec(x_134);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_62 = x_73;
x_63 = x_143;
goto block_65;
}
else
{
x_66 = x_73;
x_67 = x_142;
goto block_71;
}
}
}
}
}
}
block_191:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_147 = l_Lake_initPkg___elam__16___redArg___closed__13;
lean_inc(x_1);
x_148 = l_Lake_joinRelative(x_1, x_147);
x_149 = lean_box(4);
x_150 = lean_unbox(x_149);
x_151 = lean_io_prim_handle_mk(x_148, x_150, x_146);
lean_dec(x_148);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lake_gitignoreContents___closed__0;
x_155 = lean_io_prim_handle_put_str(x_152, x_154, x_153);
lean_dec(x_152);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_161; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lake_initPkg___elam__16___redArg___closed__14;
lean_inc(x_1);
x_158 = l_Lake_joinRelative(x_1, x_157);
x_159 = lean_box(3);
x_160 = lean_unbox(x_159);
x_161 = l_Lake_instDecidableEqInitTemplate(x_5, x_160);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; uint8_t x_164; 
x_162 = lean_box(4);
x_163 = lean_unbox(x_162);
x_164 = l_Lake_instDecidableEqInitTemplate(x_5, x_163);
x_72 = x_158;
x_73 = x_145;
x_74 = x_156;
x_75 = x_164;
goto block_144;
}
else
{
x_72 = x_158;
x_73 = x_145;
x_74 = x_156;
x_75 = x_161;
goto block_144;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; uint8_t x_172; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = lean_ctor_get(x_155, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_155, 1);
lean_inc(x_166);
lean_dec(x_155);
x_167 = lean_io_error_to_string(x_165);
x_168 = lean_box(3);
x_169 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_169, 0, x_167);
x_170 = lean_unbox(x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_170);
x_171 = lean_apply_2(x_145, x_169, x_166);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 0);
lean_dec(x_173);
x_174 = lean_box(0);
lean_ctor_set_tag(x_171, 1);
lean_ctor_set(x_171, 0, x_174);
return x_171;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_ctor_get(x_151, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_151, 1);
lean_inc(x_179);
lean_dec(x_151);
x_180 = lean_io_error_to_string(x_178);
x_181 = lean_box(3);
x_182 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_182, 0, x_180);
x_183 = lean_unbox(x_181);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_183);
x_184 = lean_apply_2(x_145, x_182, x_179);
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_184, 0);
lean_dec(x_186);
x_187 = lean_box(0);
lean_ctor_set_tag(x_184, 1);
lean_ctor_set(x_184, 0, x_187);
return x_184;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
lean_dec(x_184);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
block_197:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = l_Lake_initPkg___elam__16___redArg___closed__16;
lean_inc(x_192);
x_195 = lean_apply_2(x_192, x_194, x_193);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_145 = x_192;
x_146 = x_196;
goto block_191;
}
block_202:
{
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_145 = x_198;
x_146 = x_200;
goto block_191;
}
else
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_192 = x_198;
x_193 = x_201;
goto block_197;
}
}
block_239:
{
uint8_t x_206; 
x_206 = l_Lake_initPkg___elam__16___redArg___closed__18;
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; 
x_207 = lean_unsigned_to_nat(0u);
x_208 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_209 = l_Lake_initPkg___elam__16___redArg___closed__24;
x_210 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_211 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_1);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_1);
x_213 = lean_box(1);
x_214 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_214, 0, x_210);
lean_ctor_set(x_214, 1, x_211);
lean_ctor_set(x_214, 2, x_209);
lean_ctor_set(x_214, 3, x_212);
lean_ctor_set(x_214, 4, x_208);
x_215 = lean_unbox(x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*5, x_215);
lean_ctor_set_uint8(x_214, sizeof(void*)*5 + 1, x_203);
x_216 = lean_unbox(x_213);
x_217 = l_Lake_proc(x_214, x_216, x_208, x_205);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_10);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_array_get_size(x_220);
x_222 = lean_nat_dec_lt(x_207, x_221);
if (x_222 == 0)
{
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_9);
x_145 = x_204;
x_146 = x_219;
goto block_191;
}
else
{
uint8_t x_223; 
x_223 = lean_nat_dec_le(x_221, x_221);
if (x_223 == 0)
{
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_9);
x_145 = x_204;
x_146 = x_219;
goto block_191;
}
else
{
lean_object* x_224; size_t x_225; size_t x_226; lean_object* x_227; 
x_224 = lean_box(0);
x_225 = 0;
x_226 = lean_usize_of_nat(x_221);
lean_dec(x_221);
lean_inc(x_204);
x_227 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_9, x_220, x_225, x_226, x_224, x_204, x_219);
lean_dec(x_220);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_145 = x_204;
x_146 = x_228;
goto block_191;
}
else
{
x_198 = x_204;
x_199 = x_227;
goto block_202;
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
lean_dec(x_9);
x_229 = lean_ctor_get(x_217, 1);
lean_inc(x_229);
lean_dec(x_217);
x_230 = lean_ctor_get(x_218, 1);
lean_inc(x_230);
lean_dec(x_218);
x_231 = lean_array_get_size(x_230);
x_232 = lean_nat_dec_lt(x_207, x_231);
if (x_232 == 0)
{
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_10);
x_192 = x_204;
x_193 = x_229;
goto block_197;
}
else
{
uint8_t x_233; 
x_233 = lean_nat_dec_le(x_231, x_231);
if (x_233 == 0)
{
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_10);
x_192 = x_204;
x_193 = x_229;
goto block_197;
}
else
{
lean_object* x_234; size_t x_235; size_t x_236; lean_object* x_237; 
x_234 = lean_box(0);
x_235 = 0;
x_236 = lean_usize_of_nat(x_231);
lean_dec(x_231);
lean_inc(x_204);
x_237 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_10, x_230, x_235, x_236, x_234, x_204, x_229);
lean_dec(x_230);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_192 = x_204;
x_193 = x_238;
goto block_197;
}
else
{
x_198 = x_204;
x_199 = x_237;
goto block_202;
}
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
x_145 = x_204;
x_146 = x_205;
goto block_191;
}
}
block_245:
{
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_203 = x_240;
x_204 = x_241;
x_205 = x_243;
goto block_239;
}
else
{
lean_object* x_244; 
lean_dec(x_10);
lean_dec(x_9);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_192 = x_241;
x_193 = x_244;
goto block_197;
}
}
block_281:
{
if (x_247 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; 
x_249 = lean_unsigned_to_nat(0u);
x_250 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_251 = l_Lake_initPkg___elam__16___redArg___closed__31;
x_252 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_253 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_1);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_1);
x_255 = lean_box(1);
x_256 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_256, 0, x_252);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_251);
lean_ctor_set(x_256, 3, x_254);
lean_ctor_set(x_256, 4, x_250);
x_257 = lean_unbox(x_255);
lean_ctor_set_uint8(x_256, sizeof(void*)*5, x_257);
lean_ctor_set_uint8(x_256, sizeof(void*)*5 + 1, x_247);
x_258 = lean_unbox(x_255);
x_259 = l_Lake_proc(x_256, x_258, x_250, x_248);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
lean_dec(x_12);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_array_get_size(x_262);
x_264 = lean_nat_dec_lt(x_249, x_263);
if (x_264 == 0)
{
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_11);
x_203 = x_247;
x_204 = x_246;
x_205 = x_261;
goto block_239;
}
else
{
uint8_t x_265; 
x_265 = lean_nat_dec_le(x_263, x_263);
if (x_265 == 0)
{
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_11);
x_203 = x_247;
x_204 = x_246;
x_205 = x_261;
goto block_239;
}
else
{
lean_object* x_266; size_t x_267; size_t x_268; lean_object* x_269; 
x_266 = lean_box(0);
x_267 = 0;
x_268 = lean_usize_of_nat(x_263);
lean_dec(x_263);
lean_inc(x_246);
x_269 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_11, x_262, x_267, x_268, x_266, x_246, x_261);
lean_dec(x_262);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_203 = x_247;
x_204 = x_246;
x_205 = x_270;
goto block_239;
}
else
{
x_240 = x_247;
x_241 = x_246;
x_242 = x_269;
goto block_245;
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
lean_dec(x_11);
x_271 = lean_ctor_get(x_259, 1);
lean_inc(x_271);
lean_dec(x_259);
x_272 = lean_ctor_get(x_260, 1);
lean_inc(x_272);
lean_dec(x_260);
x_273 = lean_array_get_size(x_272);
x_274 = lean_nat_dec_lt(x_249, x_273);
if (x_274 == 0)
{
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_192 = x_246;
x_193 = x_271;
goto block_197;
}
else
{
uint8_t x_275; 
x_275 = lean_nat_dec_le(x_273, x_273);
if (x_275 == 0)
{
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_192 = x_246;
x_193 = x_271;
goto block_197;
}
else
{
lean_object* x_276; size_t x_277; size_t x_278; lean_object* x_279; 
x_276 = lean_box(0);
x_277 = 0;
x_278 = lean_usize_of_nat(x_273);
lean_dec(x_273);
lean_inc(x_246);
x_279 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_12, x_272, x_277, x_278, x_276, x_246, x_271);
lean_dec(x_272);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
lean_dec(x_10);
lean_dec(x_9);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_192 = x_246;
x_193 = x_280;
goto block_197;
}
else
{
x_240 = x_247;
x_241 = x_246;
x_242 = x_279;
goto block_245;
}
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_145 = x_246;
x_146 = x_248;
goto block_191;
}
}
block_305:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_284 = l_Lake_initPkg___elam__16___redArg___closed__35;
x_285 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_286 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_1);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_1);
x_288 = l_Lake_initPkg___elam__16___redArg___closed__36;
x_289 = lean_box(1);
x_290 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_290, 0, x_285);
lean_ctor_set(x_290, 1, x_286);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set(x_290, 3, x_287);
lean_ctor_set(x_290, 4, x_288);
x_291 = lean_unbox(x_289);
lean_ctor_set_uint8(x_290, sizeof(void*)*5, x_291);
lean_ctor_set_uint8(x_290, sizeof(void*)*5 + 1, x_4);
x_292 = l_Lake_testProc(x_290, x_283);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = l_Lake_initPkg___elam__16___redArg___closed__38;
if (x_295 == 0)
{
uint8_t x_296; 
lean_dec(x_13);
x_296 = lean_unbox(x_293);
lean_dec(x_293);
x_246 = x_282;
x_247 = x_296;
x_248 = x_294;
goto block_281;
}
else
{
uint8_t x_297; 
x_297 = l_Lake_initPkg___elam__16___redArg___closed__39;
if (x_297 == 0)
{
uint8_t x_298; 
lean_dec(x_13);
x_298 = lean_unbox(x_293);
lean_dec(x_293);
x_246 = x_282;
x_247 = x_298;
x_248 = x_294;
goto block_281;
}
else
{
lean_object* x_299; size_t x_300; size_t x_301; lean_object* x_302; 
x_299 = lean_box(0);
x_300 = 0;
x_301 = l_Lake_initPkg___elam__16___redArg___closed__40;
lean_inc(x_282);
x_302 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_13, x_288, x_300, x_301, x_299, x_282, x_294);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
lean_dec(x_302);
x_304 = lean_unbox(x_293);
lean_dec(x_293);
x_246 = x_282;
x_247 = x_304;
x_248 = x_303;
goto block_281;
}
else
{
lean_dec(x_293);
lean_dec(x_282);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_302;
}
}
}
}
block_325:
{
lean_object* x_310; 
x_310 = l_IO_FS_writeFile(x_307, x_309, x_306);
lean_dec(x_309);
lean_dec(x_307);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; 
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_282 = x_308;
x_283 = x_311;
goto block_305;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; uint8_t x_319; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_312 = lean_ctor_get(x_310, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
lean_dec(x_310);
x_314 = lean_io_error_to_string(x_312);
x_315 = lean_box(3);
x_316 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_316, 0, x_314);
x_317 = lean_unbox(x_315);
lean_ctor_set_uint8(x_316, sizeof(void*)*1, x_317);
x_318 = lean_apply_2(x_308, x_316, x_313);
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_318, 0);
lean_dec(x_320);
x_321 = lean_box(0);
lean_ctor_set_tag(x_318, 1);
lean_ctor_set(x_318, 0, x_321);
return x_318;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
lean_dec(x_318);
x_323 = lean_box(0);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
}
block_337:
{
if (x_328 == 0)
{
lean_object* x_330; uint8_t x_331; uint8_t x_332; 
x_330 = lean_box(4);
x_331 = lean_unbox(x_330);
x_332 = l_Lake_instDecidableEqInitTemplate(x_5, x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = l_Lake_dotlessName(x_14);
x_334 = l_Lake_readmeFileContents(x_333);
lean_dec(x_333);
x_306 = x_329;
x_307 = x_326;
x_308 = x_327;
x_309 = x_334;
goto block_325;
}
else
{
lean_object* x_335; lean_object* x_336; 
x_335 = l_Lake_dotlessName(x_14);
x_336 = l_Lake_mathReadmeFileContents(x_335);
lean_dec(x_335);
x_306 = x_329;
x_307 = x_326;
x_308 = x_327;
x_309 = x_336;
goto block_325;
}
}
else
{
lean_dec(x_326);
lean_dec(x_14);
x_282 = x_327;
x_283 = x_329;
goto block_305;
}
}
block_356:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_340 = l_Lake_initPkg___elam__16___redArg___closed__41;
lean_inc(x_1);
x_341 = l_Lake_joinRelative(x_1, x_340);
x_342 = l_System_FilePath_pathExists(x_341, x_339);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_346 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_346 == 0)
{
uint8_t x_347; 
lean_dec(x_15);
x_347 = lean_unbox(x_343);
lean_dec(x_343);
x_326 = x_341;
x_327 = x_338;
x_328 = x_347;
x_329 = x_344;
goto block_337;
}
else
{
uint8_t x_348; 
x_348 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_348 == 0)
{
uint8_t x_349; 
lean_dec(x_15);
x_349 = lean_unbox(x_343);
lean_dec(x_343);
x_326 = x_341;
x_327 = x_338;
x_328 = x_349;
x_329 = x_344;
goto block_337;
}
else
{
lean_object* x_350; size_t x_351; size_t x_352; lean_object* x_353; 
x_350 = lean_box(0);
x_351 = 0;
x_352 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_338);
x_353 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_15, x_345, x_351, x_352, x_350, x_338, x_344);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; uint8_t x_355; 
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
lean_dec(x_353);
x_355 = lean_unbox(x_343);
lean_dec(x_343);
x_326 = x_341;
x_327 = x_338;
x_328 = x_355;
x_329 = x_354;
goto block_337;
}
else
{
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_338);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_353;
}
}
}
}
block_395:
{
if (x_358 == 0)
{
lean_object* x_360; uint8_t x_361; uint8_t x_362; 
x_360 = lean_box(1);
x_361 = lean_unbox(x_360);
x_362 = l_Lake_instDecidableEqInitTemplate(x_5, x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = l_Lake_mainFileContents(x_16);
x_364 = l_IO_FS_writeFile(x_357, x_363, x_359);
lean_dec(x_363);
lean_dec(x_357);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_338 = x_18;
x_339 = x_365;
goto block_356;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; uint8_t x_373; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_366 = lean_ctor_get(x_364, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_io_error_to_string(x_366);
x_369 = lean_box(3);
x_370 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_370, 0, x_368);
x_371 = lean_unbox(x_369);
lean_ctor_set_uint8(x_370, sizeof(void*)*1, x_371);
x_372 = lean_apply_2(x_18, x_370, x_367);
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_372, 0);
lean_dec(x_374);
x_375 = lean_box(0);
lean_ctor_set_tag(x_372, 1);
lean_ctor_set(x_372, 0, x_375);
return x_372;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_372, 1);
lean_inc(x_376);
lean_dec(x_372);
x_377 = lean_box(0);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
}
else
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_16);
x_379 = l_Lake_exeFileContents___closed__0;
x_380 = l_IO_FS_writeFile(x_357, x_379, x_359);
lean_dec(x_357);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_338 = x_18;
x_339 = x_381;
goto block_356;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; uint8_t x_389; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_382 = lean_ctor_get(x_380, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
lean_dec(x_380);
x_384 = lean_io_error_to_string(x_382);
x_385 = lean_box(3);
x_386 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_386, 0, x_384);
x_387 = lean_unbox(x_385);
lean_ctor_set_uint8(x_386, sizeof(void*)*1, x_387);
x_388 = lean_apply_2(x_18, x_386, x_383);
x_389 = !lean_is_exclusive(x_388);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_388, 0);
lean_dec(x_390);
x_391 = lean_box(0);
lean_ctor_set_tag(x_388, 1);
lean_ctor_set(x_388, 0, x_391);
return x_388;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_388, 1);
lean_inc(x_392);
lean_dec(x_388);
x_393 = lean_box(0);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
}
}
else
{
lean_dec(x_357);
lean_dec(x_16);
x_338 = x_18;
x_339 = x_359;
goto block_356;
}
}
block_412:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_396 = l_Lake_mainFileName;
lean_inc(x_1);
x_397 = l_Lake_joinRelative(x_1, x_396);
x_398 = l_System_FilePath_pathExists(x_397, x_19);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_402 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_402 == 0)
{
uint8_t x_403; 
lean_dec(x_17);
x_403 = lean_unbox(x_399);
lean_dec(x_399);
x_357 = x_397;
x_358 = x_403;
x_359 = x_400;
goto block_395;
}
else
{
uint8_t x_404; 
x_404 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_404 == 0)
{
uint8_t x_405; 
lean_dec(x_17);
x_405 = lean_unbox(x_399);
lean_dec(x_399);
x_357 = x_397;
x_358 = x_405;
x_359 = x_400;
goto block_395;
}
else
{
lean_object* x_406; size_t x_407; size_t x_408; lean_object* x_409; 
x_406 = lean_box(0);
x_407 = 0;
x_408 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_18);
x_409 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_17, x_401, x_407, x_408, x_406, x_18, x_400);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; uint8_t x_411; 
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
lean_dec(x_409);
x_411 = lean_unbox(x_399);
lean_dec(x_399);
x_357 = x_397;
x_358 = x_411;
x_359 = x_410;
goto block_395;
}
else
{
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_409;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l_Lake_initPkg___elam__16___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_19, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_apply_2(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_initPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lake_initPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0_spec__0___redArg(x_5, x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT uint8_t l_Lake_initPkg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lakefile", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Basic.lean", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package already initialized", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_initPkg___closed__3;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_204; lean_object* x_270; uint8_t x_271; 
x_12 = l_Lake_initPkg___closed__0;
x_13 = l_Lake_ConfigLang_fileExtension(x_4);
x_14 = l_System_FilePath_addExtension(x_12, x_13);
lean_dec(x_13);
lean_inc(x_1);
x_15 = l_Lake_joinRelative(x_1, x_14);
lean_dec(x_14);
x_16 = l_System_FilePath_pathExists(x_15, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_closure((void*)(l_Lake_initPkg___elam__0___boxed), 4, 0);
x_270 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_271 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_271 == 0)
{
x_204 = x_18;
goto block_269;
}
else
{
uint8_t x_272; 
x_272 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_272 == 0)
{
x_204 = x_18;
goto block_269;
}
else
{
lean_object* x_273; size_t x_274; size_t x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_box(0);
x_274 = 0;
x_275 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_6);
x_276 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_270, x_274, x_275, x_273, x_6, x_18);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
x_204 = x_277;
goto block_269;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_42:
{
lean_object* x_26; 
x_26 = l_IO_FS_writeFile(x_20, x_25, x_22);
lean_dec(x_25);
lean_dec(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc_n(x_19, 9);
x_28 = l_Lake_initPkg___elam__16___redArg(x_1, x_12, x_5, x_21, x_3, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_2, x_19, x_24, x_19, x_23, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_io_error_to_string(x_29);
x_32 = lean_box(3);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
x_35 = lean_apply_2(x_23, x_33, x_30);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
block_57:
{
lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_49 = lean_box(4);
x_50 = lean_unbox(x_49);
x_51 = l_Lake_instDecidableEqInitTemplate(x_3, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
lean_inc(x_46);
x_54 = l_Lean_Name_toString(x_46, x_53, x_45);
lean_inc(x_46);
x_55 = l_Lake_libRootFileContents(x_54, x_46);
lean_dec(x_54);
x_20 = x_43;
x_21 = x_44;
x_22 = x_48;
x_23 = x_47;
x_24 = x_46;
x_25 = x_55;
goto block_42;
}
else
{
lean_object* x_56; 
lean_dec(x_45);
lean_inc(x_46);
x_56 = l_Lake_mathLibRootFileContents(x_46);
x_20 = x_43;
x_21 = x_44;
x_22 = x_48;
x_23 = x_47;
x_24 = x_46;
x_25 = x_56;
goto block_42;
}
}
block_97:
{
if (x_64 == 0)
{
lean_object* x_66; 
x_66 = l_IO_FS_createDirAll(x_62, x_65);
lean_dec(x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lake_basicFileContents___closed__0;
x_69 = l_IO_FS_writeFile(x_63, x_68, x_67);
lean_dec(x_63);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_43 = x_58;
x_44 = x_59;
x_45 = x_60;
x_46 = x_61;
x_47 = x_6;
x_48 = x_70;
goto block_57;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_io_error_to_string(x_71);
x_74 = lean_box(3);
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_unbox(x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_76);
x_77 = lean_apply_2(x_6, x_75, x_72);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set_tag(x_77, 1);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_84 = lean_ctor_get(x_66, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_66, 1);
lean_inc(x_85);
lean_dec(x_66);
x_86 = lean_io_error_to_string(x_84);
x_87 = lean_box(3);
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
x_89 = lean_unbox(x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_89);
x_90 = lean_apply_2(x_6, x_88, x_85);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_dec(x_63);
lean_dec(x_62);
x_43 = x_58;
x_44 = x_59;
x_45 = x_60;
x_46 = x_61;
x_47 = x_6;
x_48 = x_65;
goto block_57;
}
}
block_140:
{
lean_object* x_103; lean_object* x_104; 
lean_inc(x_100);
lean_inc(x_2);
x_103 = l_Lake_InitTemplate_configFileContents(x_3, x_4, x_2, x_100);
x_104 = l_IO_FS_writeFile(x_15, x_103, x_102);
lean_dec(x_103);
lean_dec(x_15);
if (lean_obj_tag(x_104) == 0)
{
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_99);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
lean_inc_n(x_19, 9);
x_106 = l_Lake_initPkg___elam__16___redArg(x_1, x_12, x_5, x_98, x_3, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_2, x_19, x_100, x_19, x_6, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
lean_dec(x_101);
x_109 = l_Lake_escapeIdent___closed__0;
lean_inc(x_108);
x_110 = l_System_FilePath_withExtension(x_108, x_109);
x_111 = l_Lake_initPkg___closed__1;
lean_inc(x_110);
x_112 = l_Lake_joinRelative(x_110, x_111);
x_113 = l_System_FilePath_pathExists(x_112, x_107);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_117 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = lean_unbox(x_114);
lean_dec(x_114);
x_58 = x_108;
x_59 = x_98;
x_60 = x_99;
x_61 = x_100;
x_62 = x_110;
x_63 = x_112;
x_64 = x_118;
x_65 = x_115;
goto block_97;
}
else
{
uint8_t x_119; 
x_119 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = lean_unbox(x_114);
lean_dec(x_114);
x_58 = x_108;
x_59 = x_98;
x_60 = x_99;
x_61 = x_100;
x_62 = x_110;
x_63 = x_112;
x_64 = x_120;
x_65 = x_115;
goto block_97;
}
else
{
lean_object* x_121; size_t x_122; size_t x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_box(0);
x_122 = 0;
x_123 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_6);
x_124 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_116, x_122, x_123, x_121, x_6, x_115);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_unbox(x_114);
lean_dec(x_114);
x_58 = x_108;
x_59 = x_98;
x_60 = x_99;
x_61 = x_100;
x_62 = x_110;
x_63 = x_112;
x_64 = x_126;
x_65 = x_125;
goto block_97;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_ctor_get(x_104, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_104, 1);
lean_inc(x_128);
lean_dec(x_104);
x_129 = lean_io_error_to_string(x_127);
x_130 = lean_box(3);
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
x_132 = lean_unbox(x_130);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_132);
x_133 = lean_apply_2(x_6, x_131, x_128);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_dec(x_135);
x_136 = lean_box(0);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 0, x_136);
return x_133;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec(x_133);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
block_149:
{
if (x_145 == 0)
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_144);
x_98 = x_142;
x_99 = x_143;
x_100 = x_141;
x_101 = x_147;
x_102 = x_146;
goto block_140;
}
else
{
lean_object* x_148; 
lean_dec(x_144);
x_148 = lean_box(0);
x_98 = x_142;
x_99 = x_143;
x_100 = x_141;
x_101 = x_148;
x_102 = x_146;
goto block_140;
}
}
block_173:
{
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_151);
x_156 = l_Lake_toUpperCamelCase(x_2);
x_157 = l_Lean_modToFilePath(x_1, x_156, x_154);
lean_dec(x_154);
x_158 = l_System_FilePath_pathExists(x_157, x_153);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_162 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = lean_unbox(x_159);
lean_dec(x_159);
x_141 = x_156;
x_142 = x_150;
x_143 = x_152;
x_144 = x_157;
x_145 = x_163;
x_146 = x_160;
goto block_149;
}
else
{
uint8_t x_164; 
x_164 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_164 == 0)
{
uint8_t x_165; 
x_165 = lean_unbox(x_159);
lean_dec(x_159);
x_141 = x_156;
x_142 = x_150;
x_143 = x_152;
x_144 = x_157;
x_145 = x_165;
x_146 = x_160;
goto block_149;
}
else
{
lean_object* x_166; size_t x_167; size_t x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_166 = lean_box(0);
x_167 = 0;
x_168 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_6);
x_169 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_161, x_167, x_168, x_166, x_6, x_160);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_unbox(x_159);
lean_dec(x_159);
x_141 = x_156;
x_142 = x_150;
x_143 = x_152;
x_144 = x_157;
x_145 = x_171;
x_146 = x_170;
goto block_149;
}
}
}
else
{
lean_object* x_172; 
lean_dec(x_154);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_151);
lean_inc(x_2);
x_98 = x_150;
x_99 = x_152;
x_100 = x_2;
x_101 = x_172;
x_102 = x_153;
goto block_140;
}
}
block_183:
{
lean_object* x_180; uint8_t x_181; uint8_t x_182; 
x_180 = lean_box(1);
x_181 = lean_unbox(x_180);
x_182 = l_Lake_instDecidableEqInitTemplate(x_3, x_181);
if (x_182 == 0)
{
x_150 = x_174;
x_151 = x_175;
x_152 = x_176;
x_153 = x_179;
x_154 = x_177;
x_155 = x_178;
goto block_173;
}
else
{
x_150 = x_174;
x_151 = x_175;
x_152 = x_176;
x_153 = x_179;
x_154 = x_177;
x_155 = x_182;
goto block_173;
}
}
block_203:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_187 = l_Lake_initPkg___closed__2;
x_188 = l_Lean_modToFilePath(x_1, x_2, x_187);
x_189 = l_System_FilePath_pathExists(x_188, x_186);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_193 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_193 == 0)
{
uint8_t x_194; 
x_194 = lean_unbox(x_190);
lean_dec(x_190);
x_174 = x_184;
x_175 = x_188;
x_176 = x_185;
x_177 = x_187;
x_178 = x_194;
x_179 = x_191;
goto block_183;
}
else
{
uint8_t x_195; 
x_195 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_195 == 0)
{
uint8_t x_196; 
x_196 = lean_unbox(x_190);
lean_dec(x_190);
x_174 = x_184;
x_175 = x_188;
x_176 = x_185;
x_177 = x_187;
x_178 = x_196;
x_179 = x_191;
goto block_183;
}
else
{
lean_object* x_197; size_t x_198; size_t x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_box(0);
x_198 = 0;
x_199 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_6);
x_200 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_192, x_198, x_199, x_197, x_6, x_191);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_unbox(x_190);
lean_dec(x_190);
x_174 = x_184;
x_175 = x_188;
x_176 = x_185;
x_177 = x_187;
x_178 = x_202;
x_179 = x_201;
goto block_183;
}
}
}
block_269:
{
uint8_t x_205; 
x_205 = lean_unbox(x_17);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_206 = lean_unsigned_to_nat(0u);
x_207 = l_Lake_initPkg___elam__16___redArg___closed__5;
lean_inc(x_1);
x_208 = l_Lake_createLeanActionWorkflow(x_1, x_3, x_207, x_204);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_208, 0);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_17);
x_212 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__0___boxed), 2, 1);
lean_closure_set(x_212, 0, x_17);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_free_object(x_208);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_214 = lean_array_get_size(x_213);
x_215 = lean_nat_dec_lt(x_206, x_214);
if (x_215 == 0)
{
uint8_t x_216; 
lean_dec(x_214);
lean_dec(x_213);
x_216 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_216;
x_185 = x_212;
x_186 = x_211;
goto block_203;
}
else
{
uint8_t x_217; 
x_217 = lean_nat_dec_le(x_214, x_214);
if (x_217 == 0)
{
uint8_t x_218; 
lean_dec(x_214);
lean_dec(x_213);
x_218 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_218;
x_185 = x_212;
x_186 = x_211;
goto block_203;
}
else
{
lean_object* x_219; size_t x_220; size_t x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_219 = lean_box(0);
x_220 = 0;
x_221 = lean_usize_of_nat(x_214);
lean_dec(x_214);
lean_inc(x_6);
x_222 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_213, x_220, x_221, x_219, x_6, x_211);
lean_dec(x_213);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_224;
x_185 = x_212;
x_186 = x_223;
goto block_203;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_212);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_225 = lean_ctor_get(x_210, 1);
lean_inc(x_225);
lean_dec(x_210);
x_226 = lean_array_get_size(x_225);
x_227 = lean_nat_dec_lt(x_206, x_226);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_6);
x_228 = lean_box(0);
lean_ctor_set_tag(x_208, 1);
lean_ctor_set(x_208, 0, x_228);
return x_208;
}
else
{
uint8_t x_229; 
lean_free_object(x_208);
x_229 = lean_nat_dec_le(x_226, x_226);
if (x_229 == 0)
{
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_6);
x_8 = x_211;
goto block_11;
}
else
{
lean_object* x_230; size_t x_231; size_t x_232; lean_object* x_233; lean_object* x_234; 
x_230 = lean_box(0);
x_231 = 0;
x_232 = lean_usize_of_nat(x_226);
lean_dec(x_226);
x_233 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_225, x_231, x_232, x_230, x_6, x_211);
lean_dec(x_225);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_8 = x_234;
goto block_11;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_208, 0);
x_236 = lean_ctor_get(x_208, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_208);
lean_inc(x_17);
x_237 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__0___boxed), 2, 1);
lean_closure_set(x_237, 0, x_17);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_array_get_size(x_238);
x_240 = lean_nat_dec_lt(x_206, x_239);
if (x_240 == 0)
{
uint8_t x_241; 
lean_dec(x_239);
lean_dec(x_238);
x_241 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_241;
x_185 = x_237;
x_186 = x_236;
goto block_203;
}
else
{
uint8_t x_242; 
x_242 = lean_nat_dec_le(x_239, x_239);
if (x_242 == 0)
{
uint8_t x_243; 
lean_dec(x_239);
lean_dec(x_238);
x_243 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_243;
x_185 = x_237;
x_186 = x_236;
goto block_203;
}
else
{
lean_object* x_244; size_t x_245; size_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_244 = lean_box(0);
x_245 = 0;
x_246 = lean_usize_of_nat(x_239);
lean_dec(x_239);
lean_inc(x_6);
x_247 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_238, x_245, x_246, x_244, x_6, x_236);
lean_dec(x_238);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_249;
x_185 = x_237;
x_186 = x_248;
goto block_203;
}
}
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; 
lean_dec(x_237);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_ctor_get(x_235, 1);
lean_inc(x_250);
lean_dec(x_235);
x_251 = lean_array_get_size(x_250);
x_252 = lean_nat_dec_lt(x_206, x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_6);
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_236);
return x_254;
}
else
{
uint8_t x_255; 
x_255 = lean_nat_dec_le(x_251, x_251);
if (x_255 == 0)
{
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_6);
x_8 = x_236;
goto block_11;
}
else
{
lean_object* x_256; size_t x_257; size_t x_258; lean_object* x_259; lean_object* x_260; 
x_256 = lean_box(0);
x_257 = 0;
x_258 = lean_usize_of_nat(x_251);
lean_dec(x_251);
x_259 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_250, x_257, x_258, x_256, x_6, x_236);
lean_dec(x_250);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_8 = x_260;
goto block_11;
}
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_261 = l_Lake_initPkg___closed__4;
x_262 = lean_apply_2(x_6, x_261, x_204);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_262, 0);
lean_dec(x_264);
x_265 = lean_box(0);
lean_ctor_set_tag(x_262, 1);
lean_ctor_set(x_262, 0, x_265);
return x_262;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
lean_dec(x_262);
x_267 = lean_box(0);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_initPkg___elam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_4);
lean_dec(x_4);
x_21 = lean_unbox(x_5);
lean_dec(x_5);
x_22 = l_Lake_initPkg___elam__16___redArg(x_1, x_2, x_3, x_20, x_21, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox(x_4);
lean_dec(x_4);
x_22 = lean_unbox(x_5);
lean_dec(x_5);
x_23 = l_Lake_initPkg___elam__16(x_1, x_2, x_3, x_21, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_18);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_initPkg___elam__0___at___Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_initPkg___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lake_initPkg(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqChar___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 92;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 47;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1;
x_2 = l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2___boxed__const__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_validatePkgName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__0;
x_7 = l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2;
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
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_validatePkgName_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
static lean_object* _init_l_Lake_validatePkgName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("illegal package name '", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_validatePkgName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqString___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_validatePkgName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_validatePkgName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("main", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_validatePkgName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_validatePkgName___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_validatePkgName___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_validatePkgName___closed__4;
x_2 = l_Lake_validatePkgName___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_validatePkgName___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_validatePkgName___closed__5;
x_2 = l_Lake_initPkg___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_validatePkgName___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_validatePkgName___closed__6;
x_2 = l_Lake_initPkg___elam__16___redArg___closed__27;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_validatePkgName___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reserved package name", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_validatePkgName___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_validatePkgName___closed__8;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_validatePkgName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_16; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_string_utf8_byte_size(x_1);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_String_anyAux___at___Lake_validatePkgName_spec__1(x_35, x_1, x_33, x_34);
lean_dec(x_33);
if (x_36 == 0)
{
goto block_15;
}
else
{
x_16 = x_35;
goto block_32;
}
}
else
{
lean_dec(x_33);
x_16 = x_35;
goto block_32;
}
block_15:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = l_Lake_validatePkgName___closed__0;
x_5 = lean_string_append(x_4, x_1);
lean_dec(x_1);
x_6 = l_Lake_createLeanActionWorkflow___closed__6;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_box(3);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_array_get_size(x_2);
x_12 = lean_array_push(x_2, x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
block_32:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_string_utf8_byte_size(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_String_anyAux___at___Lake_validatePkgName_spec__0(x_1, x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = l_Lake_validatePkgName___closed__1;
x_21 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_18, x_1);
x_22 = l_Lake_validatePkgName___closed__7;
x_23 = l_List_elem___redArg(x_20, x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_3);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = l_Lake_validatePkgName___closed__9;
x_28 = lean_array_get_size(x_2);
x_29 = lean_array_push(x_2, x_27);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
else
{
goto block_15;
}
}
else
{
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___at___Lake_validatePkgName_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_String_anyAux___at___Lake_validatePkgName_spec__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_36; lean_object* x_37; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_62; lean_object* x_63; lean_object* x_66; lean_object* x_67; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_145; lean_object* x_146; lean_object* x_192; lean_object* x_193; lean_object* x_198; lean_object* x_199; uint8_t x_203; lean_object* x_204; lean_object* x_205; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_246; uint8_t x_247; lean_object* x_248; lean_object* x_282; lean_object* x_283; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_326; lean_object* x_327; uint8_t x_328; lean_object* x_329; lean_object* x_338; lean_object* x_339; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_413; 
x_413 = lean_box(x_6);
switch (lean_obj_tag(x_413)) {
case 0:
{
goto block_412;
}
case 1:
{
goto block_412;
}
default: 
{
lean_dec(x_413);
lean_dec(x_18);
lean_dec(x_17);
x_338 = x_1;
x_339 = x_19;
goto block_356;
}
}
block_35:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_box(0);
x_26 = l_Lake_escapeName_x21___closed__4;
lean_inc(x_2);
x_27 = l_Lake_joinRelative(x_2, x_26);
lean_inc(x_27);
x_28 = l_Lake_joinRelative(x_27, x_3);
x_29 = l_Lake_initPkg___elam__16___redArg___closed__0;
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = l_Lake_escapeIdent___closed__0;
x_33 = lean_alloc_ctor(0, 12, 3);
lean_ctor_set(x_33, 0, x_4);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_2);
lean_ctor_set(x_33, 3, x_26);
lean_ctor_set(x_33, 4, x_27);
lean_ctor_set(x_33, 5, x_3);
lean_ctor_set(x_33, 6, x_28);
lean_ctor_set(x_33, 7, x_29);
lean_ctor_set(x_33, 8, x_30);
lean_ctor_set(x_33, 9, x_31);
lean_ctor_set(x_33, 10, x_32);
lean_ctor_set(x_33, 11, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*12, x_5);
lean_ctor_set_uint8(x_33, sizeof(void*)*12 + 1, x_5);
lean_ctor_set_uint8(x_33, sizeof(void*)*12 + 2, x_22);
x_34 = l_Lake_updateManifest(x_33, x_30, x_21, x_20);
return x_34;
}
}
block_44:
{
lean_object* x_38; uint8_t x_39; uint8_t x_40; 
x_38 = lean_box(3);
x_39 = lean_unbox(x_38);
x_40 = l_Lake_instDecidableEqInitTemplate(x_6, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_41 = lean_box(4);
x_42 = lean_unbox(x_41);
x_43 = l_Lake_instDecidableEqInitTemplate(x_6, x_42);
x_20 = x_37;
x_21 = x_36;
x_22 = x_43;
goto block_35;
}
else
{
x_20 = x_37;
x_21 = x_36;
x_22 = x_40;
goto block_35;
}
}
block_51:
{
if (x_46 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = l_Lake_initPkg___elam__16___redArg___closed__2;
lean_inc(x_45);
x_49 = lean_apply_2(x_45, x_48, x_47);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_36 = x_45;
x_37 = x_50;
goto block_44;
}
else
{
x_36 = x_45;
x_37 = x_47;
goto block_44;
}
}
block_61:
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = l_Lake_initPkg___elam__16___redArg___closed__4;
x_56 = lean_apply_2(x_52, x_55, x_54);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_dec(x_58);
lean_ctor_set_tag(x_56, 1);
lean_ctor_set(x_56, 0, x_53);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
block_65:
{
lean_object* x_64; 
x_64 = lean_box(0);
x_52 = x_62;
x_53 = x_64;
x_54 = x_63;
goto block_61;
}
block_71:
{
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_36 = x_66;
x_37 = x_68;
goto block_44;
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_52 = x_66;
x_53 = x_69;
x_54 = x_70;
goto block_61;
}
}
block_144:
{
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_9);
lean_dec(x_8);
x_76 = l_Lake_Env_toolchain(x_4);
x_77 = lean_string_utf8_byte_size(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_7);
x_80 = l_Lake_libTomlConfigFileContents___closed__0;
x_81 = lean_string_append(x_76, x_80);
x_82 = l_IO_FS_writeFile(x_74, x_81, x_73);
lean_dec(x_81);
lean_dec(x_74);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_36 = x_72;
x_37 = x_83;
goto block_44;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_io_error_to_string(x_84);
x_87 = lean_box(3);
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
x_89 = lean_unbox(x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_89);
x_90 = lean_apply_2(x_72, x_88, x_85);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
lean_dec(x_76);
x_97 = lean_ctor_get(x_4, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_string_utf8_byte_size(x_98);
lean_dec(x_98);
x_100 = lean_nat_dec_eq(x_99, x_78);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = l_System_FilePath_pathExists(x_74, x_73);
lean_dec(x_74);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_105 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_105 == 0)
{
uint8_t x_106; 
lean_dec(x_7);
x_106 = lean_unbox(x_102);
lean_dec(x_102);
x_45 = x_72;
x_46 = x_106;
x_47 = x_103;
goto block_51;
}
else
{
uint8_t x_107; 
x_107 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_107 == 0)
{
uint8_t x_108; 
lean_dec(x_7);
x_108 = lean_unbox(x_102);
lean_dec(x_102);
x_45 = x_72;
x_46 = x_108;
x_47 = x_103;
goto block_51;
}
else
{
lean_object* x_109; size_t x_110; size_t x_111; lean_object* x_112; 
x_109 = lean_box(0);
x_110 = 0;
x_111 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_72);
x_112 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_7, x_104, x_110, x_111, x_109, x_72, x_103);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_unbox(x_102);
lean_dec(x_102);
x_45 = x_72;
x_46 = x_114;
x_47 = x_113;
goto block_51;
}
else
{
lean_dec(x_102);
lean_dec(x_72);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_112;
}
}
}
}
else
{
lean_dec(x_74);
lean_dec(x_7);
x_36 = x_72;
x_37 = x_73;
goto block_44;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_7);
x_115 = l_Lake_initPkg___elam__16___redArg___closed__11;
lean_inc(x_72);
x_116 = lean_apply_2(x_72, x_115, x_73);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_118 = l_Lake_mathToolchainBlobUrl___closed__0;
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lake_initPkg___elam__16___redArg___closed__12;
x_121 = l_Lake_download(x_118, x_74, x_120, x_120, x_117);
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_9);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_array_get_size(x_124);
x_126 = lean_nat_dec_lt(x_119, x_125);
if (x_126 == 0)
{
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_8);
x_36 = x_72;
x_37 = x_123;
goto block_44;
}
else
{
uint8_t x_127; 
x_127 = lean_nat_dec_le(x_125, x_125);
if (x_127 == 0)
{
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_8);
x_36 = x_72;
x_37 = x_123;
goto block_44;
}
else
{
lean_object* x_128; size_t x_129; size_t x_130; lean_object* x_131; 
x_128 = lean_box(0);
x_129 = 0;
x_130 = lean_usize_of_nat(x_125);
lean_dec(x_125);
lean_inc(x_72);
x_131 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_8, x_124, x_129, x_130, x_128, x_72, x_123);
lean_dec(x_124);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
lean_dec(x_131);
x_36 = x_72;
x_37 = x_132;
goto block_44;
}
else
{
x_66 = x_72;
x_67 = x_131;
goto block_71;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_8);
x_133 = lean_ctor_get(x_121, 1);
lean_inc(x_133);
lean_dec(x_121);
x_134 = lean_ctor_get(x_122, 1);
lean_inc(x_134);
lean_dec(x_122);
x_135 = lean_array_get_size(x_134);
x_136 = lean_nat_dec_lt(x_119, x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_137 = lean_box(0);
x_52 = x_72;
x_53 = x_137;
x_54 = x_133;
goto block_61;
}
else
{
uint8_t x_138; 
x_138 = lean_nat_dec_le(x_135, x_135);
if (x_138 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = x_72;
x_63 = x_133;
goto block_65;
}
else
{
lean_object* x_139; size_t x_140; size_t x_141; lean_object* x_142; 
x_139 = lean_box(0);
x_140 = 0;
x_141 = lean_usize_of_nat(x_135);
lean_dec(x_135);
lean_inc(x_72);
x_142 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_9, x_134, x_140, x_141, x_139, x_72, x_133);
lean_dec(x_134);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
lean_dec(x_142);
x_62 = x_72;
x_63 = x_143;
goto block_65;
}
else
{
x_66 = x_72;
x_67 = x_142;
goto block_71;
}
}
}
}
}
}
block_191:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_147 = l_Lake_initPkg___elam__16___redArg___closed__13;
lean_inc(x_2);
x_148 = l_Lake_joinRelative(x_2, x_147);
x_149 = lean_box(4);
x_150 = lean_unbox(x_149);
x_151 = lean_io_prim_handle_mk(x_148, x_150, x_146);
lean_dec(x_148);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lake_gitignoreContents___closed__0;
x_155 = lean_io_prim_handle_put_str(x_152, x_154, x_153);
lean_dec(x_152);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_161; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lake_initPkg___elam__16___redArg___closed__14;
lean_inc(x_2);
x_158 = l_Lake_joinRelative(x_2, x_157);
x_159 = lean_box(3);
x_160 = lean_unbox(x_159);
x_161 = l_Lake_instDecidableEqInitTemplate(x_6, x_160);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; uint8_t x_164; 
x_162 = lean_box(4);
x_163 = lean_unbox(x_162);
x_164 = l_Lake_instDecidableEqInitTemplate(x_6, x_163);
x_72 = x_145;
x_73 = x_156;
x_74 = x_158;
x_75 = x_164;
goto block_144;
}
else
{
x_72 = x_145;
x_73 = x_156;
x_74 = x_158;
x_75 = x_161;
goto block_144;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; lean_object* x_171; uint8_t x_172; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_165 = lean_ctor_get(x_155, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_155, 1);
lean_inc(x_166);
lean_dec(x_155);
x_167 = lean_io_error_to_string(x_165);
x_168 = lean_box(3);
x_169 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_169, 0, x_167);
x_170 = lean_unbox(x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_170);
x_171 = lean_apply_2(x_145, x_169, x_166);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_171, 0);
lean_dec(x_173);
x_174 = lean_box(0);
lean_ctor_set_tag(x_171, 1);
lean_ctor_set(x_171, 0, x_174);
return x_171;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_171, 1);
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; lean_object* x_184; uint8_t x_185; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_ctor_get(x_151, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_151, 1);
lean_inc(x_179);
lean_dec(x_151);
x_180 = lean_io_error_to_string(x_178);
x_181 = lean_box(3);
x_182 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_182, 0, x_180);
x_183 = lean_unbox(x_181);
lean_ctor_set_uint8(x_182, sizeof(void*)*1, x_183);
x_184 = lean_apply_2(x_145, x_182, x_179);
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_184, 0);
lean_dec(x_186);
x_187 = lean_box(0);
lean_ctor_set_tag(x_184, 1);
lean_ctor_set(x_184, 0, x_187);
return x_184;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
lean_dec(x_184);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
}
block_197:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = l_Lake_initPkg___elam__16___redArg___closed__16;
lean_inc(x_192);
x_195 = lean_apply_2(x_192, x_194, x_193);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_145 = x_192;
x_146 = x_196;
goto block_191;
}
block_202:
{
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_145 = x_198;
x_146 = x_200;
goto block_191;
}
else
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_192 = x_198;
x_193 = x_201;
goto block_197;
}
}
block_239:
{
uint8_t x_206; 
x_206 = l_Lake_initPkg___elam__16___redArg___closed__18;
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; 
x_207 = lean_unsigned_to_nat(0u);
x_208 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_209 = l_Lake_initPkg___elam__16___redArg___closed__24;
x_210 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_211 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_2);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_2);
x_213 = lean_box(1);
x_214 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_214, 0, x_210);
lean_ctor_set(x_214, 1, x_211);
lean_ctor_set(x_214, 2, x_209);
lean_ctor_set(x_214, 3, x_212);
lean_ctor_set(x_214, 4, x_208);
x_215 = lean_unbox(x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*5, x_215);
lean_ctor_set_uint8(x_214, sizeof(void*)*5 + 1, x_203);
x_216 = lean_unbox(x_213);
x_217 = l_Lake_proc(x_214, x_216, x_208, x_205);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_11);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
x_221 = lean_array_get_size(x_220);
x_222 = lean_nat_dec_lt(x_207, x_221);
if (x_222 == 0)
{
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_10);
x_145 = x_204;
x_146 = x_219;
goto block_191;
}
else
{
uint8_t x_223; 
x_223 = lean_nat_dec_le(x_221, x_221);
if (x_223 == 0)
{
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_10);
x_145 = x_204;
x_146 = x_219;
goto block_191;
}
else
{
lean_object* x_224; size_t x_225; size_t x_226; lean_object* x_227; 
x_224 = lean_box(0);
x_225 = 0;
x_226 = lean_usize_of_nat(x_221);
lean_dec(x_221);
lean_inc(x_204);
x_227 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_10, x_220, x_225, x_226, x_224, x_204, x_219);
lean_dec(x_220);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_145 = x_204;
x_146 = x_228;
goto block_191;
}
else
{
x_198 = x_204;
x_199 = x_227;
goto block_202;
}
}
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
lean_dec(x_10);
x_229 = lean_ctor_get(x_217, 1);
lean_inc(x_229);
lean_dec(x_217);
x_230 = lean_ctor_get(x_218, 1);
lean_inc(x_230);
lean_dec(x_218);
x_231 = lean_array_get_size(x_230);
x_232 = lean_nat_dec_lt(x_207, x_231);
if (x_232 == 0)
{
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_11);
x_192 = x_204;
x_193 = x_229;
goto block_197;
}
else
{
uint8_t x_233; 
x_233 = lean_nat_dec_le(x_231, x_231);
if (x_233 == 0)
{
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_11);
x_192 = x_204;
x_193 = x_229;
goto block_197;
}
else
{
lean_object* x_234; size_t x_235; size_t x_236; lean_object* x_237; 
x_234 = lean_box(0);
x_235 = 0;
x_236 = lean_usize_of_nat(x_231);
lean_dec(x_231);
lean_inc(x_204);
x_237 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_11, x_230, x_235, x_236, x_234, x_204, x_229);
lean_dec(x_230);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 1);
lean_inc(x_238);
lean_dec(x_237);
x_192 = x_204;
x_193 = x_238;
goto block_197;
}
else
{
x_198 = x_204;
x_199 = x_237;
goto block_202;
}
}
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
x_145 = x_204;
x_146 = x_205;
goto block_191;
}
}
block_245:
{
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; 
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_203 = x_240;
x_204 = x_241;
x_205 = x_243;
goto block_239;
}
else
{
lean_object* x_244; 
lean_dec(x_11);
lean_dec(x_10);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
x_192 = x_241;
x_193 = x_244;
goto block_197;
}
}
block_281:
{
if (x_247 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; 
x_249 = lean_unsigned_to_nat(0u);
x_250 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_251 = l_Lake_initPkg___elam__16___redArg___closed__31;
x_252 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_253 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_2);
x_254 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_254, 0, x_2);
x_255 = lean_box(1);
x_256 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_256, 0, x_252);
lean_ctor_set(x_256, 1, x_253);
lean_ctor_set(x_256, 2, x_251);
lean_ctor_set(x_256, 3, x_254);
lean_ctor_set(x_256, 4, x_250);
x_257 = lean_unbox(x_255);
lean_ctor_set_uint8(x_256, sizeof(void*)*5, x_257);
lean_ctor_set_uint8(x_256, sizeof(void*)*5 + 1, x_247);
x_258 = lean_unbox(x_255);
x_259 = l_Lake_proc(x_256, x_258, x_250, x_248);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
lean_dec(x_13);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_array_get_size(x_262);
x_264 = lean_nat_dec_lt(x_249, x_263);
if (x_264 == 0)
{
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_12);
x_203 = x_247;
x_204 = x_246;
x_205 = x_261;
goto block_239;
}
else
{
uint8_t x_265; 
x_265 = lean_nat_dec_le(x_263, x_263);
if (x_265 == 0)
{
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_12);
x_203 = x_247;
x_204 = x_246;
x_205 = x_261;
goto block_239;
}
else
{
lean_object* x_266; size_t x_267; size_t x_268; lean_object* x_269; 
x_266 = lean_box(0);
x_267 = 0;
x_268 = lean_usize_of_nat(x_263);
lean_dec(x_263);
lean_inc(x_246);
x_269 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_12, x_262, x_267, x_268, x_266, x_246, x_261);
lean_dec(x_262);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_203 = x_247;
x_204 = x_246;
x_205 = x_270;
goto block_239;
}
else
{
x_240 = x_247;
x_241 = x_246;
x_242 = x_269;
goto block_245;
}
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; 
lean_dec(x_12);
x_271 = lean_ctor_get(x_259, 1);
lean_inc(x_271);
lean_dec(x_259);
x_272 = lean_ctor_get(x_260, 1);
lean_inc(x_272);
lean_dec(x_260);
x_273 = lean_array_get_size(x_272);
x_274 = lean_nat_dec_lt(x_249, x_273);
if (x_274 == 0)
{
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
x_192 = x_246;
x_193 = x_271;
goto block_197;
}
else
{
uint8_t x_275; 
x_275 = lean_nat_dec_le(x_273, x_273);
if (x_275 == 0)
{
lean_dec(x_273);
lean_dec(x_272);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
x_192 = x_246;
x_193 = x_271;
goto block_197;
}
else
{
lean_object* x_276; size_t x_277; size_t x_278; lean_object* x_279; 
x_276 = lean_box(0);
x_277 = 0;
x_278 = lean_usize_of_nat(x_273);
lean_dec(x_273);
lean_inc(x_246);
x_279 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_13, x_272, x_277, x_278, x_276, x_246, x_271);
lean_dec(x_272);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; 
lean_dec(x_11);
lean_dec(x_10);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec(x_279);
x_192 = x_246;
x_193 = x_280;
goto block_197;
}
else
{
x_240 = x_247;
x_241 = x_246;
x_242 = x_279;
goto block_245;
}
}
}
}
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_145 = x_246;
x_146 = x_248;
goto block_191;
}
}
block_305:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_284 = l_Lake_initPkg___elam__16___redArg___closed__35;
x_285 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_286 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_2);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_2);
x_288 = l_Lake_initPkg___elam__16___redArg___closed__36;
x_289 = lean_box(1);
x_290 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_290, 0, x_285);
lean_ctor_set(x_290, 1, x_286);
lean_ctor_set(x_290, 2, x_284);
lean_ctor_set(x_290, 3, x_287);
lean_ctor_set(x_290, 4, x_288);
x_291 = lean_unbox(x_289);
lean_ctor_set_uint8(x_290, sizeof(void*)*5, x_291);
lean_ctor_set_uint8(x_290, sizeof(void*)*5 + 1, x_5);
x_292 = l_Lake_testProc(x_290, x_283);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = l_Lake_initPkg___elam__16___redArg___closed__38;
if (x_295 == 0)
{
uint8_t x_296; 
lean_dec(x_14);
x_296 = lean_unbox(x_293);
lean_dec(x_293);
x_246 = x_282;
x_247 = x_296;
x_248 = x_294;
goto block_281;
}
else
{
uint8_t x_297; 
x_297 = l_Lake_initPkg___elam__16___redArg___closed__39;
if (x_297 == 0)
{
uint8_t x_298; 
lean_dec(x_14);
x_298 = lean_unbox(x_293);
lean_dec(x_293);
x_246 = x_282;
x_247 = x_298;
x_248 = x_294;
goto block_281;
}
else
{
lean_object* x_299; size_t x_300; size_t x_301; lean_object* x_302; 
x_299 = lean_box(0);
x_300 = 0;
x_301 = l_Lake_initPkg___elam__16___redArg___closed__40;
lean_inc(x_282);
x_302 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_14, x_288, x_300, x_301, x_299, x_282, x_294);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; uint8_t x_304; 
x_303 = lean_ctor_get(x_302, 1);
lean_inc(x_303);
lean_dec(x_302);
x_304 = lean_unbox(x_293);
lean_dec(x_293);
x_246 = x_282;
x_247 = x_304;
x_248 = x_303;
goto block_281;
}
else
{
lean_dec(x_293);
lean_dec(x_282);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_302;
}
}
}
}
block_325:
{
lean_object* x_310; 
x_310 = l_IO_FS_writeFile(x_308, x_309, x_307);
lean_dec(x_309);
lean_dec(x_308);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; 
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec(x_310);
x_282 = x_306;
x_283 = x_311;
goto block_305;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; uint8_t x_319; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_312 = lean_ctor_get(x_310, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_310, 1);
lean_inc(x_313);
lean_dec(x_310);
x_314 = lean_io_error_to_string(x_312);
x_315 = lean_box(3);
x_316 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_316, 0, x_314);
x_317 = lean_unbox(x_315);
lean_ctor_set_uint8(x_316, sizeof(void*)*1, x_317);
x_318 = lean_apply_2(x_306, x_316, x_313);
x_319 = !lean_is_exclusive(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_318, 0);
lean_dec(x_320);
x_321 = lean_box(0);
lean_ctor_set_tag(x_318, 1);
lean_ctor_set(x_318, 0, x_321);
return x_318;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
lean_dec(x_318);
x_323 = lean_box(0);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
}
block_337:
{
if (x_328 == 0)
{
lean_object* x_330; uint8_t x_331; uint8_t x_332; 
x_330 = lean_box(4);
x_331 = lean_unbox(x_330);
x_332 = l_Lake_instDecidableEqInitTemplate(x_6, x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
x_333 = l_Lake_dotlessName(x_15);
x_334 = l_Lake_readmeFileContents(x_333);
lean_dec(x_333);
x_306 = x_326;
x_307 = x_329;
x_308 = x_327;
x_309 = x_334;
goto block_325;
}
else
{
lean_object* x_335; lean_object* x_336; 
x_335 = l_Lake_dotlessName(x_15);
x_336 = l_Lake_mathReadmeFileContents(x_335);
lean_dec(x_335);
x_306 = x_326;
x_307 = x_329;
x_308 = x_327;
x_309 = x_336;
goto block_325;
}
}
else
{
lean_dec(x_327);
lean_dec(x_15);
x_282 = x_326;
x_283 = x_329;
goto block_305;
}
}
block_356:
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_340 = l_Lake_initPkg___elam__16___redArg___closed__41;
lean_inc(x_2);
x_341 = l_Lake_joinRelative(x_2, x_340);
x_342 = l_System_FilePath_pathExists(x_341, x_339);
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
x_345 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_346 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_346 == 0)
{
uint8_t x_347; 
lean_dec(x_16);
x_347 = lean_unbox(x_343);
lean_dec(x_343);
x_326 = x_338;
x_327 = x_341;
x_328 = x_347;
x_329 = x_344;
goto block_337;
}
else
{
uint8_t x_348; 
x_348 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_348 == 0)
{
uint8_t x_349; 
lean_dec(x_16);
x_349 = lean_unbox(x_343);
lean_dec(x_343);
x_326 = x_338;
x_327 = x_341;
x_328 = x_349;
x_329 = x_344;
goto block_337;
}
else
{
lean_object* x_350; size_t x_351; size_t x_352; lean_object* x_353; 
x_350 = lean_box(0);
x_351 = 0;
x_352 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_338);
x_353 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_16, x_345, x_351, x_352, x_350, x_338, x_344);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; uint8_t x_355; 
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
lean_dec(x_353);
x_355 = lean_unbox(x_343);
lean_dec(x_343);
x_326 = x_338;
x_327 = x_341;
x_328 = x_355;
x_329 = x_354;
goto block_337;
}
else
{
lean_dec(x_343);
lean_dec(x_341);
lean_dec(x_338);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_353;
}
}
}
}
block_395:
{
if (x_358 == 0)
{
lean_object* x_360; uint8_t x_361; uint8_t x_362; 
x_360 = lean_box(1);
x_361 = lean_unbox(x_360);
x_362 = l_Lake_instDecidableEqInitTemplate(x_6, x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; 
x_363 = l_Lake_mainFileContents(x_17);
x_364 = l_IO_FS_writeFile(x_357, x_363, x_359);
lean_dec(x_363);
lean_dec(x_357);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; 
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
lean_dec(x_364);
x_338 = x_1;
x_339 = x_365;
goto block_356;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; lean_object* x_372; uint8_t x_373; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_366 = lean_ctor_get(x_364, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 1);
lean_inc(x_367);
lean_dec(x_364);
x_368 = lean_io_error_to_string(x_366);
x_369 = lean_box(3);
x_370 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_370, 0, x_368);
x_371 = lean_unbox(x_369);
lean_ctor_set_uint8(x_370, sizeof(void*)*1, x_371);
x_372 = lean_apply_2(x_1, x_370, x_367);
x_373 = !lean_is_exclusive(x_372);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; 
x_374 = lean_ctor_get(x_372, 0);
lean_dec(x_374);
x_375 = lean_box(0);
lean_ctor_set_tag(x_372, 1);
lean_ctor_set(x_372, 0, x_375);
return x_372;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_372, 1);
lean_inc(x_376);
lean_dec(x_372);
x_377 = lean_box(0);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_377);
lean_ctor_set(x_378, 1, x_376);
return x_378;
}
}
}
else
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_17);
x_379 = l_Lake_exeFileContents___closed__0;
x_380 = l_IO_FS_writeFile(x_357, x_379, x_359);
lean_dec(x_357);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
lean_dec(x_380);
x_338 = x_1;
x_339 = x_381;
goto block_356;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; uint8_t x_389; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_382 = lean_ctor_get(x_380, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
lean_dec(x_380);
x_384 = lean_io_error_to_string(x_382);
x_385 = lean_box(3);
x_386 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_386, 0, x_384);
x_387 = lean_unbox(x_385);
lean_ctor_set_uint8(x_386, sizeof(void*)*1, x_387);
x_388 = lean_apply_2(x_1, x_386, x_383);
x_389 = !lean_is_exclusive(x_388);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_388, 0);
lean_dec(x_390);
x_391 = lean_box(0);
lean_ctor_set_tag(x_388, 1);
lean_ctor_set(x_388, 0, x_391);
return x_388;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_388, 1);
lean_inc(x_392);
lean_dec(x_388);
x_393 = lean_box(0);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_393);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
}
}
else
{
lean_dec(x_357);
lean_dec(x_17);
x_338 = x_1;
x_339 = x_359;
goto block_356;
}
}
block_412:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
x_396 = l_Lake_mainFileName;
lean_inc(x_2);
x_397 = l_Lake_joinRelative(x_2, x_396);
x_398 = l_System_FilePath_pathExists(x_397, x_19);
x_399 = lean_ctor_get(x_398, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_398, 1);
lean_inc(x_400);
lean_dec(x_398);
x_401 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_402 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_402 == 0)
{
uint8_t x_403; 
lean_dec(x_18);
x_403 = lean_unbox(x_399);
lean_dec(x_399);
x_357 = x_397;
x_358 = x_403;
x_359 = x_400;
goto block_395;
}
else
{
uint8_t x_404; 
x_404 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_404 == 0)
{
uint8_t x_405; 
lean_dec(x_18);
x_405 = lean_unbox(x_399);
lean_dec(x_399);
x_357 = x_397;
x_358 = x_405;
x_359 = x_400;
goto block_395;
}
else
{
lean_object* x_406; size_t x_407; size_t x_408; lean_object* x_409; 
x_406 = lean_box(0);
x_407 = 0;
x_408 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_409 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_18, x_401, x_407, x_408, x_406, x_1, x_400);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; uint8_t x_411; 
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
lean_dec(x_409);
x_411 = lean_unbox(x_399);
lean_dec(x_399);
x_357 = x_397;
x_358 = x_411;
x_359 = x_410;
goto block_395;
}
else
{
lean_dec(x_399);
lean_dec(x_397);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_409;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; 
x_21 = l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_20);
return x_21;
}
}
static lean_object* _init_l_Lake_initPkg___at___Lake_init_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_initPkg___elam__0___boxed), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___at___Lake_init_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_174; uint8_t x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; uint8_t x_184; lean_object* x_185; lean_object* x_186; lean_object* x_204; lean_object* x_270; uint8_t x_271; 
x_12 = l_Lake_initPkg___closed__0;
x_13 = l_Lake_ConfigLang_fileExtension(x_5);
x_14 = l_System_FilePath_addExtension(x_12, x_13);
lean_dec(x_13);
lean_inc(x_2);
x_15 = l_Lake_joinRelative(x_2, x_14);
lean_dec(x_14);
x_16 = l_System_FilePath_pathExists(x_15, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lake_initPkg___at___Lake_init_spec__0___closed__0;
x_270 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_271 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_271 == 0)
{
x_204 = x_18;
goto block_269;
}
else
{
uint8_t x_272; 
x_272 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_272 == 0)
{
x_204 = x_18;
goto block_269;
}
else
{
lean_object* x_273; size_t x_274; size_t x_275; lean_object* x_276; lean_object* x_277; 
x_273 = lean_box(0);
x_274 = 0;
x_275 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_276 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_270, x_274, x_275, x_273, x_1, x_18);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
x_204 = x_277;
goto block_269;
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_42:
{
lean_object* x_26; 
x_26 = l_IO_FS_writeFile(x_23, x_25, x_21);
lean_dec(x_25);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lake_initPkg___elam__16___redArg(x_2, x_12, x_6, x_22, x_4, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_3, x_19, x_20, x_19, x_24, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_io_error_to_string(x_29);
x_32 = lean_box(3);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
x_35 = lean_apply_2(x_24, x_33, x_30);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
block_57:
{
lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_49 = lean_box(4);
x_50 = lean_unbox(x_49);
x_51 = l_Lake_instDecidableEqInitTemplate(x_4, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_box(1);
x_53 = lean_unbox(x_52);
lean_inc(x_43);
x_54 = l_Lean_Name_toString(x_43, x_53, x_46);
lean_inc(x_43);
x_55 = l_Lake_libRootFileContents(x_54, x_43);
lean_dec(x_54);
x_20 = x_43;
x_21 = x_48;
x_22 = x_44;
x_23 = x_45;
x_24 = x_47;
x_25 = x_55;
goto block_42;
}
else
{
lean_object* x_56; 
lean_dec(x_46);
lean_inc(x_43);
x_56 = l_Lake_mathLibRootFileContents(x_43);
x_20 = x_43;
x_21 = x_48;
x_22 = x_44;
x_23 = x_45;
x_24 = x_47;
x_25 = x_56;
goto block_42;
}
}
block_97:
{
if (x_64 == 0)
{
lean_object* x_66; 
x_66 = l_IO_FS_createDirAll(x_62, x_65);
lean_dec(x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lake_basicFileContents___closed__0;
x_69 = l_IO_FS_writeFile(x_58, x_68, x_67);
lean_dec(x_58);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_43 = x_59;
x_44 = x_60;
x_45 = x_61;
x_46 = x_63;
x_47 = x_1;
x_48 = x_70;
goto block_57;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_io_error_to_string(x_71);
x_74 = lean_box(3);
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
x_76 = lean_unbox(x_74);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_76);
x_77 = lean_apply_2(x_1, x_75, x_72);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set_tag(x_77, 1);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_ctor_get(x_66, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_66, 1);
lean_inc(x_85);
lean_dec(x_66);
x_86 = lean_io_error_to_string(x_84);
x_87 = lean_box(3);
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
x_89 = lean_unbox(x_87);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_89);
x_90 = lean_apply_2(x_1, x_88, x_85);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_90, 0);
lean_dec(x_92);
x_93 = lean_box(0);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_dec(x_62);
lean_dec(x_58);
x_43 = x_59;
x_44 = x_60;
x_45 = x_61;
x_46 = x_63;
x_47 = x_1;
x_48 = x_65;
goto block_57;
}
}
block_140:
{
lean_object* x_103; lean_object* x_104; 
lean_inc(x_100);
lean_inc(x_3);
x_103 = l_Lake_InitTemplate_configFileContents(x_4, x_5, x_3, x_100);
x_104 = l_IO_FS_writeFile(x_15, x_103, x_102);
lean_dec(x_103);
lean_dec(x_15);
if (lean_obj_tag(x_104) == 0)
{
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_99);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___redArg(x_1, x_2, x_12, x_6, x_98, x_4, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_3, x_19, x_100, x_19, x_105);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_101, 0);
lean_inc(x_108);
lean_dec(x_101);
x_109 = l_Lake_escapeIdent___closed__0;
lean_inc(x_108);
x_110 = l_System_FilePath_withExtension(x_108, x_109);
x_111 = l_Lake_initPkg___closed__1;
lean_inc(x_110);
x_112 = l_Lake_joinRelative(x_110, x_111);
x_113 = l_System_FilePath_pathExists(x_112, x_107);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_117 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = lean_unbox(x_114);
lean_dec(x_114);
x_58 = x_112;
x_59 = x_100;
x_60 = x_98;
x_61 = x_108;
x_62 = x_110;
x_63 = x_99;
x_64 = x_118;
x_65 = x_115;
goto block_97;
}
else
{
uint8_t x_119; 
x_119 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_119 == 0)
{
uint8_t x_120; 
x_120 = lean_unbox(x_114);
lean_dec(x_114);
x_58 = x_112;
x_59 = x_100;
x_60 = x_98;
x_61 = x_108;
x_62 = x_110;
x_63 = x_99;
x_64 = x_120;
x_65 = x_115;
goto block_97;
}
else
{
lean_object* x_121; size_t x_122; size_t x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_box(0);
x_122 = 0;
x_123 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_124 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_116, x_122, x_123, x_121, x_1, x_115);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_unbox(x_114);
lean_dec(x_114);
x_58 = x_112;
x_59 = x_100;
x_60 = x_98;
x_61 = x_108;
x_62 = x_110;
x_63 = x_99;
x_64 = x_126;
x_65 = x_125;
goto block_97;
}
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_ctor_get(x_104, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_104, 1);
lean_inc(x_128);
lean_dec(x_104);
x_129 = lean_io_error_to_string(x_127);
x_130 = lean_box(3);
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
x_132 = lean_unbox(x_130);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_132);
x_133 = lean_apply_2(x_1, x_131, x_128);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_dec(x_135);
x_136 = lean_box(0);
lean_ctor_set_tag(x_133, 1);
lean_ctor_set(x_133, 0, x_136);
return x_133;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_133, 1);
lean_inc(x_137);
lean_dec(x_133);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
block_149:
{
if (x_145 == 0)
{
lean_object* x_147; 
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_142);
x_98 = x_143;
x_99 = x_144;
x_100 = x_141;
x_101 = x_147;
x_102 = x_146;
goto block_140;
}
else
{
lean_object* x_148; 
lean_dec(x_142);
x_148 = lean_box(0);
x_98 = x_143;
x_99 = x_144;
x_100 = x_141;
x_101 = x_148;
x_102 = x_146;
goto block_140;
}
}
block_173:
{
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_153);
x_156 = l_Lake_toUpperCamelCase(x_3);
x_157 = l_Lean_modToFilePath(x_2, x_156, x_150);
lean_dec(x_150);
x_158 = l_System_FilePath_pathExists(x_157, x_151);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_162 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_162 == 0)
{
uint8_t x_163; 
x_163 = lean_unbox(x_159);
lean_dec(x_159);
x_141 = x_156;
x_142 = x_157;
x_143 = x_152;
x_144 = x_154;
x_145 = x_163;
x_146 = x_160;
goto block_149;
}
else
{
uint8_t x_164; 
x_164 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_164 == 0)
{
uint8_t x_165; 
x_165 = lean_unbox(x_159);
lean_dec(x_159);
x_141 = x_156;
x_142 = x_157;
x_143 = x_152;
x_144 = x_154;
x_145 = x_165;
x_146 = x_160;
goto block_149;
}
else
{
lean_object* x_166; size_t x_167; size_t x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_166 = lean_box(0);
x_167 = 0;
x_168 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_169 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_161, x_167, x_168, x_166, x_1, x_160);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_unbox(x_159);
lean_dec(x_159);
x_141 = x_156;
x_142 = x_157;
x_143 = x_152;
x_144 = x_154;
x_145 = x_171;
x_146 = x_170;
goto block_149;
}
}
}
else
{
lean_object* x_172; 
lean_dec(x_150);
x_172 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_172, 0, x_153);
lean_inc(x_3);
x_98 = x_152;
x_99 = x_154;
x_100 = x_3;
x_101 = x_172;
x_102 = x_151;
goto block_140;
}
}
block_183:
{
lean_object* x_180; uint8_t x_181; uint8_t x_182; 
x_180 = lean_box(1);
x_181 = lean_unbox(x_180);
x_182 = l_Lake_instDecidableEqInitTemplate(x_4, x_181);
if (x_182 == 0)
{
x_150 = x_174;
x_151 = x_179;
x_152 = x_175;
x_153 = x_176;
x_154 = x_177;
x_155 = x_178;
goto block_173;
}
else
{
x_150 = x_174;
x_151 = x_179;
x_152 = x_175;
x_153 = x_176;
x_154 = x_177;
x_155 = x_182;
goto block_173;
}
}
block_203:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_187 = l_Lake_initPkg___closed__2;
x_188 = l_Lean_modToFilePath(x_2, x_3, x_187);
x_189 = l_System_FilePath_pathExists(x_188, x_186);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_193 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_193 == 0)
{
uint8_t x_194; 
x_194 = lean_unbox(x_190);
lean_dec(x_190);
x_174 = x_187;
x_175 = x_184;
x_176 = x_188;
x_177 = x_185;
x_178 = x_194;
x_179 = x_191;
goto block_183;
}
else
{
uint8_t x_195; 
x_195 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_195 == 0)
{
uint8_t x_196; 
x_196 = lean_unbox(x_190);
lean_dec(x_190);
x_174 = x_187;
x_175 = x_184;
x_176 = x_188;
x_177 = x_185;
x_178 = x_196;
x_179 = x_191;
goto block_183;
}
else
{
lean_object* x_197; size_t x_198; size_t x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_197 = lean_box(0);
x_198 = 0;
x_199 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_200 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_192, x_198, x_199, x_197, x_1, x_191);
x_201 = lean_ctor_get(x_200, 1);
lean_inc(x_201);
lean_dec(x_200);
x_202 = lean_unbox(x_190);
lean_dec(x_190);
x_174 = x_187;
x_175 = x_184;
x_176 = x_188;
x_177 = x_185;
x_178 = x_202;
x_179 = x_201;
goto block_183;
}
}
}
block_269:
{
uint8_t x_205; 
x_205 = lean_unbox(x_17);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_206 = lean_unsigned_to_nat(0u);
x_207 = l_Lake_initPkg___elam__16___redArg___closed__5;
lean_inc(x_2);
x_208 = l_Lake_createLeanActionWorkflow(x_2, x_4, x_207, x_204);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_208, 0);
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_17);
x_212 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__0___boxed), 2, 1);
lean_closure_set(x_212, 0, x_17);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_213; lean_object* x_214; uint8_t x_215; 
lean_free_object(x_208);
x_213 = lean_ctor_get(x_210, 1);
lean_inc(x_213);
lean_dec(x_210);
x_214 = lean_array_get_size(x_213);
x_215 = lean_nat_dec_lt(x_206, x_214);
if (x_215 == 0)
{
uint8_t x_216; 
lean_dec(x_214);
lean_dec(x_213);
x_216 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_216;
x_185 = x_212;
x_186 = x_211;
goto block_203;
}
else
{
uint8_t x_217; 
x_217 = lean_nat_dec_le(x_214, x_214);
if (x_217 == 0)
{
uint8_t x_218; 
lean_dec(x_214);
lean_dec(x_213);
x_218 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_218;
x_185 = x_212;
x_186 = x_211;
goto block_203;
}
else
{
lean_object* x_219; size_t x_220; size_t x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_219 = lean_box(0);
x_220 = 0;
x_221 = lean_usize_of_nat(x_214);
lean_dec(x_214);
lean_inc(x_1);
x_222 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_213, x_220, x_221, x_219, x_1, x_211);
lean_dec(x_213);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_224;
x_185 = x_212;
x_186 = x_223;
goto block_203;
}
}
}
else
{
lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_212);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_225 = lean_ctor_get(x_210, 1);
lean_inc(x_225);
lean_dec(x_210);
x_226 = lean_array_get_size(x_225);
x_227 = lean_nat_dec_lt(x_206, x_226);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_1);
x_228 = lean_box(0);
lean_ctor_set_tag(x_208, 1);
lean_ctor_set(x_208, 0, x_228);
return x_208;
}
else
{
uint8_t x_229; 
lean_free_object(x_208);
x_229 = lean_nat_dec_le(x_226, x_226);
if (x_229 == 0)
{
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_1);
x_8 = x_211;
goto block_11;
}
else
{
lean_object* x_230; size_t x_231; size_t x_232; lean_object* x_233; lean_object* x_234; 
x_230 = lean_box(0);
x_231 = 0;
x_232 = lean_usize_of_nat(x_226);
lean_dec(x_226);
x_233 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_225, x_231, x_232, x_230, x_1, x_211);
lean_dec(x_225);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_8 = x_234;
goto block_11;
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_208, 0);
x_236 = lean_ctor_get(x_208, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_208);
lean_inc(x_17);
x_237 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__0___boxed), 2, 1);
lean_closure_set(x_237, 0, x_17);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec(x_235);
x_239 = lean_array_get_size(x_238);
x_240 = lean_nat_dec_lt(x_206, x_239);
if (x_240 == 0)
{
uint8_t x_241; 
lean_dec(x_239);
lean_dec(x_238);
x_241 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_241;
x_185 = x_237;
x_186 = x_236;
goto block_203;
}
else
{
uint8_t x_242; 
x_242 = lean_nat_dec_le(x_239, x_239);
if (x_242 == 0)
{
uint8_t x_243; 
lean_dec(x_239);
lean_dec(x_238);
x_243 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_243;
x_185 = x_237;
x_186 = x_236;
goto block_203;
}
else
{
lean_object* x_244; size_t x_245; size_t x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; 
x_244 = lean_box(0);
x_245 = 0;
x_246 = lean_usize_of_nat(x_239);
lean_dec(x_239);
lean_inc(x_1);
x_247 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_238, x_245, x_246, x_244, x_1, x_236);
lean_dec(x_238);
x_248 = lean_ctor_get(x_247, 1);
lean_inc(x_248);
lean_dec(x_247);
x_249 = lean_unbox(x_17);
lean_dec(x_17);
x_184 = x_249;
x_185 = x_237;
x_186 = x_248;
goto block_203;
}
}
}
else
{
lean_object* x_250; lean_object* x_251; uint8_t x_252; 
lean_dec(x_237);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_250 = lean_ctor_get(x_235, 1);
lean_inc(x_250);
lean_dec(x_235);
x_251 = lean_array_get_size(x_250);
x_252 = lean_nat_dec_lt(x_206, x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_1);
x_253 = lean_box(0);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_236);
return x_254;
}
else
{
uint8_t x_255; 
x_255 = lean_nat_dec_le(x_251, x_251);
if (x_255 == 0)
{
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_1);
x_8 = x_236;
goto block_11;
}
else
{
lean_object* x_256; size_t x_257; size_t x_258; lean_object* x_259; lean_object* x_260; 
x_256 = lean_box(0);
x_257 = 0;
x_258 = lean_usize_of_nat(x_251);
lean_dec(x_251);
x_259 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_250, x_257, x_258, x_256, x_1, x_236);
lean_dec(x_250);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_8 = x_260;
goto block_11;
}
}
}
}
}
else
{
lean_object* x_261; lean_object* x_262; uint8_t x_263; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_261 = l_Lake_initPkg___closed__4;
x_262 = lean_apply_2(x_1, x_261, x_204);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_262, 0);
lean_dec(x_264);
x_265 = lean_box(0);
lean_ctor_set_tag(x_262, 1);
lean_ctor_set(x_262, 0, x_265);
return x_262;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
lean_dec(x_262);
x_267 = lean_box(0);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
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
LEAN_EXPORT lean_object* l_Lake_init(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_32; lean_object* x_33; lean_object* x_78; uint8_t x_79; 
x_78 = l_Lake_escapeName_x21___closed__4;
x_79 = lean_string_dec_eq(x_1, x_78);
if (x_79 == 0)
{
x_32 = x_1;
x_33 = x_7;
goto block_77;
}
else
{
lean_object* x_80; 
lean_dec(x_1);
lean_inc(x_5);
x_80 = lean_io_realpath(x_5, x_7);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_81);
x_83 = l_System_FilePath_fileName(x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_5);
lean_dec(x_4);
x_84 = l_Lake_init___closed__0;
x_85 = lean_string_append(x_84, x_81);
lean_dec(x_81);
x_86 = l_Lake_createLeanActionWorkflow___closed__6;
x_87 = lean_string_append(x_85, x_86);
x_88 = lean_box(3);
x_89 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_89, 0, x_87);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_90);
x_91 = lean_apply_2(x_6, x_89, x_82);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
x_94 = lean_box(0);
lean_ctor_set_tag(x_91, 1);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec(x_81);
x_98 = lean_ctor_get(x_83, 0);
lean_inc(x_98);
lean_dec(x_83);
x_32 = x_98;
x_33 = x_82;
goto block_77;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; lean_object* x_105; uint8_t x_106; 
lean_dec(x_5);
lean_dec(x_4);
x_99 = lean_ctor_get(x_80, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_80, 1);
lean_inc(x_100);
lean_dec(x_80);
x_101 = lean_io_error_to_string(x_99);
x_102 = lean_box(3);
x_103 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_103, 0, x_101);
x_104 = lean_unbox(x_102);
lean_ctor_set_uint8(x_103, sizeof(void*)*1, x_104);
x_105 = lean_apply_2(x_6, x_103, x_100);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_105, 0);
lean_dec(x_107);
x_108 = lean_box(0);
lean_ctor_set_tag(x_105, 1);
lean_ctor_set(x_105, 0, x_108);
return x_105;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_105, 1);
lean_inc(x_109);
lean_dec(x_105);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_31:
{
lean_object* x_14; 
x_14 = l_IO_FS_createDirAll(x_5, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lake_stringToLegalOrSimpleName(x_12);
x_17 = l_Lake_initPkg___at___Lake_init_spec__0(x_6, x_5, x_16, x_2, x_3, x_4, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_io_error_to_string(x_18);
x_21 = lean_box(3);
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
x_24 = lean_apply_2(x_6, x_22, x_19);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
block_77:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_string_utf8_byte_size(x_32);
x_36 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_32, x_35, x_34);
x_37 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_32, x_36, x_35);
x_38 = lean_string_utf8_extract(x_32, x_36, x_37);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_32);
x_39 = l_Lake_initPkg___elam__16___redArg___closed__5;
lean_inc(x_38);
x_40 = l_Lake_validatePkgName(x_38, x_39, x_33);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_array_get_size(x_43);
x_45 = lean_nat_dec_lt(x_34, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
x_12 = x_38;
x_13 = x_42;
goto block_31;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_43);
x_12 = x_38;
x_13 = x_42;
goto block_31;
}
else
{
lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; 
x_47 = lean_box(0);
x_48 = 0;
x_49 = lean_usize_of_nat(x_44);
lean_dec(x_44);
lean_inc(x_6);
x_50 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_43, x_48, x_49, x_47, x_6, x_42);
lean_dec(x_43);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_12 = x_38;
x_13 = x_51;
goto block_31;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_38);
lean_dec(x_5);
lean_dec(x_4);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_40, 1);
x_54 = lean_ctor_get(x_40, 0);
lean_dec(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
lean_dec(x_41);
x_56 = lean_array_get_size(x_55);
x_57 = lean_nat_dec_lt(x_34, x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_6);
x_58 = lean_box(0);
lean_ctor_set_tag(x_40, 1);
lean_ctor_set(x_40, 0, x_58);
return x_40;
}
else
{
uint8_t x_59; 
lean_free_object(x_40);
x_59 = lean_nat_dec_le(x_56, x_56);
if (x_59 == 0)
{
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_6);
x_8 = x_53;
goto block_11;
}
else
{
lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_box(0);
x_61 = 0;
x_62 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_63 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_55, x_61, x_62, x_60, x_6, x_53);
lean_dec(x_55);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_8 = x_64;
goto block_11;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_dec(x_40);
x_66 = lean_ctor_get(x_41, 1);
lean_inc(x_66);
lean_dec(x_41);
x_67 = lean_array_get_size(x_66);
x_68 = lean_nat_dec_lt(x_34, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_6);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
return x_70;
}
else
{
uint8_t x_71; 
x_71 = lean_nat_dec_le(x_67, x_67);
if (x_71 == 0)
{
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_6);
x_8 = x_65;
goto block_11;
}
else
{
lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_box(0);
x_73 = 0;
x_74 = lean_usize_of_nat(x_67);
lean_dec(x_67);
x_75 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_66, x_73, x_74, x_72, x_6, x_65);
lean_dec(x_66);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_8 = x_76;
goto block_11;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___redArg___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = lean_unbox(x_6);
lean_dec(x_6);
x_22 = l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_20, x_21, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox(x_5);
lean_dec(x_5);
x_22 = lean_unbox(x_6);
lean_dec(x_6);
x_23 = l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0(x_1, x_2, x_3, x_4, x_21, x_22, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_19);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___at___Lake_init_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lake_initPkg___at___Lake_init_spec__0(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lake_init(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_new(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_1);
x_14 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_1, x_13, x_12);
x_15 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_1, x_14, x_13);
x_16 = lean_string_utf8_extract(x_1, x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_38 = l_Lake_initPkg___elam__16___redArg___closed__5;
lean_inc(x_16);
x_39 = l_Lake_validatePkgName(x_16, x_38, x_7);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_array_get_size(x_42);
x_44 = lean_nat_dec_lt(x_12, x_43);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
x_17 = x_41;
goto block_37;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_43, x_43);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
x_17 = x_41;
goto block_37;
}
else
{
lean_object* x_46; size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_box(0);
x_47 = 0;
x_48 = lean_usize_of_nat(x_43);
lean_dec(x_43);
lean_inc(x_6);
x_49 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_42, x_47, x_48, x_46, x_6, x_41);
lean_dec(x_42);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_17 = x_50;
goto block_37;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_39, 1);
x_53 = lean_ctor_get(x_39, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_40, 1);
lean_inc(x_54);
lean_dec(x_40);
x_55 = lean_array_get_size(x_54);
x_56 = lean_nat_dec_lt(x_12, x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_6);
x_57 = lean_box(0);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_57);
return x_39;
}
else
{
uint8_t x_58; 
lean_free_object(x_39);
x_58 = lean_nat_dec_le(x_55, x_55);
if (x_58 == 0)
{
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_6);
x_8 = x_52;
goto block_11;
}
else
{
lean_object* x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_box(0);
x_60 = 0;
x_61 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_62 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_54, x_60, x_61, x_59, x_6, x_52);
lean_dec(x_54);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_8 = x_63;
goto block_11;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_39, 1);
lean_inc(x_64);
lean_dec(x_39);
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_dec(x_40);
x_66 = lean_array_get_size(x_65);
x_67 = lean_nat_dec_lt(x_12, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = lean_nat_dec_le(x_66, x_66);
if (x_70 == 0)
{
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
x_8 = x_64;
goto block_11;
}
else
{
lean_object* x_71; size_t x_72; size_t x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_box(0);
x_72 = 0;
x_73 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_74 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_65, x_72, x_73, x_71, x_6, x_64);
lean_dec(x_65);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_8 = x_75;
goto block_11;
}
}
}
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
block_37:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = l_Lake_stringToLegalOrSimpleName(x_16);
lean_inc(x_18);
x_19 = l_Lake_dotlessName(x_18);
x_20 = l_Lake_joinRelative(x_5, x_19);
lean_dec(x_19);
x_21 = l_IO_FS_createDirAll(x_20, x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lake_initPkg___at___Lake_init_spec__0(x_6, x_20, x_18, x_2, x_3, x_4, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_4);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_io_error_to_string(x_24);
x_27 = lean_box(3);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
x_30 = lean_apply_2(x_6, x_28, x_25);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set_tag(x_30, 1);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lake_new(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
lean_object* initialize_Lake_Util_Git(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Sugar(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Version(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Lang(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Actions(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Init(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_Git(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Sugar(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Version(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Lang(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_defaultExeRoot___closed__0 = _init_l_Lake_defaultExeRoot___closed__0();
lean_mark_persistent(l_Lake_defaultExeRoot___closed__0);
l_Lake_defaultExeRoot___closed__1 = _init_l_Lake_defaultExeRoot___closed__1();
lean_mark_persistent(l_Lake_defaultExeRoot___closed__1);
l_Lake_defaultExeRoot = _init_l_Lake_defaultExeRoot();
lean_mark_persistent(l_Lake_defaultExeRoot);
l_Lake_gitignoreContents___closed__0 = _init_l_Lake_gitignoreContents___closed__0();
lean_mark_persistent(l_Lake_gitignoreContents___closed__0);
l_Lake_gitignoreContents = _init_l_Lake_gitignoreContents();
lean_mark_persistent(l_Lake_gitignoreContents);
l_Lake_basicFileContents___closed__0 = _init_l_Lake_basicFileContents___closed__0();
lean_mark_persistent(l_Lake_basicFileContents___closed__0);
l_Lake_basicFileContents = _init_l_Lake_basicFileContents();
lean_mark_persistent(l_Lake_basicFileContents);
l_Lake_libRootFileContents___closed__0 = _init_l_Lake_libRootFileContents___closed__0();
lean_mark_persistent(l_Lake_libRootFileContents___closed__0);
l_Lake_libRootFileContents___closed__1 = _init_l_Lake_libRootFileContents___closed__1();
lean_mark_persistent(l_Lake_libRootFileContents___closed__1);
l_Lake_libRootFileContents___closed__2 = _init_l_Lake_libRootFileContents___closed__2();
lean_mark_persistent(l_Lake_libRootFileContents___closed__2);
l_Lake_mathLibRootFileContents___closed__0 = _init_l_Lake_mathLibRootFileContents___closed__0();
lean_mark_persistent(l_Lake_mathLibRootFileContents___closed__0);
l_Lake_mathLibRootFileContents___closed__1 = _init_l_Lake_mathLibRootFileContents___closed__1();
lean_mark_persistent(l_Lake_mathLibRootFileContents___closed__1);
l_Lake_mainFileName___closed__0 = _init_l_Lake_mainFileName___closed__0();
lean_mark_persistent(l_Lake_mainFileName___closed__0);
l_Lake_mainFileName___closed__1 = _init_l_Lake_mainFileName___closed__1();
lean_mark_persistent(l_Lake_mainFileName___closed__1);
l_Lake_mainFileName___closed__2 = _init_l_Lake_mainFileName___closed__2();
lean_mark_persistent(l_Lake_mainFileName___closed__2);
l_Lake_mainFileName = _init_l_Lake_mainFileName();
lean_mark_persistent(l_Lake_mainFileName);
l_Lake_mainFileContents___closed__0 = _init_l_Lake_mainFileContents___closed__0();
lean_mark_persistent(l_Lake_mainFileContents___closed__0);
l_Lake_exeFileContents___closed__0 = _init_l_Lake_exeFileContents___closed__0();
lean_mark_persistent(l_Lake_exeFileContents___closed__0);
l_Lake_exeFileContents = _init_l_Lake_exeFileContents();
lean_mark_persistent(l_Lake_exeFileContents);
l_Lake_stdLeanConfigFileContents___closed__0 = _init_l_Lake_stdLeanConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_stdLeanConfigFileContents___closed__0);
l_Lake_stdLeanConfigFileContents___closed__1 = _init_l_Lake_stdLeanConfigFileContents___closed__1();
lean_mark_persistent(l_Lake_stdLeanConfigFileContents___closed__1);
l_Lake_stdLeanConfigFileContents___closed__2 = _init_l_Lake_stdLeanConfigFileContents___closed__2();
lean_mark_persistent(l_Lake_stdLeanConfigFileContents___closed__2);
l_Lake_stdLeanConfigFileContents___closed__3 = _init_l_Lake_stdLeanConfigFileContents___closed__3();
lean_mark_persistent(l_Lake_stdLeanConfigFileContents___closed__3);
l_Lake_stdTomlConfigFileContents___closed__0 = _init_l_Lake_stdTomlConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_stdTomlConfigFileContents___closed__0);
l_Lake_stdTomlConfigFileContents___closed__1 = _init_l_Lake_stdTomlConfigFileContents___closed__1();
lean_mark_persistent(l_Lake_stdTomlConfigFileContents___closed__1);
l_Lake_stdTomlConfigFileContents___closed__2 = _init_l_Lake_stdTomlConfigFileContents___closed__2();
lean_mark_persistent(l_Lake_stdTomlConfigFileContents___closed__2);
l_Lake_stdTomlConfigFileContents___closed__3 = _init_l_Lake_stdTomlConfigFileContents___closed__3();
lean_mark_persistent(l_Lake_stdTomlConfigFileContents___closed__3);
l_Lake_stdTomlConfigFileContents___closed__4 = _init_l_Lake_stdTomlConfigFileContents___closed__4();
lean_mark_persistent(l_Lake_stdTomlConfigFileContents___closed__4);
l_Lake_exeLeanConfigFileContents___closed__0 = _init_l_Lake_exeLeanConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_exeLeanConfigFileContents___closed__0);
l_Lake_exeTomlConfigFileContents___closed__0 = _init_l_Lake_exeTomlConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_exeTomlConfigFileContents___closed__0);
l_Lake_libLeanConfigFileContents___closed__0 = _init_l_Lake_libLeanConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_libLeanConfigFileContents___closed__0);
l_Lake_libLeanConfigFileContents___closed__1 = _init_l_Lake_libLeanConfigFileContents___closed__1();
lean_mark_persistent(l_Lake_libLeanConfigFileContents___closed__1);
l_Lake_libTomlConfigFileContents___closed__0 = _init_l_Lake_libTomlConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_libTomlConfigFileContents___closed__0);
l_Lake_mathLaxLeanConfigFileContents___closed__0 = _init_l_Lake_mathLaxLeanConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_mathLaxLeanConfigFileContents___closed__0);
l_Lake_mathLaxLeanConfigFileContents___closed__1 = _init_l_Lake_mathLaxLeanConfigFileContents___closed__1();
lean_mark_persistent(l_Lake_mathLaxLeanConfigFileContents___closed__1);
l_Lake_mathLaxTomlConfigFileContents___closed__0 = _init_l_Lake_mathLaxTomlConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_mathLaxTomlConfigFileContents___closed__0);
l_Lake_mathLaxTomlConfigFileContents___closed__1 = _init_l_Lake_mathLaxTomlConfigFileContents___closed__1();
lean_mark_persistent(l_Lake_mathLaxTomlConfigFileContents___closed__1);
l_Lake_mathLeanConfigFileContents___closed__0 = _init_l_Lake_mathLeanConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_mathLeanConfigFileContents___closed__0);
l_Lake_mathTomlConfigFileContents___closed__0 = _init_l_Lake_mathTomlConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_mathTomlConfigFileContents___closed__0);
l_Lake_readmeFileContents___closed__0 = _init_l_Lake_readmeFileContents___closed__0();
lean_mark_persistent(l_Lake_readmeFileContents___closed__0);
l_Lake_mathReadmeFileContents___closed__0 = _init_l_Lake_mathReadmeFileContents___closed__0();
lean_mark_persistent(l_Lake_mathReadmeFileContents___closed__0);
l_Lake_mathToolchainBlobUrl___closed__0 = _init_l_Lake_mathToolchainBlobUrl___closed__0();
lean_mark_persistent(l_Lake_mathToolchainBlobUrl___closed__0);
l_Lake_mathToolchainBlobUrl = _init_l_Lake_mathToolchainBlobUrl();
lean_mark_persistent(l_Lake_mathToolchainBlobUrl);
l_Lake_mathToolchainUrl___closed__0 = _init_l_Lake_mathToolchainUrl___closed__0();
lean_mark_persistent(l_Lake_mathToolchainUrl___closed__0);
l_Lake_mathToolchainUrl = _init_l_Lake_mathToolchainUrl();
lean_mark_persistent(l_Lake_mathToolchainUrl);
l_Lake_leanActionWorkflowContents___closed__0 = _init_l_Lake_leanActionWorkflowContents___closed__0();
lean_mark_persistent(l_Lake_leanActionWorkflowContents___closed__0);
l_Lake_leanActionWorkflowContents = _init_l_Lake_leanActionWorkflowContents();
lean_mark_persistent(l_Lake_leanActionWorkflowContents);
l_Lake_mathBuildActionWorkflowContents___closed__0 = _init_l_Lake_mathBuildActionWorkflowContents___closed__0();
lean_mark_persistent(l_Lake_mathBuildActionWorkflowContents___closed__0);
l_Lake_mathBuildActionWorkflowContents = _init_l_Lake_mathBuildActionWorkflowContents();
lean_mark_persistent(l_Lake_mathBuildActionWorkflowContents);
l_Lake_mathUpdateActionWorkflowContents___closed__0 = _init_l_Lake_mathUpdateActionWorkflowContents___closed__0();
lean_mark_persistent(l_Lake_mathUpdateActionWorkflowContents___closed__0);
l_Lake_mathUpdateActionWorkflowContents = _init_l_Lake_mathUpdateActionWorkflowContents();
lean_mark_persistent(l_Lake_mathUpdateActionWorkflowContents);
l_Lake_createReleaseActionWorkflowContents___closed__0 = _init_l_Lake_createReleaseActionWorkflowContents___closed__0();
lean_mark_persistent(l_Lake_createReleaseActionWorkflowContents___closed__0);
l_Lake_createReleaseActionWorkflowContents = _init_l_Lake_createReleaseActionWorkflowContents();
lean_mark_persistent(l_Lake_createReleaseActionWorkflowContents);
l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_);
l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_ = _init_l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_);
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
l_Lake_escapeIdent___closed__0 = _init_l_Lake_escapeIdent___closed__0();
lean_mark_persistent(l_Lake_escapeIdent___closed__0);
l_Lake_escapeIdent___closed__1 = _init_l_Lake_escapeIdent___closed__1();
lean_mark_persistent(l_Lake_escapeIdent___closed__1);
l_Lake_escapeIdent___closed__2 = _init_l_Lake_escapeIdent___closed__2();
lean_mark_persistent(l_Lake_escapeIdent___closed__2);
l_Lake_escapeName_x21___closed__0 = _init_l_Lake_escapeName_x21___closed__0();
lean_mark_persistent(l_Lake_escapeName_x21___closed__0);
l_Lake_escapeName_x21___closed__1 = _init_l_Lake_escapeName_x21___closed__1();
lean_mark_persistent(l_Lake_escapeName_x21___closed__1);
l_Lake_escapeName_x21___closed__2 = _init_l_Lake_escapeName_x21___closed__2();
lean_mark_persistent(l_Lake_escapeName_x21___closed__2);
l_Lake_escapeName_x21___closed__3 = _init_l_Lake_escapeName_x21___closed__3();
lean_mark_persistent(l_Lake_escapeName_x21___closed__3);
l_Lake_escapeName_x21___closed__4 = _init_l_Lake_escapeName_x21___closed__4();
lean_mark_persistent(l_Lake_escapeName_x21___closed__4);
l_Lake_escapeName_x21___closed__5 = _init_l_Lake_escapeName_x21___closed__5();
lean_mark_persistent(l_Lake_escapeName_x21___closed__5);
l_Lake_createLeanActionWorkflow___closed__0 = _init_l_Lake_createLeanActionWorkflow___closed__0();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__0);
l_Lake_createLeanActionWorkflow___closed__1 = _init_l_Lake_createLeanActionWorkflow___closed__1();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__1);
l_Lake_createLeanActionWorkflow___closed__2 = _init_l_Lake_createLeanActionWorkflow___closed__2();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__2);
l_Lake_createLeanActionWorkflow___closed__3 = _init_l_Lake_createLeanActionWorkflow___closed__3();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__3);
l_Lake_createLeanActionWorkflow___closed__4 = _init_l_Lake_createLeanActionWorkflow___closed__4();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__4);
l_Lake_createLeanActionWorkflow___closed__5 = _init_l_Lake_createLeanActionWorkflow___closed__5();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__5);
l_Lake_createLeanActionWorkflow___closed__6 = _init_l_Lake_createLeanActionWorkflow___closed__6();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__6);
l_Lake_createLeanActionWorkflow___closed__7 = _init_l_Lake_createLeanActionWorkflow___closed__7();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__7);
l_Lake_createLeanActionWorkflow___closed__8 = _init_l_Lake_createLeanActionWorkflow___closed__8();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__8);
l_Lake_createLeanActionWorkflow___closed__9 = _init_l_Lake_createLeanActionWorkflow___closed__9();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__9);
l_Lake_createLeanActionWorkflow___closed__10 = _init_l_Lake_createLeanActionWorkflow___closed__10();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__10);
l_Lake_createLeanActionWorkflow___closed__11 = _init_l_Lake_createLeanActionWorkflow___closed__11();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__11);
l_Lake_createLeanActionWorkflow___closed__12 = _init_l_Lake_createLeanActionWorkflow___closed__12();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__12);
l_Lake_createLeanActionWorkflow___closed__13 = _init_l_Lake_createLeanActionWorkflow___closed__13();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__13);
l_Lake_createLeanActionWorkflow___closed__14 = _init_l_Lake_createLeanActionWorkflow___closed__14();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__14);
l_Lake_createLeanActionWorkflow___closed__15 = _init_l_Lake_createLeanActionWorkflow___closed__15();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__15);
l_Lake_createLeanActionWorkflow___closed__16 = _init_l_Lake_createLeanActionWorkflow___closed__16();
lean_mark_persistent(l_Lake_createLeanActionWorkflow___closed__16);
l_Lake_initPkg___elam__16___redArg___closed__0 = _init_l_Lake_initPkg___elam__16___redArg___closed__0();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__0);
l_Lake_initPkg___elam__16___redArg___closed__1 = _init_l_Lake_initPkg___elam__16___redArg___closed__1();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__1);
l_Lake_initPkg___elam__16___redArg___closed__2 = _init_l_Lake_initPkg___elam__16___redArg___closed__2();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__2);
l_Lake_initPkg___elam__16___redArg___closed__3 = _init_l_Lake_initPkg___elam__16___redArg___closed__3();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__3);
l_Lake_initPkg___elam__16___redArg___closed__4 = _init_l_Lake_initPkg___elam__16___redArg___closed__4();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__4);
l_Lake_initPkg___elam__16___redArg___closed__5 = _init_l_Lake_initPkg___elam__16___redArg___closed__5();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__5);
l_Lake_initPkg___elam__16___redArg___closed__6 = _init_l_Lake_initPkg___elam__16___redArg___closed__6();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__6);
l_Lake_initPkg___elam__16___redArg___closed__7 = _init_l_Lake_initPkg___elam__16___redArg___closed__7();
l_Lake_initPkg___elam__16___redArg___closed__8 = _init_l_Lake_initPkg___elam__16___redArg___closed__8();
l_Lake_initPkg___elam__16___redArg___closed__9 = _init_l_Lake_initPkg___elam__16___redArg___closed__9();
l_Lake_initPkg___elam__16___redArg___closed__10 = _init_l_Lake_initPkg___elam__16___redArg___closed__10();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__10);
l_Lake_initPkg___elam__16___redArg___closed__11 = _init_l_Lake_initPkg___elam__16___redArg___closed__11();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__11);
l_Lake_initPkg___elam__16___redArg___closed__12 = _init_l_Lake_initPkg___elam__16___redArg___closed__12();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__12);
l_Lake_initPkg___elam__16___redArg___closed__13 = _init_l_Lake_initPkg___elam__16___redArg___closed__13();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__13);
l_Lake_initPkg___elam__16___redArg___closed__14 = _init_l_Lake_initPkg___elam__16___redArg___closed__14();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__14);
l_Lake_initPkg___elam__16___redArg___closed__15 = _init_l_Lake_initPkg___elam__16___redArg___closed__15();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__15);
l_Lake_initPkg___elam__16___redArg___closed__16 = _init_l_Lake_initPkg___elam__16___redArg___closed__16();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__16);
l_Lake_initPkg___elam__16___redArg___closed__17 = _init_l_Lake_initPkg___elam__16___redArg___closed__17();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__17);
l_Lake_initPkg___elam__16___redArg___closed__18 = _init_l_Lake_initPkg___elam__16___redArg___closed__18();
l_Lake_initPkg___elam__16___redArg___closed__19 = _init_l_Lake_initPkg___elam__16___redArg___closed__19();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__19);
l_Lake_initPkg___elam__16___redArg___closed__20 = _init_l_Lake_initPkg___elam__16___redArg___closed__20();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__20);
l_Lake_initPkg___elam__16___redArg___closed__21 = _init_l_Lake_initPkg___elam__16___redArg___closed__21();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__21);
l_Lake_initPkg___elam__16___redArg___closed__22 = _init_l_Lake_initPkg___elam__16___redArg___closed__22();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__22);
l_Lake_initPkg___elam__16___redArg___closed__23 = _init_l_Lake_initPkg___elam__16___redArg___closed__23();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__23);
l_Lake_initPkg___elam__16___redArg___closed__24 = _init_l_Lake_initPkg___elam__16___redArg___closed__24();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__24);
l_Lake_initPkg___elam__16___redArg___closed__25 = _init_l_Lake_initPkg___elam__16___redArg___closed__25();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__25);
l_Lake_initPkg___elam__16___redArg___closed__26 = _init_l_Lake_initPkg___elam__16___redArg___closed__26();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__26);
l_Lake_initPkg___elam__16___redArg___closed__27 = _init_l_Lake_initPkg___elam__16___redArg___closed__27();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__27);
l_Lake_initPkg___elam__16___redArg___closed__28 = _init_l_Lake_initPkg___elam__16___redArg___closed__28();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__28);
l_Lake_initPkg___elam__16___redArg___closed__29 = _init_l_Lake_initPkg___elam__16___redArg___closed__29();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__29);
l_Lake_initPkg___elam__16___redArg___closed__30 = _init_l_Lake_initPkg___elam__16___redArg___closed__30();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__30);
l_Lake_initPkg___elam__16___redArg___closed__31 = _init_l_Lake_initPkg___elam__16___redArg___closed__31();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__31);
l_Lake_initPkg___elam__16___redArg___closed__32 = _init_l_Lake_initPkg___elam__16___redArg___closed__32();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__32);
l_Lake_initPkg___elam__16___redArg___closed__33 = _init_l_Lake_initPkg___elam__16___redArg___closed__33();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__33);
l_Lake_initPkg___elam__16___redArg___closed__34 = _init_l_Lake_initPkg___elam__16___redArg___closed__34();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__34);
l_Lake_initPkg___elam__16___redArg___closed__35 = _init_l_Lake_initPkg___elam__16___redArg___closed__35();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__35);
l_Lake_initPkg___elam__16___redArg___closed__36 = _init_l_Lake_initPkg___elam__16___redArg___closed__36();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__36);
l_Lake_initPkg___elam__16___redArg___closed__37 = _init_l_Lake_initPkg___elam__16___redArg___closed__37();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__37);
l_Lake_initPkg___elam__16___redArg___closed__38 = _init_l_Lake_initPkg___elam__16___redArg___closed__38();
l_Lake_initPkg___elam__16___redArg___closed__39 = _init_l_Lake_initPkg___elam__16___redArg___closed__39();
l_Lake_initPkg___elam__16___redArg___closed__40 = _init_l_Lake_initPkg___elam__16___redArg___closed__40();
l_Lake_initPkg___elam__16___redArg___closed__41 = _init_l_Lake_initPkg___elam__16___redArg___closed__41();
lean_mark_persistent(l_Lake_initPkg___elam__16___redArg___closed__41);
l_Lake_initPkg___closed__0 = _init_l_Lake_initPkg___closed__0();
lean_mark_persistent(l_Lake_initPkg___closed__0);
l_Lake_initPkg___closed__1 = _init_l_Lake_initPkg___closed__1();
lean_mark_persistent(l_Lake_initPkg___closed__1);
l_Lake_initPkg___closed__2 = _init_l_Lake_initPkg___closed__2();
lean_mark_persistent(l_Lake_initPkg___closed__2);
l_Lake_initPkg___closed__3 = _init_l_Lake_initPkg___closed__3();
lean_mark_persistent(l_Lake_initPkg___closed__3);
l_Lake_initPkg___closed__4 = _init_l_Lake_initPkg___closed__4();
lean_mark_persistent(l_Lake_initPkg___closed__4);
l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__0 = _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__0();
lean_mark_persistent(l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__0);
l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1___boxed__const__1 = _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1___boxed__const__1();
lean_mark_persistent(l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1___boxed__const__1);
l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1 = _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1();
lean_mark_persistent(l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1);
l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2___boxed__const__1 = _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2___boxed__const__1();
lean_mark_persistent(l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2___boxed__const__1);
l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2 = _init_l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2();
lean_mark_persistent(l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2);
l_Lake_validatePkgName___closed__0 = _init_l_Lake_validatePkgName___closed__0();
lean_mark_persistent(l_Lake_validatePkgName___closed__0);
l_Lake_validatePkgName___closed__1 = _init_l_Lake_validatePkgName___closed__1();
lean_mark_persistent(l_Lake_validatePkgName___closed__1);
l_Lake_validatePkgName___closed__2 = _init_l_Lake_validatePkgName___closed__2();
lean_mark_persistent(l_Lake_validatePkgName___closed__2);
l_Lake_validatePkgName___closed__3 = _init_l_Lake_validatePkgName___closed__3();
lean_mark_persistent(l_Lake_validatePkgName___closed__3);
l_Lake_validatePkgName___closed__4 = _init_l_Lake_validatePkgName___closed__4();
lean_mark_persistent(l_Lake_validatePkgName___closed__4);
l_Lake_validatePkgName___closed__5 = _init_l_Lake_validatePkgName___closed__5();
lean_mark_persistent(l_Lake_validatePkgName___closed__5);
l_Lake_validatePkgName___closed__6 = _init_l_Lake_validatePkgName___closed__6();
lean_mark_persistent(l_Lake_validatePkgName___closed__6);
l_Lake_validatePkgName___closed__7 = _init_l_Lake_validatePkgName___closed__7();
lean_mark_persistent(l_Lake_validatePkgName___closed__7);
l_Lake_validatePkgName___closed__8 = _init_l_Lake_validatePkgName___closed__8();
lean_mark_persistent(l_Lake_validatePkgName___closed__8);
l_Lake_validatePkgName___closed__9 = _init_l_Lake_validatePkgName___closed__9();
lean_mark_persistent(l_Lake_validatePkgName___closed__9);
l_Lake_initPkg___at___Lake_init_spec__0___closed__0 = _init_l_Lake_initPkg___at___Lake_init_spec__0___closed__0();
lean_mark_persistent(l_Lake_initPkg___at___Lake_init_spec__0___closed__0);
l_Lake_init___closed__0 = _init_l_Lake_init___closed__0();
lean_mark_persistent(l_Lake_init___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
