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
uint8_t x_2; 
x_2 = 0;
return x_2;
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
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_alloc_closure((void*)(l_Lake_libRootFileContents___lam__0___boxed), 1, 0);
x_4 = l_Lake_libRootFileContents___closed__0;
x_5 = lean_string_append(x_4, x_1);
x_6 = l_Lake_libRootFileContents___closed__1;
x_7 = lean_string_append(x_5, x_6);
x_8 = 1;
x_9 = l_Lean_Name_toString(x_2, x_8, x_3);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = l_Lake_libRootFileContents___closed__2;
x_12 = lean_string_append(x_10, x_11);
return x_12;
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lake_mathLibRootFileContents___closed__0;
x_3 = l_Lake_mathLibRootFileContents___closed__1;
x_4 = 1;
x_5 = l_Lean_Name_toString(x_1, x_4, x_2);
x_6 = lean_string_append(x_3, x_5);
lean_dec(x_5);
x_7 = l_Lake_libRootFileContents___closed__2;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_mainFileName___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_mathLibRootFileContents___closed__0;
x_2 = 1;
x_3 = l_Lake_defaultExeRoot;
x_4 = l_Lean_Name_toString(x_3, x_2, x_1);
return x_4;
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = l_Lake_mathLibRootFileContents___closed__0;
x_3 = l_Lake_mathLibRootFileContents___closed__1;
x_4 = 1;
x_5 = l_Lean_Name_toString(x_1, x_4, x_2);
x_6 = lean_string_append(x_3, x_5);
lean_dec(x_5);
x_7 = l_Lake_mainFileContents___closed__0;
x_8 = lean_string_append(x_6, x_7);
return x_8;
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
x_40 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_3 = x_40;
goto block_9;
}
else
{
lean_object* x_41; 
x_41 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
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
x_44 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_10 = x_44;
goto block_16;
}
else
{
lean_object* x_45; 
x_45 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
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
x_48 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_17 = x_48;
goto block_23;
}
else
{
lean_object* x_49; 
x_49 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
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
x_52 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_24 = x_52;
goto block_30;
}
else
{
lean_object* x_53; 
x_53 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
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
x_56 = l_Lake_reprInitTemplate___closed__10____x40_Lake_CLI_Init___hyg_524_;
x_31 = x_56;
goto block_37;
}
else
{
lean_object* x_57; 
x_57 = l_Lake_reprInitTemplate___closed__11____x40_Lake_CLI_Init___hyg_524_;
x_31 = x_57;
goto block_37;
}
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_524_;
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
x_11 = l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_524_;
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
x_18 = l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_524_;
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
x_25 = l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_524_;
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
x_32 = l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_524_;
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
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_dec_le(x_8, x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = 2;
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_1, x_8);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 4;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 3;
return x_13;
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
uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_dotlessName___lam__0___boxed), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = l_Lean_Name_toString(x_1, x_2, x_4);
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
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lake_mathLibRootFileContents___closed__0;
x_11 = 1;
x_12 = l_Lean_Name_toString(x_4, x_11, x_10);
x_13 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_14 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_13, x_5);
x_15 = l_Lake_stdTomlConfigFileContents(x_5, x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
return x_15;
}
}
case 1:
{
lean_dec(x_4);
if (x_2 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_17 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_16, x_5);
x_18 = l_Lake_exeLeanConfigFileContents(x_5, x_17);
lean_dec(x_17);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(0u);
lean_inc(x_5);
x_20 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_19, x_5);
x_21 = l_Lake_exeTomlConfigFileContents(x_5, x_20);
lean_dec(x_20);
lean_dec(x_5);
return x_21;
}
}
case 2:
{
if (x_2 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_23 = l_Lake_libLeanConfigFileContents(x_5, x_22);
lean_dec(x_22);
lean_dec(x_5);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_24 = l_Lake_mathLibRootFileContents___closed__0;
x_25 = 1;
x_26 = l_Lean_Name_toString(x_4, x_25, x_24);
x_27 = l_Lake_libTomlConfigFileContents(x_5, x_26);
lean_dec(x_26);
lean_dec(x_5);
return x_27;
}
}
case 3:
{
if (x_2 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_29 = l_Lake_mathLaxLeanConfigFileContents(x_5, x_28);
lean_dec(x_28);
lean_dec(x_5);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = l_Lake_mathLibRootFileContents___closed__0;
x_31 = 1;
x_32 = l_Lean_Name_toString(x_4, x_31, x_30);
x_33 = l_Lake_mathLaxTomlConfigFileContents(x_5, x_32);
lean_dec(x_32);
lean_dec(x_5);
return x_33;
}
}
default: 
{
if (x_2 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = l_Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_35 = l_Lake_mathLeanConfigFileContents(x_5, x_34);
lean_dec(x_34);
lean_dec(x_5);
return x_35;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = l_Lake_mathLibRootFileContents___closed__0;
x_37 = 1;
x_38 = l_Lean_Name_toString(x_4, x_37, x_36);
x_39 = l_Lake_mathTomlConfigFileContents(x_5, x_38);
lean_dec(x_38);
lean_dec(x_5);
return x_39;
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_createLeanActionWorkflow___closed__0;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_createLeanActionWorkflow___closed__11;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_createLeanActionWorkflow___closed__13;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_createLeanActionWorkflow___closed__15;
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_createLeanActionWorkflow(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = 0;
x_6 = l_Lake_createLeanActionWorkflow___closed__1;
x_7 = lean_array_push(x_3, x_6);
x_8 = l_Lake_createLeanActionWorkflow___closed__2;
x_9 = l_Lake_joinRelative(x_1, x_8);
x_10 = l_Lake_createLeanActionWorkflow___closed__3;
x_11 = l_Lake_joinRelative(x_9, x_10);
x_12 = l_IO_FS_createDirAll(x_11, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
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
x_157 = l_System_FilePath_pathExists(x_16, x_13);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; uint8_t x_162; 
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = 4;
x_162 = l_Lake_instDecidableEqInitTemplate(x_2, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = l_Lake_leanActionWorkflowContents___closed__0;
x_164 = l_IO_FS_writeFile(x_16, x_163, x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_17 = x_7;
x_18 = x_165;
goto block_156;
}
else
{
uint8_t x_166; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
x_166 = !lean_is_exclusive(x_164);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_164, 0);
x_168 = lean_io_error_to_string(x_167);
x_169 = 3;
x_170 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set_uint8(x_170, sizeof(void*)*1, x_169);
x_171 = lean_array_get_size(x_7);
x_172 = lean_array_push(x_7, x_170);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set_tag(x_164, 0);
lean_ctor_set(x_164, 0, x_173);
return x_164;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_174 = lean_ctor_get(x_164, 0);
x_175 = lean_ctor_get(x_164, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_164);
x_176 = lean_io_error_to_string(x_174);
x_177 = 3;
x_178 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*1, x_177);
x_179 = lean_array_get_size(x_7);
x_180 = lean_array_push(x_7, x_178);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_175);
return x_182;
}
}
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = l_Lake_mathBuildActionWorkflowContents___closed__0;
x_184 = l_IO_FS_writeFile(x_16, x_183, x_160);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
x_17 = x_7;
x_18 = x_185;
goto block_156;
}
else
{
uint8_t x_186; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
x_186 = !lean_is_exclusive(x_184);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_187 = lean_ctor_get(x_184, 0);
x_188 = lean_io_error_to_string(x_187);
x_189 = 3;
x_190 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set_uint8(x_190, sizeof(void*)*1, x_189);
x_191 = lean_array_get_size(x_7);
x_192 = lean_array_push(x_7, x_190);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set_tag(x_184, 0);
lean_ctor_set(x_184, 0, x_193);
return x_184;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_194 = lean_ctor_get(x_184, 0);
x_195 = lean_ctor_get(x_184, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_184);
x_196 = lean_io_error_to_string(x_194);
x_197 = 3;
x_198 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set_uint8(x_198, sizeof(void*)*1, x_197);
x_199 = lean_array_get_size(x_7);
x_200 = lean_array_push(x_7, x_198);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_195);
return x_202;
}
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_11);
x_203 = !lean_is_exclusive(x_157);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_157, 0);
lean_dec(x_204);
x_205 = l_Lake_createLeanActionWorkflow___closed__16;
x_206 = lean_array_push(x_7, x_205);
x_207 = lean_box(0);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
lean_ctor_set(x_157, 0, x_208);
return x_157;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_157, 1);
lean_inc(x_209);
lean_dec(x_157);
x_210 = l_Lake_createLeanActionWorkflow___closed__16;
x_211 = lean_array_push(x_7, x_210);
x_212 = lean_box(0);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_211);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_209);
return x_214;
}
}
block_156:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_19 = l_Lake_createLeanActionWorkflow___closed__5;
x_20 = lean_string_append(x_19, x_16);
lean_dec(x_16);
x_21 = l_Lake_createLeanActionWorkflow___closed__6;
x_22 = lean_string_append(x_20, x_21);
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_5);
x_24 = lean_array_push(x_17, x_23);
x_25 = 4;
x_26 = l_Lake_instDecidableEqInitTemplate(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
if (lean_is_scalar(x_14)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_14;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_18);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_14);
x_30 = l_Lake_createLeanActionWorkflow___closed__7;
lean_inc(x_11);
x_31 = l_Lake_joinRelative(x_11, x_30);
x_32 = l_System_FilePath_pathExists(x_31, x_18);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Lake_mathUpdateActionWorkflowContents___closed__0;
x_37 = l_IO_FS_writeFile(x_31, x_36, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lake_createLeanActionWorkflow___closed__8;
x_40 = l_Lake_joinRelative(x_11, x_39);
x_41 = l_System_FilePath_pathExists(x_40, x_38);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lake_createLeanActionWorkflow___closed__9;
x_46 = lean_string_append(x_45, x_31);
lean_dec(x_31);
x_47 = lean_string_append(x_46, x_21);
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_5);
x_49 = lean_array_push(x_24, x_48);
x_50 = lean_unbox(x_43);
lean_dec(x_43);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_free_object(x_41);
x_51 = l_Lake_createReleaseActionWorkflowContents___closed__0;
x_52 = l_IO_FS_writeFile(x_40, x_51, x_44);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
x_55 = l_Lake_createLeanActionWorkflow___closed__10;
x_56 = lean_string_append(x_55, x_40);
lean_dec(x_40);
x_57 = lean_string_append(x_56, x_21);
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_5);
x_59 = lean_box(0);
x_60 = lean_array_push(x_49, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_52, 0, x_61);
return x_52;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_dec(x_52);
x_63 = l_Lake_createLeanActionWorkflow___closed__10;
x_64 = lean_string_append(x_63, x_40);
lean_dec(x_40);
x_65 = lean_string_append(x_64, x_21);
x_66 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*1, x_5);
x_67 = lean_box(0);
x_68 = lean_array_push(x_49, x_66);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_62);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_40);
x_71 = !lean_is_exclusive(x_52);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_52, 0);
x_73 = lean_io_error_to_string(x_72);
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = lean_array_get_size(x_49);
x_77 = lean_array_push(x_49, x_75);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set_tag(x_52, 0);
lean_ctor_set(x_52, 0, x_78);
return x_52;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_79 = lean_ctor_get(x_52, 0);
x_80 = lean_ctor_get(x_52, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_52);
x_81 = lean_io_error_to_string(x_79);
x_82 = 3;
x_83 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*1, x_82);
x_84 = lean_array_get_size(x_49);
x_85 = lean_array_push(x_49, x_83);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_80);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_40);
x_88 = l_Lake_createLeanActionWorkflow___closed__12;
x_89 = lean_array_push(x_49, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
lean_ctor_set(x_41, 0, x_91);
return x_41;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_92 = lean_ctor_get(x_41, 0);
x_93 = lean_ctor_get(x_41, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_41);
x_94 = l_Lake_createLeanActionWorkflow___closed__9;
x_95 = lean_string_append(x_94, x_31);
lean_dec(x_31);
x_96 = lean_string_append(x_95, x_21);
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_5);
x_98 = lean_array_push(x_24, x_97);
x_99 = lean_unbox(x_92);
lean_dec(x_92);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = l_Lake_createReleaseActionWorkflowContents___closed__0;
x_101 = l_IO_FS_writeFile(x_40, x_100, x_93);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_103 = x_101;
} else {
 lean_dec_ref(x_101);
 x_103 = lean_box(0);
}
x_104 = l_Lake_createLeanActionWorkflow___closed__10;
x_105 = lean_string_append(x_104, x_40);
lean_dec(x_40);
x_106 = lean_string_append(x_105, x_21);
x_107 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_5);
x_108 = lean_box(0);
x_109 = lean_array_push(x_98, x_107);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
if (lean_is_scalar(x_103)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_103;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_102);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_40);
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_101, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_114 = x_101;
} else {
 lean_dec_ref(x_101);
 x_114 = lean_box(0);
}
x_115 = lean_io_error_to_string(x_112);
x_116 = 3;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = lean_array_get_size(x_98);
x_119 = lean_array_push(x_98, x_117);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
if (lean_is_scalar(x_114)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_114;
 lean_ctor_set_tag(x_121, 0);
}
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_113);
return x_121;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_40);
x_122 = l_Lake_createLeanActionWorkflow___closed__12;
x_123 = lean_array_push(x_98, x_122);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_93);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_31);
lean_dec(x_11);
x_127 = !lean_is_exclusive(x_37);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_ctor_get(x_37, 0);
x_129 = lean_io_error_to_string(x_128);
x_130 = 3;
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_130);
x_132 = lean_array_get_size(x_24);
x_133 = lean_array_push(x_24, x_131);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set_tag(x_37, 0);
lean_ctor_set(x_37, 0, x_134);
return x_37;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_135 = lean_ctor_get(x_37, 0);
x_136 = lean_ctor_get(x_37, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_37);
x_137 = lean_io_error_to_string(x_135);
x_138 = 3;
x_139 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_138);
x_140 = lean_array_get_size(x_24);
x_141 = lean_array_push(x_24, x_139);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_136);
return x_143;
}
}
}
else
{
uint8_t x_144; 
lean_dec(x_31);
lean_dec(x_11);
x_144 = !lean_is_exclusive(x_32);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_32, 0);
lean_dec(x_145);
x_146 = l_Lake_createLeanActionWorkflow___closed__14;
x_147 = lean_array_push(x_24, x_146);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_32, 0, x_149);
return x_32;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_150 = lean_ctor_get(x_32, 1);
lean_inc(x_150);
lean_dec(x_32);
x_151 = l_Lake_createLeanActionWorkflow___closed__14;
x_152 = lean_array_push(x_24, x_151);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_150);
return x_155;
}
}
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_11);
x_215 = !lean_is_exclusive(x_12);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_216 = lean_ctor_get(x_12, 0);
x_217 = lean_io_error_to_string(x_216);
x_218 = 3;
x_219 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set_uint8(x_219, sizeof(void*)*1, x_218);
x_220 = lean_array_get_size(x_7);
x_221 = lean_array_push(x_7, x_219);
x_222 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_222, 0, x_220);
lean_ctor_set(x_222, 1, x_221);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_222);
return x_12;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_223 = lean_ctor_get(x_12, 0);
x_224 = lean_ctor_get(x_12, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_12);
x_225 = lean_io_error_to_string(x_223);
x_226 = 3;
x_227 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set_uint8(x_227, sizeof(void*)*1, x_226);
x_228 = lean_array_get_size(x_7);
x_229 = lean_array_push(x_7, x_227);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_224);
return x_231;
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__1;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__3;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__10;
x_2 = 1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___elam__16___redArg___closed__15;
x_2 = 2;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
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
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
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
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_36; lean_object* x_37; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_60; lean_object* x_61; lean_object* x_64; lean_object* x_65; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_142; lean_object* x_143; lean_object* x_184; lean_object* x_185; lean_object* x_190; lean_object* x_191; uint8_t x_195; lean_object* x_196; lean_object* x_197; uint8_t x_230; lean_object* x_231; lean_object* x_232; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_270; lean_object* x_271; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_323; lean_object* x_324; lean_object* x_342; uint8_t x_343; lean_object* x_344; lean_object* x_395; 
x_395 = lean_box(x_5);
switch (lean_obj_tag(x_395)) {
case 0:
{
goto block_394;
}
case 1:
{
goto block_394;
}
default: 
{
lean_dec(x_395);
lean_dec(x_17);
lean_dec(x_16);
x_323 = x_18;
x_324 = x_19;
goto block_341;
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
block_42:
{
uint8_t x_38; uint8_t x_39; 
x_38 = 3;
x_39 = l_Lake_instDecidableEqInitTemplate(x_5, x_38);
if (x_39 == 0)
{
uint8_t x_40; uint8_t x_41; 
x_40 = 4;
x_41 = l_Lake_instDecidableEqInitTemplate(x_5, x_40);
x_20 = x_36;
x_21 = x_37;
x_22 = x_41;
goto block_35;
}
else
{
x_20 = x_36;
x_21 = x_37;
x_22 = x_39;
goto block_35;
}
}
block_49:
{
if (x_44 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lake_initPkg___elam__16___redArg___closed__2;
lean_inc(x_43);
x_47 = lean_apply_2(x_43, x_46, x_45);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_36 = x_43;
x_37 = x_48;
goto block_42;
}
else
{
x_36 = x_43;
x_37 = x_45;
goto block_42;
}
}
block_59:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = l_Lake_initPkg___elam__16___redArg___closed__4;
x_54 = lean_apply_2(x_50, x_53, x_52);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 0, x_51);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
block_63:
{
lean_object* x_62; 
x_62 = lean_box(0);
x_50 = x_60;
x_51 = x_62;
x_52 = x_61;
goto block_59;
}
block_69:
{
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_36 = x_64;
x_37 = x_66;
goto block_42;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_50 = x_64;
x_51 = x_67;
x_52 = x_68;
goto block_59;
}
}
block_141:
{
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_8);
lean_dec(x_7);
x_74 = lean_ctor_get(x_3, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_3, 12);
lean_inc(x_75);
x_76 = lean_string_utf8_byte_size(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_eq(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_74);
lean_dec(x_6);
x_79 = l_Lake_libTomlConfigFileContents___closed__0;
x_80 = lean_string_append(x_75, x_79);
x_81 = l_IO_FS_writeFile(x_70, x_80, x_71);
lean_dec(x_80);
lean_dec(x_70);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_36 = x_72;
x_37 = x_82;
goto block_42;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_io_error_to_string(x_83);
x_86 = 3;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_apply_2(x_72, x_87, x_84);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
x_91 = lean_box(0);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_75);
x_95 = lean_ctor_get(x_74, 1);
lean_inc(x_95);
lean_dec(x_74);
x_96 = lean_string_utf8_byte_size(x_95);
lean_dec(x_95);
x_97 = lean_nat_dec_eq(x_96, x_77);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = l_System_FilePath_pathExists(x_70, x_71);
lean_dec(x_70);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_102 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_102 == 0)
{
uint8_t x_103; 
lean_dec(x_6);
x_103 = lean_unbox(x_99);
lean_dec(x_99);
x_43 = x_72;
x_44 = x_103;
x_45 = x_100;
goto block_49;
}
else
{
uint8_t x_104; 
x_104 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_104 == 0)
{
uint8_t x_105; 
lean_dec(x_6);
x_105 = lean_unbox(x_99);
lean_dec(x_99);
x_43 = x_72;
x_44 = x_105;
x_45 = x_100;
goto block_49;
}
else
{
lean_object* x_106; size_t x_107; size_t x_108; lean_object* x_109; 
x_106 = lean_box(0);
x_107 = 0;
x_108 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_72);
x_109 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_6, x_101, x_107, x_108, x_106, x_72, x_100);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_unbox(x_99);
lean_dec(x_99);
x_43 = x_72;
x_44 = x_111;
x_45 = x_110;
goto block_49;
}
else
{
lean_dec(x_99);
lean_dec(x_72);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_109;
}
}
}
}
else
{
lean_dec(x_70);
lean_dec(x_6);
x_36 = x_72;
x_37 = x_71;
goto block_42;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_6);
x_112 = l_Lake_initPkg___elam__16___redArg___closed__11;
lean_inc(x_72);
x_113 = lean_apply_2(x_72, x_112, x_71);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lake_mathToolchainBlobUrl___closed__0;
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Lake_initPkg___elam__16___redArg___closed__12;
x_118 = l_Lake_download(x_115, x_70, x_117, x_117, x_114);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_8);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_array_get_size(x_121);
x_123 = lean_nat_dec_lt(x_116, x_122);
if (x_123 == 0)
{
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_7);
x_36 = x_72;
x_37 = x_120;
goto block_42;
}
else
{
uint8_t x_124; 
x_124 = lean_nat_dec_le(x_122, x_122);
if (x_124 == 0)
{
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_7);
x_36 = x_72;
x_37 = x_120;
goto block_42;
}
else
{
lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; 
x_125 = lean_box(0);
x_126 = 0;
x_127 = lean_usize_of_nat(x_122);
lean_dec(x_122);
lean_inc(x_72);
x_128 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_7, x_121, x_126, x_127, x_125, x_72, x_120);
lean_dec(x_121);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_36 = x_72;
x_37 = x_129;
goto block_42;
}
else
{
x_64 = x_72;
x_65 = x_128;
goto block_69;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_7);
x_130 = lean_ctor_get(x_118, 1);
lean_inc(x_130);
lean_dec(x_118);
x_131 = lean_ctor_get(x_119, 1);
lean_inc(x_131);
lean_dec(x_119);
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_dec_lt(x_116, x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_box(0);
x_50 = x_72;
x_51 = x_134;
x_52 = x_130;
goto block_59;
}
else
{
uint8_t x_135; 
x_135 = lean_nat_dec_le(x_132, x_132);
if (x_135 == 0)
{
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = x_72;
x_61 = x_130;
goto block_63;
}
else
{
lean_object* x_136; size_t x_137; size_t x_138; lean_object* x_139; 
x_136 = lean_box(0);
x_137 = 0;
x_138 = lean_usize_of_nat(x_132);
lean_dec(x_132);
lean_inc(x_72);
x_139 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_8, x_131, x_137, x_138, x_136, x_72, x_130);
lean_dec(x_131);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_60 = x_72;
x_61 = x_140;
goto block_63;
}
else
{
x_64 = x_72;
x_65 = x_139;
goto block_69;
}
}
}
}
}
}
block_183:
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_144 = l_Lake_initPkg___elam__16___redArg___closed__13;
lean_inc(x_1);
x_145 = l_Lake_joinRelative(x_1, x_144);
x_146 = 4;
x_147 = lean_io_prim_handle_mk(x_145, x_146, x_143);
lean_dec(x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lake_gitignoreContents___closed__0;
x_151 = lean_io_prim_handle_put_str(x_148, x_150, x_149);
lean_dec(x_148);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = l_Lake_initPkg___elam__16___redArg___closed__14;
lean_inc(x_1);
x_154 = l_Lake_joinRelative(x_1, x_153);
x_155 = 3;
x_156 = l_Lake_instDecidableEqInitTemplate(x_5, x_155);
if (x_156 == 0)
{
uint8_t x_157; uint8_t x_158; 
x_157 = 4;
x_158 = l_Lake_instDecidableEqInitTemplate(x_5, x_157);
x_70 = x_154;
x_71 = x_152;
x_72 = x_142;
x_73 = x_158;
goto block_141;
}
else
{
x_70 = x_154;
x_71 = x_152;
x_72 = x_142;
x_73 = x_156;
goto block_141;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
lean_dec(x_151);
x_161 = lean_io_error_to_string(x_159);
x_162 = 3;
x_163 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_162);
x_164 = lean_apply_2(x_142, x_163, x_160);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_164, 0);
lean_dec(x_166);
x_167 = lean_box(0);
lean_ctor_set_tag(x_164, 1);
lean_ctor_set(x_164, 0, x_167);
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
lean_dec(x_164);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_147, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_147, 1);
lean_inc(x_172);
lean_dec(x_147);
x_173 = lean_io_error_to_string(x_171);
x_174 = 3;
x_175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
x_176 = lean_apply_2(x_142, x_175, x_172);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_176, 0);
lean_dec(x_178);
x_179 = lean_box(0);
lean_ctor_set_tag(x_176, 1);
lean_ctor_set(x_176, 0, x_179);
return x_176;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_176, 1);
lean_inc(x_180);
lean_dec(x_176);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
block_189:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = l_Lake_initPkg___elam__16___redArg___closed__16;
lean_inc(x_184);
x_187 = lean_apply_2(x_184, x_186, x_185);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_142 = x_184;
x_143 = x_188;
goto block_183;
}
block_194:
{
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_142 = x_190;
x_143 = x_192;
goto block_183;
}
else
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_184 = x_190;
x_185 = x_193;
goto block_189;
}
}
block_229:
{
uint8_t x_198; 
x_198 = l_Lake_initPkg___elam__16___redArg___closed__18;
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_201 = l_Lake_initPkg___elam__16___redArg___closed__24;
x_202 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_203 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_1);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_1);
x_205 = 1;
x_206 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_206, 0, x_202);
lean_ctor_set(x_206, 1, x_203);
lean_ctor_set(x_206, 2, x_201);
lean_ctor_set(x_206, 3, x_204);
lean_ctor_set(x_206, 4, x_200);
lean_ctor_set_uint8(x_206, sizeof(void*)*5, x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*5 + 1, x_195);
x_207 = l_Lake_proc(x_206, x_205, x_200, x_197);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_10);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_array_get_size(x_210);
x_212 = lean_nat_dec_lt(x_199, x_211);
if (x_212 == 0)
{
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_9);
x_142 = x_196;
x_143 = x_209;
goto block_183;
}
else
{
uint8_t x_213; 
x_213 = lean_nat_dec_le(x_211, x_211);
if (x_213 == 0)
{
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_9);
x_142 = x_196;
x_143 = x_209;
goto block_183;
}
else
{
lean_object* x_214; size_t x_215; size_t x_216; lean_object* x_217; 
x_214 = lean_box(0);
x_215 = 0;
x_216 = lean_usize_of_nat(x_211);
lean_dec(x_211);
lean_inc(x_196);
x_217 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_9, x_210, x_215, x_216, x_214, x_196, x_209);
lean_dec(x_210);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_142 = x_196;
x_143 = x_218;
goto block_183;
}
else
{
x_190 = x_196;
x_191 = x_217;
goto block_194;
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_9);
x_219 = lean_ctor_get(x_207, 1);
lean_inc(x_219);
lean_dec(x_207);
x_220 = lean_ctor_get(x_208, 1);
lean_inc(x_220);
lean_dec(x_208);
x_221 = lean_array_get_size(x_220);
x_222 = lean_nat_dec_lt(x_199, x_221);
if (x_222 == 0)
{
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_10);
x_184 = x_196;
x_185 = x_219;
goto block_189;
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
x_184 = x_196;
x_185 = x_219;
goto block_189;
}
else
{
lean_object* x_224; size_t x_225; size_t x_226; lean_object* x_227; 
x_224 = lean_box(0);
x_225 = 0;
x_226 = lean_usize_of_nat(x_221);
lean_dec(x_221);
lean_inc(x_196);
x_227 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_10, x_220, x_225, x_226, x_224, x_196, x_219);
lean_dec(x_220);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_184 = x_196;
x_185 = x_228;
goto block_189;
}
else
{
x_190 = x_196;
x_191 = x_227;
goto block_194;
}
}
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
x_142 = x_196;
x_143 = x_197;
goto block_183;
}
}
block_235:
{
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_195 = x_230;
x_196 = x_231;
x_197 = x_233;
goto block_229;
}
else
{
lean_object* x_234; 
lean_dec(x_10);
lean_dec(x_9);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_184 = x_231;
x_185 = x_234;
goto block_189;
}
}
block_269:
{
if (x_237 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_239 = lean_unsigned_to_nat(0u);
x_240 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_241 = l_Lake_initPkg___elam__16___redArg___closed__31;
x_242 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_243 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_1);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_1);
x_245 = 1;
x_246 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_246, 0, x_242);
lean_ctor_set(x_246, 1, x_243);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_244);
lean_ctor_set(x_246, 4, x_240);
lean_ctor_set_uint8(x_246, sizeof(void*)*5, x_245);
lean_ctor_set_uint8(x_246, sizeof(void*)*5 + 1, x_237);
x_247 = l_Lake_proc(x_246, x_245, x_240, x_238);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
lean_dec(x_12);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_array_get_size(x_250);
x_252 = lean_nat_dec_lt(x_239, x_251);
if (x_252 == 0)
{
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_11);
x_195 = x_237;
x_196 = x_236;
x_197 = x_249;
goto block_229;
}
else
{
uint8_t x_253; 
x_253 = lean_nat_dec_le(x_251, x_251);
if (x_253 == 0)
{
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_11);
x_195 = x_237;
x_196 = x_236;
x_197 = x_249;
goto block_229;
}
else
{
lean_object* x_254; size_t x_255; size_t x_256; lean_object* x_257; 
x_254 = lean_box(0);
x_255 = 0;
x_256 = lean_usize_of_nat(x_251);
lean_dec(x_251);
lean_inc(x_236);
x_257 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_11, x_250, x_255, x_256, x_254, x_236, x_249);
lean_dec(x_250);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_195 = x_237;
x_196 = x_236;
x_197 = x_258;
goto block_229;
}
else
{
x_230 = x_237;
x_231 = x_236;
x_232 = x_257;
goto block_235;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
lean_dec(x_11);
x_259 = lean_ctor_get(x_247, 1);
lean_inc(x_259);
lean_dec(x_247);
x_260 = lean_ctor_get(x_248, 1);
lean_inc(x_260);
lean_dec(x_248);
x_261 = lean_array_get_size(x_260);
x_262 = lean_nat_dec_lt(x_239, x_261);
if (x_262 == 0)
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_184 = x_236;
x_185 = x_259;
goto block_189;
}
else
{
uint8_t x_263; 
x_263 = lean_nat_dec_le(x_261, x_261);
if (x_263 == 0)
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
x_184 = x_236;
x_185 = x_259;
goto block_189;
}
else
{
lean_object* x_264; size_t x_265; size_t x_266; lean_object* x_267; 
x_264 = lean_box(0);
x_265 = 0;
x_266 = lean_usize_of_nat(x_261);
lean_dec(x_261);
lean_inc(x_236);
x_267 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_12, x_260, x_265, x_266, x_264, x_236, x_259);
lean_dec(x_260);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
lean_dec(x_10);
lean_dec(x_9);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_184 = x_236;
x_185 = x_268;
goto block_189;
}
else
{
x_230 = x_237;
x_231 = x_236;
x_232 = x_267;
goto block_235;
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
x_142 = x_236;
x_143 = x_238;
goto block_183;
}
}
block_292:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_272 = l_Lake_initPkg___elam__16___redArg___closed__35;
x_273 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_274 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_1);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_1);
x_276 = l_Lake_initPkg___elam__16___redArg___closed__36;
x_277 = 1;
x_278 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_278, 0, x_273);
lean_ctor_set(x_278, 1, x_274);
lean_ctor_set(x_278, 2, x_272);
lean_ctor_set(x_278, 3, x_275);
lean_ctor_set(x_278, 4, x_276);
lean_ctor_set_uint8(x_278, sizeof(void*)*5, x_277);
lean_ctor_set_uint8(x_278, sizeof(void*)*5 + 1, x_4);
x_279 = l_Lake_testProc(x_278, x_271);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = l_Lake_initPkg___elam__16___redArg___closed__38;
if (x_282 == 0)
{
uint8_t x_283; 
lean_dec(x_13);
x_283 = lean_unbox(x_280);
lean_dec(x_280);
x_236 = x_270;
x_237 = x_283;
x_238 = x_281;
goto block_269;
}
else
{
uint8_t x_284; 
x_284 = l_Lake_initPkg___elam__16___redArg___closed__39;
if (x_284 == 0)
{
uint8_t x_285; 
lean_dec(x_13);
x_285 = lean_unbox(x_280);
lean_dec(x_280);
x_236 = x_270;
x_237 = x_285;
x_238 = x_281;
goto block_269;
}
else
{
lean_object* x_286; size_t x_287; size_t x_288; lean_object* x_289; 
x_286 = lean_box(0);
x_287 = 0;
x_288 = l_Lake_initPkg___elam__16___redArg___closed__40;
lean_inc(x_270);
x_289 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_13, x_276, x_287, x_288, x_286, x_270, x_281);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; uint8_t x_291; 
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_unbox(x_280);
lean_dec(x_280);
x_236 = x_270;
x_237 = x_291;
x_238 = x_290;
goto block_269;
}
else
{
lean_dec(x_280);
lean_dec(x_270);
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
return x_289;
}
}
}
}
block_311:
{
lean_object* x_297; 
x_297 = l_IO_FS_writeFile(x_294, x_296, x_293);
lean_dec(x_296);
lean_dec(x_294);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
x_270 = x_295;
x_271 = x_298;
goto block_292;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
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
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
lean_dec(x_297);
x_301 = lean_io_error_to_string(x_299);
x_302 = 3;
x_303 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*1, x_302);
x_304 = lean_apply_2(x_295, x_303, x_300);
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_304, 0);
lean_dec(x_306);
x_307 = lean_box(0);
lean_ctor_set_tag(x_304, 1);
lean_ctor_set(x_304, 0, x_307);
return x_304;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_304, 1);
lean_inc(x_308);
lean_dec(x_304);
x_309 = lean_box(0);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
}
block_322:
{
if (x_314 == 0)
{
uint8_t x_316; uint8_t x_317; 
x_316 = 4;
x_317 = l_Lake_instDecidableEqInitTemplate(x_5, x_316);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; 
x_318 = l_Lake_dotlessName(x_14);
x_319 = l_Lake_readmeFileContents(x_318);
lean_dec(x_318);
x_293 = x_315;
x_294 = x_312;
x_295 = x_313;
x_296 = x_319;
goto block_311;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = l_Lake_dotlessName(x_14);
x_321 = l_Lake_mathReadmeFileContents(x_320);
lean_dec(x_320);
x_293 = x_315;
x_294 = x_312;
x_295 = x_313;
x_296 = x_321;
goto block_311;
}
}
else
{
lean_dec(x_312);
lean_dec(x_14);
x_270 = x_313;
x_271 = x_315;
goto block_292;
}
}
block_341:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_325 = l_Lake_initPkg___elam__16___redArg___closed__41;
lean_inc(x_1);
x_326 = l_Lake_joinRelative(x_1, x_325);
x_327 = l_System_FilePath_pathExists(x_326, x_324);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_331 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_331 == 0)
{
uint8_t x_332; 
lean_dec(x_15);
x_332 = lean_unbox(x_328);
lean_dec(x_328);
x_312 = x_326;
x_313 = x_323;
x_314 = x_332;
x_315 = x_329;
goto block_322;
}
else
{
uint8_t x_333; 
x_333 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_333 == 0)
{
uint8_t x_334; 
lean_dec(x_15);
x_334 = lean_unbox(x_328);
lean_dec(x_328);
x_312 = x_326;
x_313 = x_323;
x_314 = x_334;
x_315 = x_329;
goto block_322;
}
else
{
lean_object* x_335; size_t x_336; size_t x_337; lean_object* x_338; 
x_335 = lean_box(0);
x_336 = 0;
x_337 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_323);
x_338 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_15, x_330, x_336, x_337, x_335, x_323, x_329);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec(x_338);
x_340 = lean_unbox(x_328);
lean_dec(x_328);
x_312 = x_326;
x_313 = x_323;
x_314 = x_340;
x_315 = x_339;
goto block_322;
}
else
{
lean_dec(x_328);
lean_dec(x_326);
lean_dec(x_323);
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
return x_338;
}
}
}
}
block_377:
{
if (x_343 == 0)
{
uint8_t x_345; uint8_t x_346; 
x_345 = 1;
x_346 = l_Lake_instDecidableEqInitTemplate(x_5, x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = l_Lake_mainFileContents(x_16);
x_348 = l_IO_FS_writeFile(x_342, x_347, x_344);
lean_dec(x_347);
lean_dec(x_342);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
lean_dec(x_348);
x_323 = x_18;
x_324 = x_349;
goto block_341;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
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
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
lean_dec(x_348);
x_352 = lean_io_error_to_string(x_350);
x_353 = 3;
x_354 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set_uint8(x_354, sizeof(void*)*1, x_353);
x_355 = lean_apply_2(x_18, x_354, x_351);
x_356 = !lean_is_exclusive(x_355);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_355, 0);
lean_dec(x_357);
x_358 = lean_box(0);
lean_ctor_set_tag(x_355, 1);
lean_ctor_set(x_355, 0, x_358);
return x_355;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_355, 1);
lean_inc(x_359);
lean_dec(x_355);
x_360 = lean_box(0);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_16);
x_362 = l_Lake_exeFileContents___closed__0;
x_363 = l_IO_FS_writeFile(x_342, x_362, x_344);
lean_dec(x_342);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec(x_363);
x_323 = x_18;
x_324 = x_364;
goto block_341;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
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
x_365 = lean_ctor_get(x_363, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_363, 1);
lean_inc(x_366);
lean_dec(x_363);
x_367 = lean_io_error_to_string(x_365);
x_368 = 3;
x_369 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set_uint8(x_369, sizeof(void*)*1, x_368);
x_370 = lean_apply_2(x_18, x_369, x_366);
x_371 = !lean_is_exclusive(x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_370, 0);
lean_dec(x_372);
x_373 = lean_box(0);
lean_ctor_set_tag(x_370, 1);
lean_ctor_set(x_370, 0, x_373);
return x_370;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_370, 1);
lean_inc(x_374);
lean_dec(x_370);
x_375 = lean_box(0);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
}
}
else
{
lean_dec(x_342);
lean_dec(x_16);
x_323 = x_18;
x_324 = x_344;
goto block_341;
}
}
block_394:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_378 = l_Lake_mainFileName;
lean_inc(x_1);
x_379 = l_Lake_joinRelative(x_1, x_378);
x_380 = l_System_FilePath_pathExists(x_379, x_19);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_384 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_384 == 0)
{
uint8_t x_385; 
lean_dec(x_17);
x_385 = lean_unbox(x_381);
lean_dec(x_381);
x_342 = x_379;
x_343 = x_385;
x_344 = x_382;
goto block_377;
}
else
{
uint8_t x_386; 
x_386 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_386 == 0)
{
uint8_t x_387; 
lean_dec(x_17);
x_387 = lean_unbox(x_381);
lean_dec(x_381);
x_342 = x_379;
x_343 = x_387;
x_344 = x_382;
goto block_377;
}
else
{
lean_object* x_388; size_t x_389; size_t x_390; lean_object* x_391; 
x_388 = lean_box(0);
x_389 = 0;
x_390 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_18);
x_391 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_17, x_383, x_389, x_390, x_388, x_18, x_382);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; uint8_t x_393; 
x_392 = lean_ctor_get(x_391, 1);
lean_inc(x_392);
lean_dec(x_391);
x_393 = lean_unbox(x_381);
lean_dec(x_381);
x_342 = x_379;
x_343 = x_393;
x_344 = x_392;
goto block_377;
}
else
{
lean_dec(x_381);
lean_dec(x_379);
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
return x_391;
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___closed__3;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_197; lean_object* x_263; uint8_t x_264; 
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
x_263 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_264 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_264 == 0)
{
x_197 = x_18;
goto block_262;
}
else
{
uint8_t x_265; 
x_265 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_265 == 0)
{
x_197 = x_18;
goto block_262;
}
else
{
lean_object* x_266; size_t x_267; size_t x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_box(0);
x_267 = 0;
x_268 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_6);
x_269 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_263, x_267, x_268, x_266, x_6, x_18);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_197 = x_270;
goto block_262;
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
block_41:
{
lean_object* x_26; 
x_26 = l_IO_FS_writeFile(x_20, x_25, x_24);
lean_dec(x_25);
lean_dec(x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc_n(x_19, 9);
x_28 = l_Lake_initPkg___elam__16___redArg(x_1, x_12, x_5, x_21, x_3, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_2, x_19, x_23, x_19, x_22, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_23);
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
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_apply_2(x_22, x_33, x_30);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
block_54:
{
uint8_t x_48; uint8_t x_49; 
x_48 = 4;
x_49 = l_Lake_instDecidableEqInitTemplate(x_3, x_48);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_50 = 1;
lean_inc(x_45);
x_51 = l_Lean_Name_toString(x_45, x_50, x_44);
lean_inc(x_45);
x_52 = l_Lake_libRootFileContents(x_51, x_45);
lean_dec(x_51);
x_20 = x_42;
x_21 = x_43;
x_22 = x_46;
x_23 = x_45;
x_24 = x_47;
x_25 = x_52;
goto block_41;
}
else
{
lean_object* x_53; 
lean_dec(x_44);
lean_inc(x_45);
x_53 = l_Lake_mathLibRootFileContents(x_45);
x_20 = x_42;
x_21 = x_43;
x_22 = x_46;
x_23 = x_45;
x_24 = x_47;
x_25 = x_53;
goto block_41;
}
}
block_92:
{
if (x_61 == 0)
{
lean_object* x_63; 
x_63 = l_IO_FS_createDirAll(x_59, x_62);
lean_dec(x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lake_basicFileContents___closed__0;
x_66 = l_IO_FS_writeFile(x_57, x_65, x_64);
lean_dec(x_57);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_42 = x_55;
x_43 = x_56;
x_44 = x_58;
x_45 = x_60;
x_46 = x_6;
x_47 = x_67;
goto block_54;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_io_error_to_string(x_68);
x_71 = 3;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_apply_2(x_6, x_72, x_69);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_63, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_63, 1);
lean_inc(x_81);
lean_dec(x_63);
x_82 = lean_io_error_to_string(x_80);
x_83 = 3;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_apply_2(x_6, x_84, x_81);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set_tag(x_85, 1);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_dec(x_59);
lean_dec(x_57);
x_42 = x_55;
x_43 = x_56;
x_44 = x_58;
x_45 = x_60;
x_46 = x_6;
x_47 = x_62;
goto block_54;
}
}
block_134:
{
lean_object* x_98; lean_object* x_99; 
lean_inc(x_95);
lean_inc(x_2);
x_98 = l_Lake_InitTemplate_configFileContents(x_3, x_4, x_2, x_95);
x_99 = l_IO_FS_writeFile(x_15, x_98, x_97);
lean_dec(x_98);
lean_dec(x_15);
if (lean_obj_tag(x_99) == 0)
{
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
lean_inc_n(x_19, 9);
x_101 = l_Lake_initPkg___elam__16___redArg(x_1, x_12, x_5, x_93, x_3, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_2, x_19, x_95, x_19, x_6, x_100);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_ctor_get(x_96, 0);
lean_inc(x_103);
lean_dec(x_96);
x_104 = l_Lake_escapeIdent___closed__0;
lean_inc(x_103);
x_105 = l_System_FilePath_withExtension(x_103, x_104);
x_106 = l_Lake_initPkg___closed__1;
lean_inc(x_105);
x_107 = l_Lake_joinRelative(x_105, x_106);
x_108 = l_System_FilePath_pathExists(x_107, x_102);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_112 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = lean_unbox(x_109);
lean_dec(x_109);
x_55 = x_103;
x_56 = x_93;
x_57 = x_107;
x_58 = x_94;
x_59 = x_105;
x_60 = x_95;
x_61 = x_113;
x_62 = x_110;
goto block_92;
}
else
{
uint8_t x_114; 
x_114 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_114 == 0)
{
uint8_t x_115; 
x_115 = lean_unbox(x_109);
lean_dec(x_109);
x_55 = x_103;
x_56 = x_93;
x_57 = x_107;
x_58 = x_94;
x_59 = x_105;
x_60 = x_95;
x_61 = x_115;
x_62 = x_110;
goto block_92;
}
else
{
lean_object* x_116; size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = lean_box(0);
x_117 = 0;
x_118 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_6);
x_119 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_111, x_117, x_118, x_116, x_6, x_110);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_unbox(x_109);
lean_dec(x_109);
x_55 = x_103;
x_56 = x_93;
x_57 = x_107;
x_58 = x_94;
x_59 = x_105;
x_60 = x_95;
x_61 = x_121;
x_62 = x_120;
goto block_92;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_ctor_get(x_99, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_99, 1);
lean_inc(x_123);
lean_dec(x_99);
x_124 = lean_io_error_to_string(x_122);
x_125 = 3;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_apply_2(x_6, x_126, x_123);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_127, 0);
lean_dec(x_129);
x_130 = lean_box(0);
lean_ctor_set_tag(x_127, 1);
lean_ctor_set(x_127, 0, x_130);
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_dec(x_127);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
block_143:
{
if (x_139 == 0)
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_136);
x_93 = x_135;
x_94 = x_137;
x_95 = x_138;
x_96 = x_141;
x_97 = x_140;
goto block_134;
}
else
{
lean_object* x_142; 
lean_dec(x_136);
x_142 = lean_box(0);
x_93 = x_135;
x_94 = x_137;
x_95 = x_138;
x_96 = x_142;
x_97 = x_140;
goto block_134;
}
}
block_167:
{
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_146);
x_150 = l_Lake_toUpperCamelCase(x_2);
x_151 = l_Lean_modToFilePath(x_1, x_150, x_145);
lean_dec(x_145);
x_152 = l_System_FilePath_pathExists(x_151, x_148);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_156 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = lean_unbox(x_153);
lean_dec(x_153);
x_135 = x_144;
x_136 = x_151;
x_137 = x_147;
x_138 = x_150;
x_139 = x_157;
x_140 = x_154;
goto block_143;
}
else
{
uint8_t x_158; 
x_158 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = lean_unbox(x_153);
lean_dec(x_153);
x_135 = x_144;
x_136 = x_151;
x_137 = x_147;
x_138 = x_150;
x_139 = x_159;
x_140 = x_154;
goto block_143;
}
else
{
lean_object* x_160; size_t x_161; size_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_box(0);
x_161 = 0;
x_162 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_6);
x_163 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_155, x_161, x_162, x_160, x_6, x_154);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_unbox(x_153);
lean_dec(x_153);
x_135 = x_144;
x_136 = x_151;
x_137 = x_147;
x_138 = x_150;
x_139 = x_165;
x_140 = x_164;
goto block_143;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_145);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_146);
lean_inc(x_2);
x_93 = x_144;
x_94 = x_147;
x_95 = x_2;
x_96 = x_166;
x_97 = x_148;
goto block_134;
}
}
block_176:
{
uint8_t x_174; uint8_t x_175; 
x_174 = 1;
x_175 = l_Lake_instDecidableEqInitTemplate(x_3, x_174);
if (x_175 == 0)
{
x_144 = x_169;
x_145 = x_168;
x_146 = x_170;
x_147 = x_171;
x_148 = x_173;
x_149 = x_172;
goto block_167;
}
else
{
x_144 = x_169;
x_145 = x_168;
x_146 = x_170;
x_147 = x_171;
x_148 = x_173;
x_149 = x_175;
goto block_167;
}
}
block_196:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_180 = l_Lake_initPkg___closed__2;
x_181 = l_Lean_modToFilePath(x_1, x_2, x_180);
x_182 = l_System_FilePath_pathExists(x_181, x_179);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_186 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_186 == 0)
{
uint8_t x_187; 
x_187 = lean_unbox(x_183);
lean_dec(x_183);
x_168 = x_180;
x_169 = x_177;
x_170 = x_181;
x_171 = x_178;
x_172 = x_187;
x_173 = x_184;
goto block_176;
}
else
{
uint8_t x_188; 
x_188 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = lean_unbox(x_183);
lean_dec(x_183);
x_168 = x_180;
x_169 = x_177;
x_170 = x_181;
x_171 = x_178;
x_172 = x_189;
x_173 = x_184;
goto block_176;
}
else
{
lean_object* x_190; size_t x_191; size_t x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_190 = lean_box(0);
x_191 = 0;
x_192 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_6);
x_193 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_185, x_191, x_192, x_190, x_6, x_184);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_unbox(x_183);
lean_dec(x_183);
x_168 = x_180;
x_169 = x_177;
x_170 = x_181;
x_171 = x_178;
x_172 = x_195;
x_173 = x_194;
goto block_176;
}
}
}
block_262:
{
uint8_t x_198; 
x_198 = lean_unbox(x_17);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Lake_initPkg___elam__16___redArg___closed__5;
lean_inc(x_1);
x_201 = l_Lake_createLeanActionWorkflow(x_1, x_3, x_200, x_197);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_17);
x_205 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__0___boxed), 2, 1);
lean_closure_set(x_205, 0, x_17);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_free_object(x_201);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec(x_203);
x_207 = lean_array_get_size(x_206);
x_208 = lean_nat_dec_lt(x_199, x_207);
if (x_208 == 0)
{
uint8_t x_209; 
lean_dec(x_207);
lean_dec(x_206);
x_209 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_209;
x_178 = x_205;
x_179 = x_204;
goto block_196;
}
else
{
uint8_t x_210; 
x_210 = lean_nat_dec_le(x_207, x_207);
if (x_210 == 0)
{
uint8_t x_211; 
lean_dec(x_207);
lean_dec(x_206);
x_211 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_211;
x_178 = x_205;
x_179 = x_204;
goto block_196;
}
else
{
lean_object* x_212; size_t x_213; size_t x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_212 = lean_box(0);
x_213 = 0;
x_214 = lean_usize_of_nat(x_207);
lean_dec(x_207);
lean_inc(x_6);
x_215 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_206, x_213, x_214, x_212, x_6, x_204);
lean_dec(x_206);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_217;
x_178 = x_205;
x_179 = x_216;
goto block_196;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
lean_dec(x_205);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_218 = lean_ctor_get(x_203, 1);
lean_inc(x_218);
lean_dec(x_203);
x_219 = lean_array_get_size(x_218);
x_220 = lean_nat_dec_lt(x_199, x_219);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_6);
x_221 = lean_box(0);
lean_ctor_set_tag(x_201, 1);
lean_ctor_set(x_201, 0, x_221);
return x_201;
}
else
{
uint8_t x_222; 
lean_free_object(x_201);
x_222 = lean_nat_dec_le(x_219, x_219);
if (x_222 == 0)
{
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_6);
x_8 = x_204;
goto block_11;
}
else
{
lean_object* x_223; size_t x_224; size_t x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_box(0);
x_224 = 0;
x_225 = lean_usize_of_nat(x_219);
lean_dec(x_219);
x_226 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_218, x_224, x_225, x_223, x_6, x_204);
lean_dec(x_218);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_8 = x_227;
goto block_11;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_201, 0);
x_229 = lean_ctor_get(x_201, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_201);
lean_inc(x_17);
x_230 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__0___boxed), 2, 1);
lean_closure_set(x_230, 0, x_17);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_array_get_size(x_231);
x_233 = lean_nat_dec_lt(x_199, x_232);
if (x_233 == 0)
{
uint8_t x_234; 
lean_dec(x_232);
lean_dec(x_231);
x_234 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_234;
x_178 = x_230;
x_179 = x_229;
goto block_196;
}
else
{
uint8_t x_235; 
x_235 = lean_nat_dec_le(x_232, x_232);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_232);
lean_dec(x_231);
x_236 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_236;
x_178 = x_230;
x_179 = x_229;
goto block_196;
}
else
{
lean_object* x_237; size_t x_238; size_t x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_237 = lean_box(0);
x_238 = 0;
x_239 = lean_usize_of_nat(x_232);
lean_dec(x_232);
lean_inc(x_6);
x_240 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_231, x_238, x_239, x_237, x_6, x_229);
lean_dec(x_231);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_242;
x_178 = x_230;
x_179 = x_241;
goto block_196;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
lean_dec(x_230);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_243 = lean_ctor_get(x_228, 1);
lean_inc(x_243);
lean_dec(x_228);
x_244 = lean_array_get_size(x_243);
x_245 = lean_nat_dec_lt(x_199, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_6);
x_246 = lean_box(0);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_229);
return x_247;
}
else
{
uint8_t x_248; 
x_248 = lean_nat_dec_le(x_244, x_244);
if (x_248 == 0)
{
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_6);
x_8 = x_229;
goto block_11;
}
else
{
lean_object* x_249; size_t x_250; size_t x_251; lean_object* x_252; lean_object* x_253; 
x_249 = lean_box(0);
x_250 = 0;
x_251 = lean_usize_of_nat(x_244);
lean_dec(x_244);
x_252 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_243, x_250, x_251, x_249, x_6, x_229);
lean_dec(x_243);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_8 = x_253;
goto block_11;
}
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_254 = l_Lake_initPkg___closed__4;
x_255 = lean_apply_2(x_6, x_254, x_197);
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_255, 0);
lean_dec(x_257);
x_258 = lean_box(0);
lean_ctor_set_tag(x_255, 1);
lean_ctor_set(x_255, 0, x_258);
return x_255;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
x_260 = lean_box(0);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
return x_261;
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_validatePkgName___closed__8;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_validatePkgName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_15; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_string_utf8_byte_size(x_1);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_String_anyAux___at___Lake_validatePkgName_spec__1(x_34, x_1, x_32, x_33);
lean_dec(x_32);
if (x_35 == 0)
{
goto block_14;
}
else
{
x_15 = x_34;
goto block_31;
}
}
else
{
lean_dec(x_32);
x_15 = x_34;
goto block_31;
}
block_14:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lake_validatePkgName___closed__0;
x_5 = lean_string_append(x_4, x_1);
lean_dec(x_1);
x_6 = l_Lake_createLeanActionWorkflow___closed__6;
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
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
block_31:
{
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_string_utf8_byte_size(x_1);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_String_anyAux___at___Lake_validatePkgName_spec__0(x_1, x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = l_Lake_validatePkgName___closed__1;
x_20 = l_String_mapAux___at___Lake_envToBool_x3f_spec__0(x_17, x_1);
x_21 = l_Lake_validatePkgName___closed__7;
x_22 = l_List_elem___redArg(x_19, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = l_Lake_validatePkgName___closed__9;
x_27 = lean_array_get_size(x_2);
x_28 = lean_array_push(x_2, x_26);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
}
else
{
goto block_14;
}
}
else
{
goto block_14;
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
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_36; lean_object* x_37; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_60; lean_object* x_61; lean_object* x_64; lean_object* x_65; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_142; lean_object* x_143; lean_object* x_184; lean_object* x_185; lean_object* x_190; lean_object* x_191; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_230; uint8_t x_231; lean_object* x_232; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_270; lean_object* x_271; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_312; lean_object* x_313; uint8_t x_314; lean_object* x_315; lean_object* x_323; lean_object* x_324; lean_object* x_342; uint8_t x_343; lean_object* x_344; lean_object* x_395; 
x_395 = lean_box(x_6);
switch (lean_obj_tag(x_395)) {
case 0:
{
goto block_394;
}
case 1:
{
goto block_394;
}
default: 
{
lean_dec(x_395);
lean_dec(x_18);
lean_dec(x_17);
x_323 = x_1;
x_324 = x_19;
goto block_341;
}
}
block_35:
{
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
x_34 = l_Lake_updateManifest(x_33, x_30, x_20, x_21);
return x_34;
}
}
block_42:
{
uint8_t x_38; uint8_t x_39; 
x_38 = 3;
x_39 = l_Lake_instDecidableEqInitTemplate(x_6, x_38);
if (x_39 == 0)
{
uint8_t x_40; uint8_t x_41; 
x_40 = 4;
x_41 = l_Lake_instDecidableEqInitTemplate(x_6, x_40);
x_20 = x_36;
x_21 = x_37;
x_22 = x_41;
goto block_35;
}
else
{
x_20 = x_36;
x_21 = x_37;
x_22 = x_39;
goto block_35;
}
}
block_49:
{
if (x_44 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lake_initPkg___elam__16___redArg___closed__2;
lean_inc(x_43);
x_47 = lean_apply_2(x_43, x_46, x_45);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_36 = x_43;
x_37 = x_48;
goto block_42;
}
else
{
x_36 = x_43;
x_37 = x_45;
goto block_42;
}
}
block_59:
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = l_Lake_initPkg___elam__16___redArg___closed__4;
x_54 = lean_apply_2(x_50, x_53, x_52);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 0, x_51);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_51);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
block_63:
{
lean_object* x_62; 
x_62 = lean_box(0);
x_50 = x_60;
x_51 = x_62;
x_52 = x_61;
goto block_59;
}
block_69:
{
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_36 = x_64;
x_37 = x_66;
goto block_42;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_50 = x_64;
x_51 = x_67;
x_52 = x_68;
goto block_59;
}
}
block_141:
{
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
lean_dec(x_9);
lean_dec(x_8);
x_74 = lean_ctor_get(x_4, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_4, 12);
lean_inc(x_75);
x_76 = lean_string_utf8_byte_size(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_eq(x_76, x_77);
lean_dec(x_76);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_74);
lean_dec(x_7);
x_79 = l_Lake_libTomlConfigFileContents___closed__0;
x_80 = lean_string_append(x_75, x_79);
x_81 = l_IO_FS_writeFile(x_72, x_80, x_71);
lean_dec(x_80);
lean_dec(x_72);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_36 = x_70;
x_37 = x_82;
goto block_42;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_io_error_to_string(x_83);
x_86 = 3;
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_apply_2(x_70, x_87, x_84);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
lean_dec(x_90);
x_91 = lean_box(0);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_88, 1);
lean_inc(x_92);
lean_dec(x_88);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_75);
x_95 = lean_ctor_get(x_74, 1);
lean_inc(x_95);
lean_dec(x_74);
x_96 = lean_string_utf8_byte_size(x_95);
lean_dec(x_95);
x_97 = lean_nat_dec_eq(x_96, x_77);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_98 = l_System_FilePath_pathExists(x_72, x_71);
lean_dec(x_72);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_102 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_102 == 0)
{
uint8_t x_103; 
lean_dec(x_7);
x_103 = lean_unbox(x_99);
lean_dec(x_99);
x_43 = x_70;
x_44 = x_103;
x_45 = x_100;
goto block_49;
}
else
{
uint8_t x_104; 
x_104 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_104 == 0)
{
uint8_t x_105; 
lean_dec(x_7);
x_105 = lean_unbox(x_99);
lean_dec(x_99);
x_43 = x_70;
x_44 = x_105;
x_45 = x_100;
goto block_49;
}
else
{
lean_object* x_106; size_t x_107; size_t x_108; lean_object* x_109; 
x_106 = lean_box(0);
x_107 = 0;
x_108 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_70);
x_109 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_7, x_101, x_107, x_108, x_106, x_70, x_100);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; uint8_t x_111; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_unbox(x_99);
lean_dec(x_99);
x_43 = x_70;
x_44 = x_111;
x_45 = x_110;
goto block_49;
}
else
{
lean_dec(x_99);
lean_dec(x_70);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_109;
}
}
}
}
else
{
lean_dec(x_72);
lean_dec(x_7);
x_36 = x_70;
x_37 = x_71;
goto block_42;
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_7);
x_112 = l_Lake_initPkg___elam__16___redArg___closed__11;
lean_inc(x_70);
x_113 = lean_apply_2(x_70, x_112, x_71);
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
lean_dec(x_113);
x_115 = l_Lake_mathToolchainBlobUrl___closed__0;
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Lake_initPkg___elam__16___redArg___closed__12;
x_118 = l_Lake_download(x_115, x_72, x_117, x_117, x_114);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
lean_dec(x_9);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_array_get_size(x_121);
x_123 = lean_nat_dec_lt(x_116, x_122);
if (x_123 == 0)
{
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_8);
x_36 = x_70;
x_37 = x_120;
goto block_42;
}
else
{
uint8_t x_124; 
x_124 = lean_nat_dec_le(x_122, x_122);
if (x_124 == 0)
{
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_8);
x_36 = x_70;
x_37 = x_120;
goto block_42;
}
else
{
lean_object* x_125; size_t x_126; size_t x_127; lean_object* x_128; 
x_125 = lean_box(0);
x_126 = 0;
x_127 = lean_usize_of_nat(x_122);
lean_dec(x_122);
lean_inc(x_70);
x_128 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_8, x_121, x_126, x_127, x_125, x_70, x_120);
lean_dec(x_121);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_36 = x_70;
x_37 = x_129;
goto block_42;
}
else
{
x_64 = x_70;
x_65 = x_128;
goto block_69;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
lean_dec(x_8);
x_130 = lean_ctor_get(x_118, 1);
lean_inc(x_130);
lean_dec(x_118);
x_131 = lean_ctor_get(x_119, 1);
lean_inc(x_131);
lean_dec(x_119);
x_132 = lean_array_get_size(x_131);
x_133 = lean_nat_dec_lt(x_116, x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_134 = lean_box(0);
x_50 = x_70;
x_51 = x_134;
x_52 = x_130;
goto block_59;
}
else
{
uint8_t x_135; 
x_135 = lean_nat_dec_le(x_132, x_132);
if (x_135 == 0)
{
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = x_70;
x_61 = x_130;
goto block_63;
}
else
{
lean_object* x_136; size_t x_137; size_t x_138; lean_object* x_139; 
x_136 = lean_box(0);
x_137 = 0;
x_138 = lean_usize_of_nat(x_132);
lean_dec(x_132);
lean_inc(x_70);
x_139 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_9, x_131, x_137, x_138, x_136, x_70, x_130);
lean_dec(x_131);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_60 = x_70;
x_61 = x_140;
goto block_63;
}
else
{
x_64 = x_70;
x_65 = x_139;
goto block_69;
}
}
}
}
}
}
block_183:
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_144 = l_Lake_initPkg___elam__16___redArg___closed__13;
lean_inc(x_2);
x_145 = l_Lake_joinRelative(x_2, x_144);
x_146 = 4;
x_147 = lean_io_prim_handle_mk(x_145, x_146, x_143);
lean_dec(x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = l_Lake_gitignoreContents___closed__0;
x_151 = lean_io_prim_handle_put_str(x_148, x_150, x_149);
lean_dec(x_148);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; uint8_t x_156; 
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = l_Lake_initPkg___elam__16___redArg___closed__14;
lean_inc(x_2);
x_154 = l_Lake_joinRelative(x_2, x_153);
x_155 = 3;
x_156 = l_Lake_instDecidableEqInitTemplate(x_6, x_155);
if (x_156 == 0)
{
uint8_t x_157; uint8_t x_158; 
x_157 = 4;
x_158 = l_Lake_instDecidableEqInitTemplate(x_6, x_157);
x_70 = x_142;
x_71 = x_152;
x_72 = x_154;
x_73 = x_158;
goto block_141;
}
else
{
x_70 = x_142;
x_71 = x_152;
x_72 = x_154;
x_73 = x_156;
goto block_141;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_159 = lean_ctor_get(x_151, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
lean_dec(x_151);
x_161 = lean_io_error_to_string(x_159);
x_162 = 3;
x_163 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_162);
x_164 = lean_apply_2(x_142, x_163, x_160);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_164, 0);
lean_dec(x_166);
x_167 = lean_box(0);
lean_ctor_set_tag(x_164, 1);
lean_ctor_set(x_164, 0, x_167);
return x_164;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
lean_dec(x_164);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_171 = lean_ctor_get(x_147, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_147, 1);
lean_inc(x_172);
lean_dec(x_147);
x_173 = lean_io_error_to_string(x_171);
x_174 = 3;
x_175 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set_uint8(x_175, sizeof(void*)*1, x_174);
x_176 = lean_apply_2(x_142, x_175, x_172);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_176, 0);
lean_dec(x_178);
x_179 = lean_box(0);
lean_ctor_set_tag(x_176, 1);
lean_ctor_set(x_176, 0, x_179);
return x_176;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_176, 1);
lean_inc(x_180);
lean_dec(x_176);
x_181 = lean_box(0);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
block_189:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = l_Lake_initPkg___elam__16___redArg___closed__16;
lean_inc(x_184);
x_187 = lean_apply_2(x_184, x_186, x_185);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
lean_dec(x_187);
x_142 = x_184;
x_143 = x_188;
goto block_183;
}
block_194:
{
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_142 = x_190;
x_143 = x_192;
goto block_183;
}
else
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_184 = x_190;
x_185 = x_193;
goto block_189;
}
}
block_229:
{
uint8_t x_198; 
x_198 = l_Lake_initPkg___elam__16___redArg___closed__18;
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_201 = l_Lake_initPkg___elam__16___redArg___closed__24;
x_202 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_203 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_2);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_2);
x_205 = 1;
x_206 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_206, 0, x_202);
lean_ctor_set(x_206, 1, x_203);
lean_ctor_set(x_206, 2, x_201);
lean_ctor_set(x_206, 3, x_204);
lean_ctor_set(x_206, 4, x_200);
lean_ctor_set_uint8(x_206, sizeof(void*)*5, x_205);
lean_ctor_set_uint8(x_206, sizeof(void*)*5 + 1, x_196);
x_207 = l_Lake_proc(x_206, x_205, x_200, x_197);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_11);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_array_get_size(x_210);
x_212 = lean_nat_dec_lt(x_199, x_211);
if (x_212 == 0)
{
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_10);
x_142 = x_195;
x_143 = x_209;
goto block_183;
}
else
{
uint8_t x_213; 
x_213 = lean_nat_dec_le(x_211, x_211);
if (x_213 == 0)
{
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_10);
x_142 = x_195;
x_143 = x_209;
goto block_183;
}
else
{
lean_object* x_214; size_t x_215; size_t x_216; lean_object* x_217; 
x_214 = lean_box(0);
x_215 = 0;
x_216 = lean_usize_of_nat(x_211);
lean_dec(x_211);
lean_inc(x_195);
x_217 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_10, x_210, x_215, x_216, x_214, x_195, x_209);
lean_dec(x_210);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
lean_dec(x_217);
x_142 = x_195;
x_143 = x_218;
goto block_183;
}
else
{
x_190 = x_195;
x_191 = x_217;
goto block_194;
}
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
lean_dec(x_10);
x_219 = lean_ctor_get(x_207, 1);
lean_inc(x_219);
lean_dec(x_207);
x_220 = lean_ctor_get(x_208, 1);
lean_inc(x_220);
lean_dec(x_208);
x_221 = lean_array_get_size(x_220);
x_222 = lean_nat_dec_lt(x_199, x_221);
if (x_222 == 0)
{
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_11);
x_184 = x_195;
x_185 = x_219;
goto block_189;
}
else
{
uint8_t x_223; 
x_223 = lean_nat_dec_le(x_221, x_221);
if (x_223 == 0)
{
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_11);
x_184 = x_195;
x_185 = x_219;
goto block_189;
}
else
{
lean_object* x_224; size_t x_225; size_t x_226; lean_object* x_227; 
x_224 = lean_box(0);
x_225 = 0;
x_226 = lean_usize_of_nat(x_221);
lean_dec(x_221);
lean_inc(x_195);
x_227 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_11, x_220, x_225, x_226, x_224, x_195, x_219);
lean_dec(x_220);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 1);
lean_inc(x_228);
lean_dec(x_227);
x_184 = x_195;
x_185 = x_228;
goto block_189;
}
else
{
x_190 = x_195;
x_191 = x_227;
goto block_194;
}
}
}
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
x_142 = x_195;
x_143 = x_197;
goto block_183;
}
}
block_235:
{
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; 
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_195 = x_230;
x_196 = x_231;
x_197 = x_233;
goto block_229;
}
else
{
lean_object* x_234; 
lean_dec(x_11);
lean_dec(x_10);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_184 = x_230;
x_185 = x_234;
goto block_189;
}
}
block_269:
{
if (x_237 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_239 = lean_unsigned_to_nat(0u);
x_240 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_241 = l_Lake_initPkg___elam__16___redArg___closed__31;
x_242 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_243 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_2);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_2);
x_245 = 1;
x_246 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_246, 0, x_242);
lean_ctor_set(x_246, 1, x_243);
lean_ctor_set(x_246, 2, x_241);
lean_ctor_set(x_246, 3, x_244);
lean_ctor_set(x_246, 4, x_240);
lean_ctor_set_uint8(x_246, sizeof(void*)*5, x_245);
lean_ctor_set_uint8(x_246, sizeof(void*)*5 + 1, x_237);
x_247 = l_Lake_proc(x_246, x_245, x_240, x_238);
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
lean_dec(x_13);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
x_251 = lean_array_get_size(x_250);
x_252 = lean_nat_dec_lt(x_239, x_251);
if (x_252 == 0)
{
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_12);
x_195 = x_236;
x_196 = x_237;
x_197 = x_249;
goto block_229;
}
else
{
uint8_t x_253; 
x_253 = lean_nat_dec_le(x_251, x_251);
if (x_253 == 0)
{
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_12);
x_195 = x_236;
x_196 = x_237;
x_197 = x_249;
goto block_229;
}
else
{
lean_object* x_254; size_t x_255; size_t x_256; lean_object* x_257; 
x_254 = lean_box(0);
x_255 = 0;
x_256 = lean_usize_of_nat(x_251);
lean_dec(x_251);
lean_inc(x_236);
x_257 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_12, x_250, x_255, x_256, x_254, x_236, x_249);
lean_dec(x_250);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_195 = x_236;
x_196 = x_237;
x_197 = x_258;
goto block_229;
}
else
{
x_230 = x_236;
x_231 = x_237;
x_232 = x_257;
goto block_235;
}
}
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
lean_dec(x_12);
x_259 = lean_ctor_get(x_247, 1);
lean_inc(x_259);
lean_dec(x_247);
x_260 = lean_ctor_get(x_248, 1);
lean_inc(x_260);
lean_dec(x_248);
x_261 = lean_array_get_size(x_260);
x_262 = lean_nat_dec_lt(x_239, x_261);
if (x_262 == 0)
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
x_184 = x_236;
x_185 = x_259;
goto block_189;
}
else
{
uint8_t x_263; 
x_263 = lean_nat_dec_le(x_261, x_261);
if (x_263 == 0)
{
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
x_184 = x_236;
x_185 = x_259;
goto block_189;
}
else
{
lean_object* x_264; size_t x_265; size_t x_266; lean_object* x_267; 
x_264 = lean_box(0);
x_265 = 0;
x_266 = lean_usize_of_nat(x_261);
lean_dec(x_261);
lean_inc(x_236);
x_267 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_13, x_260, x_265, x_266, x_264, x_236, x_259);
lean_dec(x_260);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; 
lean_dec(x_11);
lean_dec(x_10);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_184 = x_236;
x_185 = x_268;
goto block_189;
}
else
{
x_230 = x_236;
x_231 = x_237;
x_232 = x_267;
goto block_235;
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
x_142 = x_236;
x_143 = x_238;
goto block_183;
}
}
block_292:
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_272 = l_Lake_initPkg___elam__16___redArg___closed__35;
x_273 = l_Lake_initPkg___elam__16___redArg___closed__25;
x_274 = l_Lake_initPkg___elam__16___redArg___closed__26;
lean_inc(x_2);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_2);
x_276 = l_Lake_initPkg___elam__16___redArg___closed__36;
x_277 = 1;
x_278 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_278, 0, x_273);
lean_ctor_set(x_278, 1, x_274);
lean_ctor_set(x_278, 2, x_272);
lean_ctor_set(x_278, 3, x_275);
lean_ctor_set(x_278, 4, x_276);
lean_ctor_set_uint8(x_278, sizeof(void*)*5, x_277);
lean_ctor_set_uint8(x_278, sizeof(void*)*5 + 1, x_5);
x_279 = l_Lake_testProc(x_278, x_271);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
lean_dec(x_279);
x_282 = l_Lake_initPkg___elam__16___redArg___closed__38;
if (x_282 == 0)
{
uint8_t x_283; 
lean_dec(x_14);
x_283 = lean_unbox(x_280);
lean_dec(x_280);
x_236 = x_270;
x_237 = x_283;
x_238 = x_281;
goto block_269;
}
else
{
uint8_t x_284; 
x_284 = l_Lake_initPkg___elam__16___redArg___closed__39;
if (x_284 == 0)
{
uint8_t x_285; 
lean_dec(x_14);
x_285 = lean_unbox(x_280);
lean_dec(x_280);
x_236 = x_270;
x_237 = x_285;
x_238 = x_281;
goto block_269;
}
else
{
lean_object* x_286; size_t x_287; size_t x_288; lean_object* x_289; 
x_286 = lean_box(0);
x_287 = 0;
x_288 = l_Lake_initPkg___elam__16___redArg___closed__40;
lean_inc(x_270);
x_289 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_14, x_276, x_287, x_288, x_286, x_270, x_281);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; uint8_t x_291; 
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
x_291 = lean_unbox(x_280);
lean_dec(x_280);
x_236 = x_270;
x_237 = x_291;
x_238 = x_290;
goto block_269;
}
else
{
lean_dec(x_280);
lean_dec(x_270);
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
return x_289;
}
}
}
}
block_311:
{
lean_object* x_297; 
x_297 = l_IO_FS_writeFile(x_294, x_296, x_295);
lean_dec(x_296);
lean_dec(x_294);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
x_270 = x_293;
x_271 = x_298;
goto block_292;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
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
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
lean_dec(x_297);
x_301 = lean_io_error_to_string(x_299);
x_302 = 3;
x_303 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set_uint8(x_303, sizeof(void*)*1, x_302);
x_304 = lean_apply_2(x_293, x_303, x_300);
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_304, 0);
lean_dec(x_306);
x_307 = lean_box(0);
lean_ctor_set_tag(x_304, 1);
lean_ctor_set(x_304, 0, x_307);
return x_304;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_304, 1);
lean_inc(x_308);
lean_dec(x_304);
x_309 = lean_box(0);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
}
block_322:
{
if (x_314 == 0)
{
uint8_t x_316; uint8_t x_317; 
x_316 = 4;
x_317 = l_Lake_instDecidableEqInitTemplate(x_6, x_316);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; 
x_318 = l_Lake_dotlessName(x_15);
x_319 = l_Lake_readmeFileContents(x_318);
lean_dec(x_318);
x_293 = x_313;
x_294 = x_312;
x_295 = x_315;
x_296 = x_319;
goto block_311;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = l_Lake_dotlessName(x_15);
x_321 = l_Lake_mathReadmeFileContents(x_320);
lean_dec(x_320);
x_293 = x_313;
x_294 = x_312;
x_295 = x_315;
x_296 = x_321;
goto block_311;
}
}
else
{
lean_dec(x_312);
lean_dec(x_15);
x_270 = x_313;
x_271 = x_315;
goto block_292;
}
}
block_341:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; uint8_t x_331; 
x_325 = l_Lake_initPkg___elam__16___redArg___closed__41;
lean_inc(x_2);
x_326 = l_Lake_joinRelative(x_2, x_325);
x_327 = l_System_FilePath_pathExists(x_326, x_324);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
x_330 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_331 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_331 == 0)
{
uint8_t x_332; 
lean_dec(x_16);
x_332 = lean_unbox(x_328);
lean_dec(x_328);
x_312 = x_326;
x_313 = x_323;
x_314 = x_332;
x_315 = x_329;
goto block_322;
}
else
{
uint8_t x_333; 
x_333 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_333 == 0)
{
uint8_t x_334; 
lean_dec(x_16);
x_334 = lean_unbox(x_328);
lean_dec(x_328);
x_312 = x_326;
x_313 = x_323;
x_314 = x_334;
x_315 = x_329;
goto block_322;
}
else
{
lean_object* x_335; size_t x_336; size_t x_337; lean_object* x_338; 
x_335 = lean_box(0);
x_336 = 0;
x_337 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_323);
x_338 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_16, x_330, x_336, x_337, x_335, x_323, x_329);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; uint8_t x_340; 
x_339 = lean_ctor_get(x_338, 1);
lean_inc(x_339);
lean_dec(x_338);
x_340 = lean_unbox(x_328);
lean_dec(x_328);
x_312 = x_326;
x_313 = x_323;
x_314 = x_340;
x_315 = x_339;
goto block_322;
}
else
{
lean_dec(x_328);
lean_dec(x_326);
lean_dec(x_323);
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
return x_338;
}
}
}
}
block_377:
{
if (x_343 == 0)
{
uint8_t x_345; uint8_t x_346; 
x_345 = 1;
x_346 = l_Lake_instDecidableEqInitTemplate(x_6, x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; 
x_347 = l_Lake_mainFileContents(x_17);
x_348 = l_IO_FS_writeFile(x_342, x_347, x_344);
lean_dec(x_347);
lean_dec(x_342);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; 
x_349 = lean_ctor_get(x_348, 1);
lean_inc(x_349);
lean_dec(x_348);
x_323 = x_1;
x_324 = x_349;
goto block_341;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; 
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
x_350 = lean_ctor_get(x_348, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_348, 1);
lean_inc(x_351);
lean_dec(x_348);
x_352 = lean_io_error_to_string(x_350);
x_353 = 3;
x_354 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set_uint8(x_354, sizeof(void*)*1, x_353);
x_355 = lean_apply_2(x_1, x_354, x_351);
x_356 = !lean_is_exclusive(x_355);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_355, 0);
lean_dec(x_357);
x_358 = lean_box(0);
lean_ctor_set_tag(x_355, 1);
lean_ctor_set(x_355, 0, x_358);
return x_355;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_355, 1);
lean_inc(x_359);
lean_dec(x_355);
x_360 = lean_box(0);
x_361 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_17);
x_362 = l_Lake_exeFileContents___closed__0;
x_363 = l_IO_FS_writeFile(x_342, x_362, x_344);
lean_dec(x_342);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; 
x_364 = lean_ctor_get(x_363, 1);
lean_inc(x_364);
lean_dec(x_363);
x_323 = x_1;
x_324 = x_364;
goto block_341;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; uint8_t x_368; lean_object* x_369; lean_object* x_370; uint8_t x_371; 
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
x_365 = lean_ctor_get(x_363, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_363, 1);
lean_inc(x_366);
lean_dec(x_363);
x_367 = lean_io_error_to_string(x_365);
x_368 = 3;
x_369 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set_uint8(x_369, sizeof(void*)*1, x_368);
x_370 = lean_apply_2(x_1, x_369, x_366);
x_371 = !lean_is_exclusive(x_370);
if (x_371 == 0)
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_370, 0);
lean_dec(x_372);
x_373 = lean_box(0);
lean_ctor_set_tag(x_370, 1);
lean_ctor_set(x_370, 0, x_373);
return x_370;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_370, 1);
lean_inc(x_374);
lean_dec(x_370);
x_375 = lean_box(0);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_374);
return x_376;
}
}
}
}
else
{
lean_dec(x_342);
lean_dec(x_17);
x_323 = x_1;
x_324 = x_344;
goto block_341;
}
}
block_394:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; 
x_378 = l_Lake_mainFileName;
lean_inc(x_2);
x_379 = l_Lake_joinRelative(x_2, x_378);
x_380 = l_System_FilePath_pathExists(x_379, x_19);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
x_383 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_384 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_384 == 0)
{
uint8_t x_385; 
lean_dec(x_18);
x_385 = lean_unbox(x_381);
lean_dec(x_381);
x_342 = x_379;
x_343 = x_385;
x_344 = x_382;
goto block_377;
}
else
{
uint8_t x_386; 
x_386 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_386 == 0)
{
uint8_t x_387; 
lean_dec(x_18);
x_387 = lean_unbox(x_381);
lean_dec(x_381);
x_342 = x_379;
x_343 = x_387;
x_344 = x_382;
goto block_377;
}
else
{
lean_object* x_388; size_t x_389; size_t x_390; lean_object* x_391; 
x_388 = lean_box(0);
x_389 = 0;
x_390 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_391 = l_Array_foldlMUnsafe_fold___at___Lake_Workspace_updateAndMaterializeCore___elam__2_spec__2(x_18, x_383, x_389, x_390, x_388, x_1, x_382);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; uint8_t x_393; 
x_392 = lean_ctor_get(x_391, 1);
lean_inc(x_392);
lean_dec(x_391);
x_393 = lean_unbox(x_381);
lean_dec(x_381);
x_342 = x_379;
x_343 = x_393;
x_344 = x_392;
goto block_377;
}
else
{
lean_dec(x_381);
lean_dec(x_379);
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
return x_391;
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
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; uint8_t x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_168; uint8_t x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_197; lean_object* x_263; uint8_t x_264; 
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
x_263 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_264 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_264 == 0)
{
x_197 = x_18;
goto block_262;
}
else
{
uint8_t x_265; 
x_265 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_265 == 0)
{
x_197 = x_18;
goto block_262;
}
else
{
lean_object* x_266; size_t x_267; size_t x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_box(0);
x_267 = 0;
x_268 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_269 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_263, x_267, x_268, x_266, x_1, x_18);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_197 = x_270;
goto block_262;
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
block_41:
{
lean_object* x_26; 
x_26 = l_IO_FS_writeFile(x_22, x_25, x_20);
lean_dec(x_25);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l_Lake_initPkg___elam__16___redArg(x_2, x_12, x_6, x_21, x_4, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_3, x_19, x_24, x_19, x_23, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_26, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_io_error_to_string(x_29);
x_32 = 3;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
x_34 = lean_apply_2(x_23, x_33, x_30);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
block_54:
{
uint8_t x_48; uint8_t x_49; 
x_48 = 4;
x_49 = l_Lake_instDecidableEqInitTemplate(x_4, x_48);
if (x_49 == 0)
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_50 = 1;
lean_inc(x_45);
x_51 = l_Lean_Name_toString(x_45, x_50, x_44);
lean_inc(x_45);
x_52 = l_Lake_libRootFileContents(x_51, x_45);
lean_dec(x_51);
x_20 = x_47;
x_21 = x_43;
x_22 = x_42;
x_23 = x_46;
x_24 = x_45;
x_25 = x_52;
goto block_41;
}
else
{
lean_object* x_53; 
lean_dec(x_44);
lean_inc(x_45);
x_53 = l_Lake_mathLibRootFileContents(x_45);
x_20 = x_47;
x_21 = x_43;
x_22 = x_42;
x_23 = x_46;
x_24 = x_45;
x_25 = x_53;
goto block_41;
}
}
block_92:
{
if (x_61 == 0)
{
lean_object* x_63; 
x_63 = l_IO_FS_createDirAll(x_55, x_62);
lean_dec(x_55);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_Lake_basicFileContents___closed__0;
x_66 = l_IO_FS_writeFile(x_58, x_65, x_64);
lean_dec(x_58);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_42 = x_57;
x_43 = x_56;
x_44 = x_60;
x_45 = x_59;
x_46 = x_1;
x_47 = x_67;
goto block_54;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_io_error_to_string(x_68);
x_71 = 3;
x_72 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set_uint8(x_72, sizeof(void*)*1, x_71);
x_73 = lean_apply_2(x_1, x_72, x_69);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
x_76 = lean_box(0);
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_76);
return x_73;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_dec(x_73);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_ctor_get(x_63, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_63, 1);
lean_inc(x_81);
lean_dec(x_63);
x_82 = lean_io_error_to_string(x_80);
x_83 = 3;
x_84 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_83);
x_85 = lean_apply_2(x_1, x_84, x_81);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_85, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set_tag(x_85, 1);
lean_ctor_set(x_85, 0, x_88);
return x_85;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_dec(x_85);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
}
else
{
lean_dec(x_58);
lean_dec(x_55);
x_42 = x_57;
x_43 = x_56;
x_44 = x_60;
x_45 = x_59;
x_46 = x_1;
x_47 = x_62;
goto block_54;
}
}
block_134:
{
lean_object* x_98; lean_object* x_99; 
lean_inc(x_95);
lean_inc(x_3);
x_98 = l_Lake_InitTemplate_configFileContents(x_4, x_5, x_3, x_95);
x_99 = l_IO_FS_writeFile(x_15, x_98, x_97);
lean_dec(x_98);
lean_dec(x_15);
if (lean_obj_tag(x_99) == 0)
{
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_94);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l_Lake_initPkg___elam__16___at___Lake_initPkg___at___Lake_init_spec__0_spec__0___redArg(x_1, x_2, x_12, x_6, x_93, x_4, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_19, x_3, x_19, x_95, x_19, x_100);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_ctor_get(x_96, 0);
lean_inc(x_103);
lean_dec(x_96);
x_104 = l_Lake_escapeIdent___closed__0;
lean_inc(x_103);
x_105 = l_System_FilePath_withExtension(x_103, x_104);
x_106 = l_Lake_initPkg___closed__1;
lean_inc(x_105);
x_107 = l_Lake_joinRelative(x_105, x_106);
x_108 = l_System_FilePath_pathExists(x_107, x_102);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_112 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_112 == 0)
{
uint8_t x_113; 
x_113 = lean_unbox(x_109);
lean_dec(x_109);
x_55 = x_105;
x_56 = x_93;
x_57 = x_103;
x_58 = x_107;
x_59 = x_95;
x_60 = x_94;
x_61 = x_113;
x_62 = x_110;
goto block_92;
}
else
{
uint8_t x_114; 
x_114 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_114 == 0)
{
uint8_t x_115; 
x_115 = lean_unbox(x_109);
lean_dec(x_109);
x_55 = x_105;
x_56 = x_93;
x_57 = x_103;
x_58 = x_107;
x_59 = x_95;
x_60 = x_94;
x_61 = x_115;
x_62 = x_110;
goto block_92;
}
else
{
lean_object* x_116; size_t x_117; size_t x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_116 = lean_box(0);
x_117 = 0;
x_118 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_119 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_111, x_117, x_118, x_116, x_1, x_110);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_unbox(x_109);
lean_dec(x_109);
x_55 = x_105;
x_56 = x_93;
x_57 = x_103;
x_58 = x_107;
x_59 = x_95;
x_60 = x_94;
x_61 = x_121;
x_62 = x_120;
goto block_92;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_ctor_get(x_99, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_99, 1);
lean_inc(x_123);
lean_dec(x_99);
x_124 = lean_io_error_to_string(x_122);
x_125 = 3;
x_126 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set_uint8(x_126, sizeof(void*)*1, x_125);
x_127 = lean_apply_2(x_1, x_126, x_123);
x_128 = !lean_is_exclusive(x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_127, 0);
lean_dec(x_129);
x_130 = lean_box(0);
lean_ctor_set_tag(x_127, 1);
lean_ctor_set(x_127, 0, x_130);
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_127, 1);
lean_inc(x_131);
lean_dec(x_127);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
block_143:
{
if (x_139 == 0)
{
lean_object* x_141; 
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_135);
x_93 = x_136;
x_94 = x_138;
x_95 = x_137;
x_96 = x_141;
x_97 = x_140;
goto block_134;
}
else
{
lean_object* x_142; 
lean_dec(x_135);
x_142 = lean_box(0);
x_93 = x_136;
x_94 = x_138;
x_95 = x_137;
x_96 = x_142;
x_97 = x_140;
goto block_134;
}
}
block_167:
{
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_144);
x_150 = l_Lake_toUpperCamelCase(x_3);
x_151 = l_Lean_modToFilePath(x_2, x_150, x_147);
lean_dec(x_147);
x_152 = l_System_FilePath_pathExists(x_151, x_146);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_156 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = lean_unbox(x_153);
lean_dec(x_153);
x_135 = x_151;
x_136 = x_145;
x_137 = x_150;
x_138 = x_148;
x_139 = x_157;
x_140 = x_154;
goto block_143;
}
else
{
uint8_t x_158; 
x_158 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_158 == 0)
{
uint8_t x_159; 
x_159 = lean_unbox(x_153);
lean_dec(x_153);
x_135 = x_151;
x_136 = x_145;
x_137 = x_150;
x_138 = x_148;
x_139 = x_159;
x_140 = x_154;
goto block_143;
}
else
{
lean_object* x_160; size_t x_161; size_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_160 = lean_box(0);
x_161 = 0;
x_162 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_163 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_155, x_161, x_162, x_160, x_1, x_154);
x_164 = lean_ctor_get(x_163, 1);
lean_inc(x_164);
lean_dec(x_163);
x_165 = lean_unbox(x_153);
lean_dec(x_153);
x_135 = x_151;
x_136 = x_145;
x_137 = x_150;
x_138 = x_148;
x_139 = x_165;
x_140 = x_164;
goto block_143;
}
}
}
else
{
lean_object* x_166; 
lean_dec(x_147);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_144);
lean_inc(x_3);
x_93 = x_145;
x_94 = x_148;
x_95 = x_3;
x_96 = x_166;
x_97 = x_146;
goto block_134;
}
}
block_176:
{
uint8_t x_174; uint8_t x_175; 
x_174 = 1;
x_175 = l_Lake_instDecidableEqInitTemplate(x_4, x_174);
if (x_175 == 0)
{
x_144 = x_168;
x_145 = x_169;
x_146 = x_173;
x_147 = x_170;
x_148 = x_171;
x_149 = x_172;
goto block_167;
}
else
{
x_144 = x_168;
x_145 = x_169;
x_146 = x_173;
x_147 = x_170;
x_148 = x_171;
x_149 = x_175;
goto block_167;
}
}
block_196:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_180 = l_Lake_initPkg___closed__2;
x_181 = l_Lean_modToFilePath(x_2, x_3, x_180);
x_182 = l_System_FilePath_pathExists(x_181, x_179);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_182, 1);
lean_inc(x_184);
lean_dec(x_182);
x_185 = l_Lake_initPkg___elam__16___redArg___closed__5;
x_186 = l_Lake_initPkg___elam__16___redArg___closed__7;
if (x_186 == 0)
{
uint8_t x_187; 
x_187 = lean_unbox(x_183);
lean_dec(x_183);
x_168 = x_181;
x_169 = x_177;
x_170 = x_180;
x_171 = x_178;
x_172 = x_187;
x_173 = x_184;
goto block_176;
}
else
{
uint8_t x_188; 
x_188 = l_Lake_initPkg___elam__16___redArg___closed__8;
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = lean_unbox(x_183);
lean_dec(x_183);
x_168 = x_181;
x_169 = x_177;
x_170 = x_180;
x_171 = x_178;
x_172 = x_189;
x_173 = x_184;
goto block_176;
}
else
{
lean_object* x_190; size_t x_191; size_t x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_190 = lean_box(0);
x_191 = 0;
x_192 = l_Lake_initPkg___elam__16___redArg___closed__9;
lean_inc(x_1);
x_193 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_185, x_191, x_192, x_190, x_1, x_184);
x_194 = lean_ctor_get(x_193, 1);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_unbox(x_183);
lean_dec(x_183);
x_168 = x_181;
x_169 = x_177;
x_170 = x_180;
x_171 = x_178;
x_172 = x_195;
x_173 = x_194;
goto block_176;
}
}
}
block_262:
{
uint8_t x_198; 
x_198 = lean_unbox(x_17);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_199 = lean_unsigned_to_nat(0u);
x_200 = l_Lake_initPkg___elam__16___redArg___closed__5;
lean_inc(x_2);
x_201 = l_Lake_createLeanActionWorkflow(x_2, x_4, x_200, x_197);
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_17);
x_205 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__0___boxed), 2, 1);
lean_closure_set(x_205, 0, x_17);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
lean_free_object(x_201);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_dec(x_203);
x_207 = lean_array_get_size(x_206);
x_208 = lean_nat_dec_lt(x_199, x_207);
if (x_208 == 0)
{
uint8_t x_209; 
lean_dec(x_207);
lean_dec(x_206);
x_209 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_209;
x_178 = x_205;
x_179 = x_204;
goto block_196;
}
else
{
uint8_t x_210; 
x_210 = lean_nat_dec_le(x_207, x_207);
if (x_210 == 0)
{
uint8_t x_211; 
lean_dec(x_207);
lean_dec(x_206);
x_211 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_211;
x_178 = x_205;
x_179 = x_204;
goto block_196;
}
else
{
lean_object* x_212; size_t x_213; size_t x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_212 = lean_box(0);
x_213 = 0;
x_214 = lean_usize_of_nat(x_207);
lean_dec(x_207);
lean_inc(x_1);
x_215 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_206, x_213, x_214, x_212, x_1, x_204);
lean_dec(x_206);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_217;
x_178 = x_205;
x_179 = x_216;
goto block_196;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
lean_dec(x_205);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_218 = lean_ctor_get(x_203, 1);
lean_inc(x_218);
lean_dec(x_203);
x_219 = lean_array_get_size(x_218);
x_220 = lean_nat_dec_lt(x_199, x_219);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_1);
x_221 = lean_box(0);
lean_ctor_set_tag(x_201, 1);
lean_ctor_set(x_201, 0, x_221);
return x_201;
}
else
{
uint8_t x_222; 
lean_free_object(x_201);
x_222 = lean_nat_dec_le(x_219, x_219);
if (x_222 == 0)
{
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_1);
x_8 = x_204;
goto block_11;
}
else
{
lean_object* x_223; size_t x_224; size_t x_225; lean_object* x_226; lean_object* x_227; 
x_223 = lean_box(0);
x_224 = 0;
x_225 = lean_usize_of_nat(x_219);
lean_dec(x_219);
x_226 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_218, x_224, x_225, x_223, x_1, x_204);
lean_dec(x_218);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_8 = x_227;
goto block_11;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_201, 0);
x_229 = lean_ctor_get(x_201, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_201);
lean_inc(x_17);
x_230 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__0___boxed), 2, 1);
lean_closure_set(x_230, 0, x_17);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_231 = lean_ctor_get(x_228, 1);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_array_get_size(x_231);
x_233 = lean_nat_dec_lt(x_199, x_232);
if (x_233 == 0)
{
uint8_t x_234; 
lean_dec(x_232);
lean_dec(x_231);
x_234 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_234;
x_178 = x_230;
x_179 = x_229;
goto block_196;
}
else
{
uint8_t x_235; 
x_235 = lean_nat_dec_le(x_232, x_232);
if (x_235 == 0)
{
uint8_t x_236; 
lean_dec(x_232);
lean_dec(x_231);
x_236 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_236;
x_178 = x_230;
x_179 = x_229;
goto block_196;
}
else
{
lean_object* x_237; size_t x_238; size_t x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_237 = lean_box(0);
x_238 = 0;
x_239 = lean_usize_of_nat(x_232);
lean_dec(x_232);
lean_inc(x_1);
x_240 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_231, x_238, x_239, x_237, x_1, x_229);
lean_dec(x_231);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_unbox(x_17);
lean_dec(x_17);
x_177 = x_242;
x_178 = x_230;
x_179 = x_241;
goto block_196;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
lean_dec(x_230);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_243 = lean_ctor_get(x_228, 1);
lean_inc(x_243);
lean_dec(x_228);
x_244 = lean_array_get_size(x_243);
x_245 = lean_nat_dec_lt(x_199, x_244);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_1);
x_246 = lean_box(0);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_229);
return x_247;
}
else
{
uint8_t x_248; 
x_248 = lean_nat_dec_le(x_244, x_244);
if (x_248 == 0)
{
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_1);
x_8 = x_229;
goto block_11;
}
else
{
lean_object* x_249; size_t x_250; size_t x_251; lean_object* x_252; lean_object* x_253; 
x_249 = lean_box(0);
x_250 = 0;
x_251 = lean_usize_of_nat(x_244);
lean_dec(x_244);
x_252 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_243, x_250, x_251, x_249, x_1, x_229);
lean_dec(x_243);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_8 = x_253;
goto block_11;
}
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_254 = l_Lake_initPkg___closed__4;
x_255 = lean_apply_2(x_1, x_254, x_197);
x_256 = !lean_is_exclusive(x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_255, 0);
lean_dec(x_257);
x_258 = lean_box(0);
lean_ctor_set_tag(x_255, 1);
lean_ctor_set(x_255, 0, x_258);
return x_255;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_255, 1);
lean_inc(x_259);
lean_dec(x_255);
x_260 = lean_box(0);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_259);
return x_261;
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
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_31; lean_object* x_32; lean_object* x_77; uint8_t x_78; 
x_77 = l_Lake_escapeName_x21___closed__4;
x_78 = lean_string_dec_eq(x_1, x_77);
if (x_78 == 0)
{
x_31 = x_1;
x_32 = x_7;
goto block_76;
}
else
{
lean_object* x_79; 
lean_dec(x_1);
lean_inc(x_5);
x_79 = lean_io_realpath(x_5, x_7);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_80);
x_82 = l_System_FilePath_fileName(x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_5);
lean_dec(x_4);
x_83 = l_Lake_init___closed__0;
x_84 = lean_string_append(x_83, x_80);
lean_dec(x_80);
x_85 = l_Lake_createLeanActionWorkflow___closed__6;
x_86 = lean_string_append(x_84, x_85);
x_87 = 3;
x_88 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set_uint8(x_88, sizeof(void*)*1, x_87);
x_89 = lean_apply_2(x_6, x_88, x_81);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
x_92 = lean_box(0);
lean_ctor_set_tag(x_89, 1);
lean_ctor_set(x_89, 0, x_92);
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; 
lean_dec(x_80);
x_96 = lean_ctor_get(x_82, 0);
lean_inc(x_96);
lean_dec(x_82);
x_31 = x_96;
x_32 = x_81;
goto block_76;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_5);
lean_dec(x_4);
x_97 = lean_ctor_get(x_79, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_79, 1);
lean_inc(x_98);
lean_dec(x_79);
x_99 = lean_io_error_to_string(x_97);
x_100 = 3;
x_101 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_100);
x_102 = lean_apply_2(x_6, x_101, x_98);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
x_105 = lean_box(0);
lean_ctor_set_tag(x_102, 1);
lean_ctor_set(x_102, 0, x_105);
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
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
block_30:
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
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_io_error_to_string(x_18);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_21);
x_23 = lean_apply_2(x_6, x_22, x_19);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
block_76:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_string_utf8_byte_size(x_31);
x_35 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_31, x_34, x_33);
x_36 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_31, x_35, x_34);
x_37 = lean_string_utf8_extract(x_31, x_35, x_36);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
x_38 = l_Lake_initPkg___elam__16___redArg___closed__5;
lean_inc(x_37);
x_39 = l_Lake_validatePkgName(x_37, x_38, x_32);
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
x_44 = lean_nat_dec_lt(x_33, x_43);
if (x_44 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
x_12 = x_37;
x_13 = x_41;
goto block_30;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_43, x_43);
if (x_45 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
x_12 = x_37;
x_13 = x_41;
goto block_30;
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
x_12 = x_37;
x_13 = x_50;
goto block_30;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_37);
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
x_56 = lean_nat_dec_lt(x_33, x_55);
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
x_67 = lean_nat_dec_lt(x_33, x_66);
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
lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_string_utf8_byte_size(x_1);
x_14 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_1, x_13, x_12);
x_15 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_1, x_14, x_13);
x_16 = lean_string_utf8_extract(x_1, x_14, x_15);
lean_dec(x_15);
lean_dec(x_14);
x_37 = l_Lake_initPkg___elam__16___redArg___closed__5;
lean_inc(x_16);
x_38 = l_Lake_validatePkgName(x_16, x_37, x_7);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_array_get_size(x_41);
x_43 = lean_nat_dec_lt(x_12, x_42);
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
x_17 = x_40;
goto block_36;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_le(x_42, x_42);
if (x_44 == 0)
{
lean_dec(x_42);
lean_dec(x_41);
x_17 = x_40;
goto block_36;
}
else
{
lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_box(0);
x_46 = 0;
x_47 = lean_usize_of_nat(x_42);
lean_dec(x_42);
lean_inc(x_6);
x_48 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_41, x_46, x_47, x_45, x_6, x_40);
lean_dec(x_41);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_17 = x_49;
goto block_36;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_16);
lean_dec(x_5);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_38);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_38, 1);
x_52 = lean_ctor_get(x_38, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
lean_dec(x_39);
x_54 = lean_array_get_size(x_53);
x_55 = lean_nat_dec_lt(x_12, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_6);
x_56 = lean_box(0);
lean_ctor_set_tag(x_38, 1);
lean_ctor_set(x_38, 0, x_56);
return x_38;
}
else
{
uint8_t x_57; 
lean_free_object(x_38);
x_57 = lean_nat_dec_le(x_54, x_54);
if (x_57 == 0)
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_6);
x_8 = x_51;
goto block_11;
}
else
{
lean_object* x_58; size_t x_59; size_t x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_box(0);
x_59 = 0;
x_60 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_61 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_53, x_59, x_60, x_58, x_6, x_51);
lean_dec(x_53);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_8 = x_62;
goto block_11;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_63 = lean_ctor_get(x_38, 1);
lean_inc(x_63);
lean_dec(x_38);
x_64 = lean_ctor_get(x_39, 1);
lean_inc(x_64);
lean_dec(x_39);
x_65 = lean_array_get_size(x_64);
x_66 = lean_nat_dec_lt(x_12, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_6);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
return x_68;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_65, x_65);
if (x_69 == 0)
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_6);
x_8 = x_63;
goto block_11;
}
else
{
lean_object* x_70; size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = 0;
x_72 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_73 = l_Array_foldlMUnsafe_fold___at___Lake_initPkg_spec__0(x_64, x_71, x_72, x_70, x_6, x_63);
lean_dec(x_64);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_8 = x_74;
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
block_36:
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_4);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_io_error_to_string(x_24);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_apply_2(x_6, x_28, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
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
