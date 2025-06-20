// Lean compiler output
// Module: Lake.CLI.Init
// Imports: Lake.Util.Git Lake.Util.Sugar Lake.Util.Version Lake.Config.Lang Lake.Config.Package Lake.Config.Workspace Lake.Load.Config Lake.Build.Actions
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
static lean_object* l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_412_;
LEAN_EXPORT lean_object* l_Lake_defaultExeRoot;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_validatePkgName___closed__6;
static lean_object* l_Lake_initPkg___lam__1___closed__21;
static lean_object* l_Lake_initPkg___lam__1___closed__31;
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
static lean_object* l_Lake_stdLeanConfigFileContents___closed__3;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__23;
static lean_object* l_Lake_escapeName_x21___closed__1;
lean_object* lean_io_prim_handle_put_str(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__7;
static lean_object* l_Lake_mainFileName___closed__3;
LEAN_EXPORT lean_object* l_Lake_leanActionWorkflowContents;
LEAN_EXPORT lean_object* l_Lake_initPkg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_escapeName_x21___closed__0;
static lean_object* l_Lake_initPkg___lam__1___closed__22;
static lean_object* l_Lake_instReprInitTemplate___closed__0;
LEAN_EXPORT lean_object* l_Lake_libRootFileContents(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__9;
LEAN_EXPORT lean_object* l_Lake_createLeanActionWorkflow(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_defaultExeRoot___closed__1;
static lean_object* l_Lake_escapeName_x21___closed__3;
static lean_object* l_Lake_mathTomlConfigFileContents___closed__0;
static lean_object* l_Lake_createLeanActionWorkflow___closed__7;
static lean_object* l_Lake_mathToolchainBlobUrl___closed__0;
static lean_object* l_Lake_createLeanActionWorkflow___closed__4;
static lean_object* l_Lake_initPkg___lam__1___closed__25;
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_mainFileName___closed__0;
static lean_object* l_Lake_validatePkgName___closed__8;
LEAN_EXPORT lean_object* l_Lake_stdTomlConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__8;
static lean_object* l_Lake_stdTomlConfigFileContents___closed__4;
static lean_object* l_Lake_initPkg___lam__1___closed__20;
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_escapeName_x21___boxed(lean_object*);
static lean_object* l_Lake_basicFileContents___closed__0;
lean_object* l_Lake_download(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___lam__0___boxed(lean_object*);
static lean_object* l_Lake_initPkg___closed__0;
static lean_object* l_Lake_initPkg___lam__1___closed__12;
lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
static lean_object* l_Lake_init___closed__0;
static lean_object* l_Lake_initPkg___lam__1___closed__30;
LEAN_EXPORT lean_object* l_Lake_new___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprInitTemplate;
static lean_object* l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_412_;
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
static lean_object* l_Lake_initPkg___lam__1___closed__11;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lake_initPkg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedInitTemplate;
LEAN_EXPORT lean_object* l_Lake_mathToolchainUrl;
lean_object* l_IO_FS_createDirAll(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mathTomlConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__18;
static lean_object* l_Lake_stdTomlConfigFileContents___closed__3;
LEAN_EXPORT lean_object* l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_412____boxed(lean_object*, lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_412_;
static lean_object* l_Lake_libTomlConfigFileContents___closed__0;
static lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2___boxed__const__1;
static lean_object* l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_412_;
static lean_object* l_Lake_escapeName_x21___closed__4;
static lean_object* l_Lake_validatePkgName___closed__7;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_configFileContents(uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqInitTemplate___boxed(lean_object*, lean_object*);
static lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__2;
static lean_object* l_Lake_initPkg___lam__1___closed__1;
static lean_object* l_Lake_initPkg___lam__1___closed__29;
LEAN_EXPORT lean_object* l_Lake_gitignoreContents;
static lean_object* l_Lake_initPkg___lam__1___closed__14;
LEAN_EXPORT lean_object* l_Lake_escapeIdent___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__15;
static lean_object* l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_412_;
static lean_object* l_Lake_exeTomlConfigFileContents___closed__0;
static lean_object* l_Lake_createLeanActionWorkflow___closed__3;
LEAN_EXPORT lean_object* l_Lake_dotlessName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_libTomlConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_mathLeanConfigFileContents___closed__1;
lean_object* l_Lake_stringToLegalOrSimpleName(lean_object*);
LEAN_EXPORT lean_object* l_Lake_readmeFileContents___boxed(lean_object*);
static lean_object* l_Lake_initPkg___closed__2;
static lean_object* l_Lake_libLeanConfigFileContents___closed__0;
static lean_object* l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_412_;
static lean_object* l_Lake_validatePkgName___closed__5;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofNat___boxed(lean_object*);
static lean_object* l_Lake_mathLeanConfigFileContents___closed__0;
lean_object* l_System_FilePath_fileName(lean_object*);
lean_object* l_String_mapAux___at___Lake_envToBool_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mainFileName;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__5;
static lean_object* l_Lake_mathToolchainUrl___closed__0;
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_validatePkgName_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdLeanConfigFileContents(lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
static lean_object* l_Lake_libRootFileContents___closed__0;
static lean_object* l_Lake_createLeanActionWorkflow___closed__6;
static lean_object* l_Lake_initPkg___lam__1___closed__4;
static lean_object* l_Lake_validatePkgName___closed__1;
static lean_object* l_Lake_createLeanActionWorkflow___closed__1;
static lean_object* l_Lake_stdLeanConfigFileContents___closed__2;
LEAN_EXPORT uint8_t l_Lake_libRootFileContents___lam__0(lean_object*);
static uint8_t l_Lake_initPkg___lam__1___closed__24;
LEAN_EXPORT lean_object* l_Lake_initPkg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l_Lake_initPkg___closed__4;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__1;
static lean_object* l_Lake_initPkg___lam__1___closed__26;
static lean_object* l_Lake_initPkg___lam__1___closed__5;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lake_exeLeanConfigFileContents(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_escapeIdent(lean_object*);
static lean_object* l_Lake_escapeName_x21___closed__5;
static lean_object* l_Lake_initPkg___closed__1;
LEAN_EXPORT lean_object* l_Lake_basicFileContents;
static lean_object* l_Lake_stdLeanConfigFileContents___closed__1;
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_stdTomlConfigFileContents___closed__1;
LEAN_EXPORT lean_object* l_Lake_libRootFileContents___lam__0___boxed(lean_object*);
static lean_object* l_Lake_escapeIdent___closed__2;
static lean_object* l_Lake_initPkg___lam__1___closed__3;
lean_object* l_Lake_testProc(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_initPkg___lam__0(uint8_t, lean_object*);
static lean_object* l_Lake_mainFileName___closed__1;
LEAN_EXPORT lean_object* l_Lake_init___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__0;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__2;
static lean_object* l_Lake_initPkg___lam__1___closed__19;
LEAN_EXPORT lean_object* l_Lake_mathLeanConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__10;
static lean_object* l_Lake_validatePkgName___closed__3;
lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
LEAN_EXPORT lean_object* l_Lake_libLeanConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_stdTomlConfigFileContents___closed__2;
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_exeLeanConfigFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_escapeIdent___closed__1;
static lean_object* l_Lake_validatePkgName___closed__2;
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_configFileContents___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mainFileContents___closed__0;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_new(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_stdLeanConfigFileContents___closed__0;
static lean_object* l_Lake_initPkg___lam__1___closed__28;
static lean_object* l_Lake_initPkg___lam__1___closed__27;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_initPkg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exeFileContents;
static lean_object* l_Lake_createLeanActionWorkflow___closed__2;
LEAN_EXPORT lean_object* l_Lake_mathLeanConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_validatePkgName___closed__0;
lean_object* lean_io_realpath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_validatePkgName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_stdLeanConfigFileContents___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_libRootFileContents___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__13;
static lean_object* l_String_anyAux___at___Lake_validatePkgName_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lake_stdTomlConfigFileContents(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___closed__3;
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initPkg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lake_mainFileContents(lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_mathTomlConfigFileContents___closed__1;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_ofString_x3f(lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_412_;
lean_object* l_Lake_proc(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_libRootFileContents___closed__1;
LEAN_EXPORT lean_object* l_Lake_mathToolchainBlobUrl;
LEAN_EXPORT lean_object* l_Lake_init(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_exeFileContents___closed__0;
lean_object* l_Lake_toUpperCamelCase(lean_object*);
static lean_object* l_Lake_gitignoreContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_escapeName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lake_libLeanConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_412_;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_libTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_readmeFileContents___closed__0;
lean_object* l_Lake_Env_toolchain(lean_object*);
static lean_object* l_Lake_libRootFileContents___closed__2;
static lean_object* l_Lake_initPkg___lam__1___closed__6;
static lean_object* l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_412_;
LEAN_EXPORT lean_object* l_Lake_readmeFileContents(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_exeTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_validatePkgName___closed__9;
static lean_object* l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_412_;
lean_object* l_Lean_modToFilePath(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_FS_writeFile(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_mainFileName___closed__2;
LEAN_EXPORT uint8_t l_Lake_instDecidableEqInitTemplate(uint8_t, uint8_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_InitTemplate_ofNat(lean_object*);
static lean_object* l_Lake_mainFileContents___closed__1;
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lake_exeLeanConfigFileContents___closed__0;
static lean_object* l_Lake_libLeanConfigFileContents___closed__1;
static lean_object* l_Lake_leanActionWorkflowContents___closed__0;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lake_defaultExeRoot___closed__0;
LEAN_EXPORT lean_object* l_Lake_initPkg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_dotlessName___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_exeTomlConfigFileContents___boxed(lean_object*, lean_object*);
lean_object* l_Lake_joinRelative(lean_object*, lean_object*);
static lean_object* l_Lake_createLeanActionWorkflow___closed__8;
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_validatePkgName_spec__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_InitTemplate_noConfusion___redArg(uint8_t, uint8_t);
static lean_object* l_Lake_escapeIdent___closed__0;
static lean_object* l_Lake_initPkg___lam__1___closed__17;
static lean_object* l_Lake_InitTemplate_ofString_x3f___closed__7;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_mathTomlConfigFileContents(lean_object*, lean_object*);
static lean_object* l_Lake_escapeName_x21___closed__2;
lean_object* l_instDecidableEqString___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_stdTomlConfigFileContents___closed__0;
LEAN_EXPORT lean_object* l_Lake_InitTemplate_toCtorIdx(uint8_t);
static lean_object* l_Lake_initPkg___lam__1___closed__16;
LEAN_EXPORT lean_object* l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_412_(uint8_t, lean_object*);
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
static lean_object* _init_l_Lake_mainFileName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_libRootFileContents___lam__0___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_mainFileName___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lake_mainFileName___closed__0;
x_2 = lean_box(1);
x_3 = l_Lake_defaultExeRoot;
x_4 = lean_unbox(x_2);
x_5 = l_Lean_Name_toString(x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_mainFileName___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".lean", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_mainFileName___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_mainFileName___closed__2;
x_2 = l_Lake_mainFileName___closed__1;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_mainFileName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_mainFileName___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_mainFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("import ", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_mainFileContents___closed__1() {
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
x_2 = l_Lake_mainFileName___closed__0;
x_3 = l_Lake_mainFileContents___closed__0;
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
x_6 = l_Lean_Name_toString(x_1, x_5, x_2);
x_7 = lean_string_append(x_3, x_6);
lean_dec(x_6);
x_8 = l_Lake_mainFileContents___closed__1;
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
static lean_object* _init_l_Lake_mathLeanConfigFileContents___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  version := v!\"0.1.0\"\n  keywords := #[\"math\"]\n  leanOptions := #[\n    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`\n  ]\n\nrequire \"leanprover-community\" / \"mathlib\"\n\n@[default_target]\nlean_lib ", 213, 207);
return x_1;
}
}
static lean_object* _init_l_Lake_mathLeanConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" where\n  -- add any library configuration options here\n", 55, 55);
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
x_13 = l_Lake_mathLeanConfigFileContents___closed__1;
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
x_1 = lean_mk_string_unchecked("\nversion = \"0.1.0\"\nkeywords = [\"math\"]\ndefaultTargets = [", 57, 57);
return x_1;
}
}
static lean_object* _init_l_Lake_mathTomlConfigFileContents___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("]\n\n[leanOptions]\npp.unicode.fun = true # pretty-prints `fun a ↦ b`\n\n[[require]]\nname = \"mathlib\"\nscope = \"leanprover-community\"\n\n[[lean_lib]]\nname = ", 151, 149);
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
x_10 = l_Lake_mathTomlConfigFileContents___closed__0;
x_11 = lean_string_append(x_9, x_10);
x_12 = l_String_quote(x_2);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_format_pretty(x_13, x_6, x_7, x_7);
x_15 = lean_string_append(x_11, x_14);
x_16 = l_Lake_mathTomlConfigFileContents___closed__1;
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
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
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
static lean_object* _init_l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.std", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_412_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.exe", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_412_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.lib", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_412_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.InitTemplate.math", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_412_;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_412_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_412_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_11; lean_object* x_19; lean_object* x_27; 
switch (x_1) {
case 0:
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_unsigned_to_nat(1024u);
x_36 = lean_nat_dec_le(x_35, x_2);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_412_;
x_3 = x_37;
goto block_10;
}
else
{
lean_object* x_38; 
x_38 = l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_412_;
x_3 = x_38;
goto block_10;
}
}
case 1:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_412_;
x_11 = x_41;
goto block_18;
}
else
{
lean_object* x_42; 
x_42 = l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_412_;
x_11 = x_42;
goto block_18;
}
}
case 2:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_unsigned_to_nat(1024u);
x_44 = lean_nat_dec_le(x_43, x_2);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_412_;
x_19 = x_45;
goto block_26;
}
else
{
lean_object* x_46; 
x_46 = l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_412_;
x_19 = x_46;
goto block_26;
}
}
default: 
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_unsigned_to_nat(1024u);
x_48 = lean_nat_dec_le(x_47, x_2);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_412_;
x_27 = x_49;
goto block_34;
}
else
{
lean_object* x_50; 
x_50 = l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_412_;
x_27 = x_50;
goto block_34;
}
}
}
block_10:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_4 = l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_412_;
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
x_12 = l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_412_;
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
x_20 = l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_412_;
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
x_28 = l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_412_;
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
}
}
LEAN_EXPORT lean_object* l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_412____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_412_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprInitTemplate___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_reprInitTemplate____x40_Lake_CLI_Init___hyg_412____boxed), 2, 0);
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
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_1, x_2);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(3);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(2);
x_14 = lean_unbox(x_13);
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
x_1 = lean_mk_string_unchecked("math", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(3);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(2);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_InitTemplate_ofString_x3f___closed__7() {
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
lean_object* x_10; 
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = l_Lake_InitTemplate_ofString_x3f___closed__4;
return x_11;
}
}
else
{
lean_object* x_12; 
x_12 = l_Lake_InitTemplate_ofString_x3f___closed__5;
return x_12;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lake_InitTemplate_ofString_x3f___closed__6;
return x_13;
}
}
else
{
lean_object* x_14; 
x_14 = l_Lake_InitTemplate_ofString_x3f___closed__7;
return x_14;
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
x_3 = lean_unsigned_to_nat(201u);
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
x_3 = lean_unsigned_to_nat(204u);
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
x_3 = l_panic___at___Lean_Name_getString_x21_spec__0(x_2);
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
x_14 = l_panic___at___Lean_Name_getString_x21_spec__0(x_13);
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
x_10 = l_Lake_mainFileName___closed__0;
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
x_25 = l_Lake_mainFileName___closed__0;
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
x_28 = l_Lean_Name_toString(x_4, x_27, x_25);
x_29 = l_Lake_libTomlConfigFileContents(x_5, x_28);
lean_dec(x_28);
lean_dec(x_5);
return x_29;
}
}
default: 
{
if (x_2 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lake_escapeName_x21(x_4);
lean_dec(x_4);
x_31 = l_Lake_mathLeanConfigFileContents(x_5, x_30);
lean_dec(x_30);
lean_dec(x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_32 = l_Lake_mainFileName___closed__0;
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
x_35 = l_Lean_Name_toString(x_4, x_34, x_32);
x_36 = l_Lake_mathTomlConfigFileContents(x_5, x_35);
lean_dec(x_35);
lean_dec(x_5);
return x_36;
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
x_1 = lean_mk_string_unchecked(".github", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("workflows", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_action_ci.yml", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("creating lean-action CI workflow", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_createLeanActionWorkflow___closed__3;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
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
x_1 = lean_mk_string_unchecked("lean-action CI workflow already exists", 38, 38);
return x_1;
}
}
static lean_object* _init_l_Lake_createLeanActionWorkflow___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_createLeanActionWorkflow___closed__7;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_createLeanActionWorkflow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = l_Lake_createLeanActionWorkflow___closed__0;
x_5 = l_Lake_joinRelative(x_1, x_4);
x_6 = l_Lake_createLeanActionWorkflow___closed__1;
x_7 = l_Lake_joinRelative(x_5, x_6);
x_8 = l_Lake_createLeanActionWorkflow___closed__2;
lean_inc(x_7);
x_9 = l_Lake_joinRelative(x_7, x_8);
x_10 = l_System_FilePath_pathExists(x_9, x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_box(0);
x_15 = l_Lake_createLeanActionWorkflow___closed__4;
x_16 = lean_array_push(x_2, x_15);
x_17 = lean_unbox(x_12);
lean_dec(x_12);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_10);
x_18 = l_IO_FS_createDirAll(x_7, x_13);
lean_dec(x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lake_leanActionWorkflowContents___closed__0;
x_21 = l_IO_FS_writeFile(x_9, x_20, x_19);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = l_Lake_createLeanActionWorkflow___closed__5;
x_25 = lean_string_append(x_24, x_9);
lean_dec(x_9);
x_26 = l_Lake_createLeanActionWorkflow___closed__6;
x_27 = lean_string_append(x_25, x_26);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_unbox(x_14);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
x_30 = lean_box(0);
x_31 = lean_array_push(x_16, x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = l_Lake_createLeanActionWorkflow___closed__5;
x_35 = lean_string_append(x_34, x_9);
lean_dec(x_9);
x_36 = l_Lake_createLeanActionWorkflow___closed__6;
x_37 = lean_string_append(x_35, x_36);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_unbox(x_14);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = lean_box(0);
x_41 = lean_array_push(x_16, x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_9);
x_44 = !lean_is_exclusive(x_21);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_io_error_to_string(x_45);
x_47 = lean_box(3);
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_46);
x_49 = lean_unbox(x_47);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_array_get_size(x_16);
x_51 = lean_array_push(x_16, x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set_tag(x_21, 0);
lean_ctor_set(x_21, 0, x_52);
return x_21;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_53 = lean_ctor_get(x_21, 0);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_21);
x_55 = lean_io_error_to_string(x_53);
x_56 = lean_box(3);
x_57 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_57, 0, x_55);
x_58 = lean_unbox(x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*1, x_58);
x_59 = lean_array_get_size(x_16);
x_60 = lean_array_push(x_16, x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_9);
x_63 = !lean_is_exclusive(x_18);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_18, 0);
x_65 = lean_io_error_to_string(x_64);
x_66 = lean_box(3);
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_unbox(x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_68);
x_69 = lean_array_get_size(x_16);
x_70 = lean_array_push(x_16, x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set_tag(x_18, 0);
lean_ctor_set(x_18, 0, x_71);
return x_18;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_72 = lean_ctor_get(x_18, 0);
x_73 = lean_ctor_get(x_18, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_18);
x_74 = lean_io_error_to_string(x_72);
x_75 = lean_box(3);
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
x_77 = lean_unbox(x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_77);
x_78 = lean_array_get_size(x_16);
x_79 = lean_array_push(x_16, x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_9);
lean_dec(x_7);
x_82 = l_Lake_createLeanActionWorkflow___closed__8;
x_83 = lean_array_push(x_16, x_82);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_10, 0, x_85);
return x_10;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_86 = lean_ctor_get(x_10, 0);
x_87 = lean_ctor_get(x_10, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_10);
x_88 = lean_box(0);
x_89 = l_Lake_createLeanActionWorkflow___closed__4;
x_90 = lean_array_push(x_2, x_89);
x_91 = lean_unbox(x_86);
lean_dec(x_86);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = l_IO_FS_createDirAll(x_7, x_87);
lean_dec(x_7);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lake_leanActionWorkflowContents___closed__0;
x_95 = l_IO_FS_writeFile(x_9, x_94, x_93);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_97 = x_95;
} else {
 lean_dec_ref(x_95);
 x_97 = lean_box(0);
}
x_98 = l_Lake_createLeanActionWorkflow___closed__5;
x_99 = lean_string_append(x_98, x_9);
lean_dec(x_9);
x_100 = l_Lake_createLeanActionWorkflow___closed__6;
x_101 = lean_string_append(x_99, x_100);
x_102 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_unbox(x_88);
lean_ctor_set_uint8(x_102, sizeof(void*)*1, x_103);
x_104 = lean_box(0);
x_105 = lean_array_push(x_90, x_102);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
if (lean_is_scalar(x_97)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_97;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_96);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_9);
x_108 = lean_ctor_get(x_95, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_110 = x_95;
} else {
 lean_dec_ref(x_95);
 x_110 = lean_box(0);
}
x_111 = lean_io_error_to_string(x_108);
x_112 = lean_box(3);
x_113 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_113, 0, x_111);
x_114 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_114);
x_115 = lean_array_get_size(x_90);
x_116 = lean_array_push(x_90, x_113);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
if (lean_is_scalar(x_110)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_110;
 lean_ctor_set_tag(x_118, 0);
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_109);
return x_118;
}
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_9);
x_119 = lean_ctor_get(x_92, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_92, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_121 = x_92;
} else {
 lean_dec_ref(x_92);
 x_121 = lean_box(0);
}
x_122 = lean_io_error_to_string(x_119);
x_123 = lean_box(3);
x_124 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_124, 0, x_122);
x_125 = lean_unbox(x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*1, x_125);
x_126 = lean_array_get_size(x_90);
x_127 = lean_array_push(x_90, x_124);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
if (lean_is_scalar(x_121)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_121;
 lean_ctor_set_tag(x_129, 0);
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_120);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_9);
lean_dec(x_7);
x_130 = l_Lake_createLeanActionWorkflow___closed__8;
x_131 = lean_array_push(x_90, x_130);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_131);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_87);
return x_134;
}
}
}
}
LEAN_EXPORT uint8_t l_Lake_initPkg___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".gitignore", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean-toolchain", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("downloading mathlib `lean-toolchain` file", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_initPkg___lam__1___closed__2;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to download mathlib 'lean-toolchain' file; you can manually copy it from:\n  {mathToolchainUrl}", 101, 101);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_initPkg___lam__1___closed__5;
x_2 = lean_box(3);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("could not create a `lean-toolchain` file for the new package; no known toolchain name for the current Elan/Lean/Lake", 116, 116);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_initPkg___lam__1___closed__7;
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to initialize git repository", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_1 = l_Lake_initPkg___lam__1___closed__9;
x_2 = lean_box(2);
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rev-parse", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--is-inside-work-tree", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___lam__1___closed__11;
x_2 = l_Lake_initPkg___lam__1___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___lam__1___closed__12;
x_2 = l_Lake_initPkg___lam__1___closed__14;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__16() {
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
static lean_object* _init_l_Lake_initPkg___lam__1___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("git", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("init", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-q", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___lam__1___closed__19;
x_2 = l_Lake_initPkg___lam__1___closed__13;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___lam__1___closed__20;
x_2 = l_Lake_initPkg___lam__1___closed__21;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("master", 6, 6);
return x_1;
}
}
static uint8_t _init_l_Lake_initPkg___lam__1___closed__24() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = l_Lake_initPkg___lam__1___closed__23;
x_2 = lean_string_dec_eq(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("checkout", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-B", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___lam__1___closed__25;
x_2 = l_Lake_initPkg___lam__1___closed__27;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___lam__1___closed__26;
x_2 = l_Lake_initPkg___lam__1___closed__28;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_initPkg___lam__1___closed__23;
x_2 = l_Lake_initPkg___lam__1___closed__29;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initPkg___lam__1___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("README.md", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_initPkg___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_221; lean_object* x_230; lean_object* x_231; lean_object* x_262; lean_object* x_310; 
x_310 = lean_box(x_3);
switch (lean_obj_tag(x_310)) {
case 2:
{
lean_dec(x_6);
x_262 = x_9;
goto block_309;
}
case 3:
{
lean_dec(x_6);
x_262 = x_9;
goto block_309;
}
default: 
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
lean_dec(x_310);
x_311 = l_Lake_mainFileName;
lean_inc(x_1);
x_312 = l_Lake_joinRelative(x_1, x_311);
x_313 = l_System_FilePath_pathExists(x_312, x_9);
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_unbox(x_314);
lean_dec(x_314);
if (x_315 == 0)
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_313);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; uint8_t x_321; 
x_317 = lean_ctor_get(x_313, 1);
x_318 = lean_ctor_get(x_313, 0);
lean_dec(x_318);
x_319 = lean_box(1);
x_320 = lean_unbox(x_319);
x_321 = l_Lake_instDecidableEqInitTemplate(x_3, x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
x_322 = l_Lake_mainFileContents(x_6);
x_323 = l_IO_FS_writeFile(x_312, x_322, x_317);
lean_dec(x_322);
lean_dec(x_312);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; 
lean_free_object(x_313);
x_324 = lean_ctor_get(x_323, 1);
lean_inc(x_324);
lean_dec(x_323);
x_262 = x_324;
goto block_309;
}
else
{
uint8_t x_325; 
lean_dec(x_5);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_323);
if (x_325 == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; lean_object* x_331; lean_object* x_332; 
x_326 = lean_ctor_get(x_323, 0);
x_327 = lean_io_error_to_string(x_326);
x_328 = lean_box(3);
x_329 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_329, 0, x_327);
x_330 = lean_unbox(x_328);
lean_ctor_set_uint8(x_329, sizeof(void*)*1, x_330);
x_331 = lean_array_get_size(x_8);
x_332 = lean_array_push(x_8, x_329);
lean_ctor_set_tag(x_313, 1);
lean_ctor_set(x_313, 1, x_332);
lean_ctor_set(x_313, 0, x_331);
lean_ctor_set_tag(x_323, 0);
lean_ctor_set(x_323, 0, x_313);
return x_323;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_333 = lean_ctor_get(x_323, 0);
x_334 = lean_ctor_get(x_323, 1);
lean_inc(x_334);
lean_inc(x_333);
lean_dec(x_323);
x_335 = lean_io_error_to_string(x_333);
x_336 = lean_box(3);
x_337 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_337, 0, x_335);
x_338 = lean_unbox(x_336);
lean_ctor_set_uint8(x_337, sizeof(void*)*1, x_338);
x_339 = lean_array_get_size(x_8);
x_340 = lean_array_push(x_8, x_337);
lean_ctor_set_tag(x_313, 1);
lean_ctor_set(x_313, 1, x_340);
lean_ctor_set(x_313, 0, x_339);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_313);
lean_ctor_set(x_341, 1, x_334);
return x_341;
}
}
}
else
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_6);
x_342 = l_Lake_exeFileContents___closed__0;
x_343 = l_IO_FS_writeFile(x_312, x_342, x_317);
lean_dec(x_312);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; 
lean_free_object(x_313);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
lean_dec(x_343);
x_262 = x_344;
goto block_309;
}
else
{
uint8_t x_345; 
lean_dec(x_5);
lean_dec(x_1);
x_345 = !lean_is_exclusive(x_343);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; lean_object* x_352; 
x_346 = lean_ctor_get(x_343, 0);
x_347 = lean_io_error_to_string(x_346);
x_348 = lean_box(3);
x_349 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_349, 0, x_347);
x_350 = lean_unbox(x_348);
lean_ctor_set_uint8(x_349, sizeof(void*)*1, x_350);
x_351 = lean_array_get_size(x_8);
x_352 = lean_array_push(x_8, x_349);
lean_ctor_set_tag(x_313, 1);
lean_ctor_set(x_313, 1, x_352);
lean_ctor_set(x_313, 0, x_351);
lean_ctor_set_tag(x_343, 0);
lean_ctor_set(x_343, 0, x_313);
return x_343;
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_353 = lean_ctor_get(x_343, 0);
x_354 = lean_ctor_get(x_343, 1);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_343);
x_355 = lean_io_error_to_string(x_353);
x_356 = lean_box(3);
x_357 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_357, 0, x_355);
x_358 = lean_unbox(x_356);
lean_ctor_set_uint8(x_357, sizeof(void*)*1, x_358);
x_359 = lean_array_get_size(x_8);
x_360 = lean_array_push(x_8, x_357);
lean_ctor_set_tag(x_313, 1);
lean_ctor_set(x_313, 1, x_360);
lean_ctor_set(x_313, 0, x_359);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_313);
lean_ctor_set(x_361, 1, x_354);
return x_361;
}
}
}
}
else
{
lean_object* x_362; lean_object* x_363; uint8_t x_364; uint8_t x_365; 
x_362 = lean_ctor_get(x_313, 1);
lean_inc(x_362);
lean_dec(x_313);
x_363 = lean_box(1);
x_364 = lean_unbox(x_363);
x_365 = l_Lake_instDecidableEqInitTemplate(x_3, x_364);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; 
x_366 = l_Lake_mainFileContents(x_6);
x_367 = l_IO_FS_writeFile(x_312, x_366, x_362);
lean_dec(x_366);
lean_dec(x_312);
if (lean_obj_tag(x_367) == 0)
{
lean_object* x_368; 
x_368 = lean_ctor_get(x_367, 1);
lean_inc(x_368);
lean_dec(x_367);
x_262 = x_368;
goto block_309;
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_5);
lean_dec(x_1);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_371 = x_367;
} else {
 lean_dec_ref(x_367);
 x_371 = lean_box(0);
}
x_372 = lean_io_error_to_string(x_369);
x_373 = lean_box(3);
x_374 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_374, 0, x_372);
x_375 = lean_unbox(x_373);
lean_ctor_set_uint8(x_374, sizeof(void*)*1, x_375);
x_376 = lean_array_get_size(x_8);
x_377 = lean_array_push(x_8, x_374);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
if (lean_is_scalar(x_371)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_371;
 lean_ctor_set_tag(x_379, 0);
}
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_370);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_6);
x_380 = l_Lake_exeFileContents___closed__0;
x_381 = l_IO_FS_writeFile(x_312, x_380, x_362);
lean_dec(x_312);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; 
x_382 = lean_ctor_get(x_381, 1);
lean_inc(x_382);
lean_dec(x_381);
x_262 = x_382;
goto block_309;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec(x_5);
lean_dec(x_1);
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
x_384 = lean_ctor_get(x_381, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_385 = x_381;
} else {
 lean_dec_ref(x_381);
 x_385 = lean_box(0);
}
x_386 = lean_io_error_to_string(x_383);
x_387 = lean_box(3);
x_388 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_388, 0, x_386);
x_389 = lean_unbox(x_387);
lean_ctor_set_uint8(x_388, sizeof(void*)*1, x_389);
x_390 = lean_array_get_size(x_8);
x_391 = lean_array_push(x_8, x_388);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
if (lean_is_scalar(x_385)) {
 x_393 = lean_alloc_ctor(0, 2, 0);
} else {
 x_393 = x_385;
 lean_ctor_set_tag(x_393, 0);
}
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_384);
return x_393;
}
}
}
}
else
{
lean_object* x_394; 
lean_dec(x_312);
lean_dec(x_6);
x_394 = lean_ctor_get(x_313, 1);
lean_inc(x_394);
lean_dec(x_313);
x_262 = x_394;
goto block_309;
}
}
}
block_220:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = l_Lake_initPkg___lam__1___closed__0;
lean_inc(x_1);
x_13 = l_Lake_joinRelative(x_1, x_12);
x_14 = lean_box(4);
x_15 = lean_unbox(x_14);
x_16 = lean_io_prim_handle_mk(x_13, x_15, x_11);
lean_dec(x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lake_gitignoreContents___closed__0;
x_20 = lean_io_prim_handle_put_str(x_17, x_19, x_18);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_20, 1);
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = l_Lake_initPkg___lam__1___closed__1;
x_25 = l_Lake_joinRelative(x_1, x_24);
x_26 = l_Lake_Env_toolchain(x_2);
x_27 = lean_string_utf8_byte_size(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_eq(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; uint8_t x_32; 
lean_free_object(x_20);
x_30 = lean_box(3);
x_31 = lean_unbox(x_30);
x_32 = l_Lake_instDecidableEqInitTemplate(x_3, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lake_libTomlConfigFileContents___closed__0;
x_34 = lean_string_append(x_26, x_33);
x_35 = l_IO_FS_writeFile(x_25, x_34, x_22);
lean_dec(x_34);
lean_dec(x_25);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_35);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_10);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_35);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_io_error_to_string(x_44);
x_46 = lean_box(3);
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = lean_array_get_size(x_10);
x_50 = lean_array_push(x_10, x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set_tag(x_35, 0);
lean_ctor_set(x_35, 0, x_51);
return x_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = lean_io_error_to_string(x_52);
x_55 = lean_box(3);
x_56 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_56, 0, x_54);
x_57 = lean_unbox(x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
x_58 = lean_array_get_size(x_10);
x_59 = lean_array_push(x_10, x_56);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_53);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_26);
x_62 = l_Lake_initPkg___lam__1___closed__3;
x_63 = lean_array_push(x_10, x_62);
x_64 = l_Lake_mathToolchainBlobUrl___closed__0;
x_65 = l_Lake_initPkg___lam__1___closed__4;
x_66 = l_Lake_download(x_64, x_25, x_65, x_63, x_22);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_dec(x_67);
return x_66;
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_dec(x_69);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 1);
x_72 = l_Lake_initPkg___lam__1___closed__6;
x_73 = lean_array_push(x_71, x_72);
lean_ctor_set(x_67, 1, x_73);
return x_66;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_67, 0);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_67);
x_76 = l_Lake_initPkg___lam__1___closed__6;
x_77 = lean_array_push(x_75, x_76);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_74);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_66, 0, x_78);
return x_66;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
lean_dec(x_66);
x_80 = lean_ctor_get(x_67, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_67, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_82 = x_67;
} else {
 lean_dec_ref(x_67);
 x_82 = lean_box(0);
}
x_83 = l_Lake_initPkg___lam__1___closed__6;
x_84 = lean_array_push(x_81, x_83);
if (lean_is_scalar(x_82)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_82;
}
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_79);
return x_86;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
lean_dec(x_26);
x_87 = lean_ctor_get(x_2, 1);
x_88 = lean_ctor_get(x_87, 1);
x_89 = lean_string_utf8_byte_size(x_88);
x_90 = lean_nat_dec_eq(x_89, x_28);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_free_object(x_20);
x_91 = l_System_FilePath_pathExists(x_25, x_22);
lean_dec(x_25);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_91);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_91, 0);
lean_dec(x_95);
x_96 = l_Lake_initPkg___lam__1___closed__8;
x_97 = lean_box(0);
x_98 = lean_array_push(x_10, x_96);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
lean_ctor_set(x_91, 0, x_99);
return x_91;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = lean_ctor_get(x_91, 1);
lean_inc(x_100);
lean_dec(x_91);
x_101 = l_Lake_initPkg___lam__1___closed__8;
x_102 = lean_box(0);
x_103 = lean_array_push(x_10, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_100);
return x_105;
}
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_91);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_91, 0);
lean_dec(x_107);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_10);
lean_ctor_set(x_91, 0, x_109);
return x_91;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_91, 1);
lean_inc(x_110);
lean_dec(x_91);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_10);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_25);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_10);
lean_ctor_set(x_20, 0, x_115);
return x_20;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_116 = lean_ctor_get(x_20, 1);
lean_inc(x_116);
lean_dec(x_20);
x_117 = l_Lake_initPkg___lam__1___closed__1;
x_118 = l_Lake_joinRelative(x_1, x_117);
x_119 = l_Lake_Env_toolchain(x_2);
x_120 = lean_string_utf8_byte_size(x_119);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_nat_dec_eq(x_120, x_121);
lean_dec(x_120);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; uint8_t x_125; 
x_123 = lean_box(3);
x_124 = lean_unbox(x_123);
x_125 = l_Lake_instDecidableEqInitTemplate(x_3, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = l_Lake_libTomlConfigFileContents___closed__0;
x_127 = lean_string_append(x_119, x_126);
x_128 = l_IO_FS_writeFile(x_118, x_127, x_116);
lean_dec(x_127);
lean_dec(x_118);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_10);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_128, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_136 = x_128;
} else {
 lean_dec_ref(x_128);
 x_136 = lean_box(0);
}
x_137 = lean_io_error_to_string(x_134);
x_138 = lean_box(3);
x_139 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_139, 0, x_137);
x_140 = lean_unbox(x_138);
lean_ctor_set_uint8(x_139, sizeof(void*)*1, x_140);
x_141 = lean_array_get_size(x_10);
x_142 = lean_array_push(x_10, x_139);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
if (lean_is_scalar(x_136)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_136;
 lean_ctor_set_tag(x_144, 0);
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_135);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_119);
x_145 = l_Lake_initPkg___lam__1___closed__3;
x_146 = lean_array_push(x_10, x_145);
x_147 = l_Lake_mathToolchainBlobUrl___closed__0;
x_148 = l_Lake_initPkg___lam__1___closed__4;
x_149 = l_Lake_download(x_147, x_118, x_148, x_146, x_116);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
if (lean_obj_tag(x_150) == 0)
{
lean_dec(x_150);
return x_149;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_ctor_get(x_150, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_150, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_155 = x_150;
} else {
 lean_dec_ref(x_150);
 x_155 = lean_box(0);
}
x_156 = l_Lake_initPkg___lam__1___closed__6;
x_157 = lean_array_push(x_154, x_156);
if (lean_is_scalar(x_155)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_155;
}
lean_ctor_set(x_158, 0, x_153);
lean_ctor_set(x_158, 1, x_157);
if (lean_is_scalar(x_152)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_152;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_151);
return x_159;
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
lean_dec(x_119);
x_160 = lean_ctor_get(x_2, 1);
x_161 = lean_ctor_get(x_160, 1);
x_162 = lean_string_utf8_byte_size(x_161);
x_163 = lean_nat_dec_eq(x_162, x_121);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = l_System_FilePath_pathExists(x_118, x_116);
lean_dec(x_118);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_unbox(x_165);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_167 = lean_ctor_get(x_164, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_168 = x_164;
} else {
 lean_dec_ref(x_164);
 x_168 = lean_box(0);
}
x_169 = l_Lake_initPkg___lam__1___closed__8;
x_170 = lean_box(0);
x_171 = lean_array_push(x_10, x_169);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
if (lean_is_scalar(x_168)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_168;
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_167);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_174 = lean_ctor_get(x_164, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_175 = x_164;
} else {
 lean_dec_ref(x_164);
 x_175 = lean_box(0);
}
x_176 = lean_box(0);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_10);
if (lean_is_scalar(x_175)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_175;
}
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_174);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_118);
x_179 = lean_box(0);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_10);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_116);
return x_181;
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_20);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_183 = lean_ctor_get(x_20, 0);
x_184 = lean_io_error_to_string(x_183);
x_185 = lean_box(3);
x_186 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_186, 0, x_184);
x_187 = lean_unbox(x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_187);
x_188 = lean_array_get_size(x_10);
x_189 = lean_array_push(x_10, x_186);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
lean_ctor_set_tag(x_20, 0);
lean_ctor_set(x_20, 0, x_190);
return x_20;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_191 = lean_ctor_get(x_20, 0);
x_192 = lean_ctor_get(x_20, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_20);
x_193 = lean_io_error_to_string(x_191);
x_194 = lean_box(3);
x_195 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_195, 0, x_193);
x_196 = lean_unbox(x_194);
lean_ctor_set_uint8(x_195, sizeof(void*)*1, x_196);
x_197 = lean_array_get_size(x_10);
x_198 = lean_array_push(x_10, x_195);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_192);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_16);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_16, 0);
x_203 = lean_io_error_to_string(x_202);
x_204 = lean_box(3);
x_205 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_205, 0, x_203);
x_206 = lean_unbox(x_204);
lean_ctor_set_uint8(x_205, sizeof(void*)*1, x_206);
x_207 = lean_array_get_size(x_10);
x_208 = lean_array_push(x_10, x_205);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
lean_ctor_set_tag(x_16, 0);
lean_ctor_set(x_16, 0, x_209);
return x_16;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_210 = lean_ctor_get(x_16, 0);
x_211 = lean_ctor_get(x_16, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_16);
x_212 = lean_io_error_to_string(x_210);
x_213 = lean_box(3);
x_214 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_214, 0, x_212);
x_215 = lean_unbox(x_213);
lean_ctor_set_uint8(x_214, sizeof(void*)*1, x_215);
x_216 = lean_array_get_size(x_10);
x_217 = lean_array_push(x_10, x_214);
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
block_229:
{
lean_object* x_222; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_10 = x_224;
x_11 = x_223;
goto block_220;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_221, 1);
lean_inc(x_225);
lean_dec(x_221);
x_226 = lean_ctor_get(x_222, 1);
lean_inc(x_226);
lean_dec(x_222);
x_227 = l_Lake_initPkg___lam__1___closed__10;
x_228 = lean_array_push(x_226, x_227);
x_10 = x_228;
x_11 = x_225;
goto block_220;
}
}
block_261:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_232 = l_Lake_initPkg___lam__1___closed__15;
x_233 = l_Lake_initPkg___lam__1___closed__16;
x_234 = l_Lake_initPkg___lam__1___closed__17;
lean_inc(x_1);
x_235 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_235, 0, x_1);
x_236 = l_Lake_initPkg___lam__1___closed__18;
x_237 = lean_box(1);
lean_inc(x_235);
x_238 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_238, 0, x_233);
lean_ctor_set(x_238, 1, x_234);
lean_ctor_set(x_238, 2, x_232);
lean_ctor_set(x_238, 3, x_235);
lean_ctor_set(x_238, 4, x_236);
x_239 = lean_unbox(x_237);
lean_ctor_set_uint8(x_238, sizeof(void*)*5, x_239);
lean_ctor_set_uint8(x_238, sizeof(void*)*5 + 1, x_4);
x_240 = l_Lake_testProc(x_238, x_231);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_unbox(x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; uint8_t x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; 
x_243 = lean_ctor_get(x_240, 1);
lean_inc(x_243);
lean_dec(x_240);
x_244 = l_Lake_initPkg___lam__1___closed__22;
lean_inc(x_235);
x_245 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_245, 0, x_233);
lean_ctor_set(x_245, 1, x_234);
lean_ctor_set(x_245, 2, x_244);
lean_ctor_set(x_245, 3, x_235);
lean_ctor_set(x_245, 4, x_236);
x_246 = lean_unbox(x_237);
lean_ctor_set_uint8(x_245, sizeof(void*)*5, x_246);
x_247 = lean_unbox(x_241);
lean_ctor_set_uint8(x_245, sizeof(void*)*5 + 1, x_247);
x_248 = lean_unbox(x_237);
x_249 = l_Lake_proc(x_245, x_248, x_230, x_243);
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
x_253 = l_Lake_initPkg___lam__1___closed__24;
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; uint8_t x_257; uint8_t x_258; lean_object* x_259; 
x_254 = l_Lake_initPkg___lam__1___closed__30;
x_255 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_255, 0, x_233);
lean_ctor_set(x_255, 1, x_234);
lean_ctor_set(x_255, 2, x_254);
lean_ctor_set(x_255, 3, x_235);
lean_ctor_set(x_255, 4, x_236);
x_256 = lean_unbox(x_237);
lean_ctor_set_uint8(x_255, sizeof(void*)*5, x_256);
x_257 = lean_unbox(x_241);
lean_dec(x_241);
lean_ctor_set_uint8(x_255, sizeof(void*)*5 + 1, x_257);
x_258 = lean_unbox(x_237);
x_259 = l_Lake_proc(x_255, x_258, x_252, x_251);
x_221 = x_259;
goto block_229;
}
else
{
lean_dec(x_241);
lean_dec(x_235);
x_10 = x_252;
x_11 = x_251;
goto block_220;
}
}
else
{
lean_dec(x_250);
lean_dec(x_241);
lean_dec(x_235);
x_221 = x_249;
goto block_229;
}
}
else
{
lean_object* x_260; 
lean_dec(x_241);
lean_dec(x_235);
x_260 = lean_ctor_get(x_240, 1);
lean_inc(x_260);
lean_dec(x_240);
x_10 = x_230;
x_11 = x_260;
goto block_220;
}
}
block_309:
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_263 = l_Lake_initPkg___lam__1___closed__31;
lean_inc(x_1);
x_264 = l_Lake_joinRelative(x_1, x_263);
x_265 = l_System_FilePath_pathExists(x_264, x_262);
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_unbox(x_266);
lean_dec(x_266);
if (x_267 == 0)
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_265);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_269 = lean_ctor_get(x_265, 1);
x_270 = lean_ctor_get(x_265, 0);
lean_dec(x_270);
x_271 = l_Lake_dotlessName(x_5);
x_272 = l_Lake_readmeFileContents(x_271);
lean_dec(x_271);
x_273 = l_IO_FS_writeFile(x_264, x_272, x_269);
lean_dec(x_272);
lean_dec(x_264);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
lean_free_object(x_265);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_230 = x_8;
x_231 = x_274;
goto block_261;
}
else
{
uint8_t x_275; 
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_273);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; lean_object* x_281; lean_object* x_282; 
x_276 = lean_ctor_get(x_273, 0);
x_277 = lean_io_error_to_string(x_276);
x_278 = lean_box(3);
x_279 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_279, 0, x_277);
x_280 = lean_unbox(x_278);
lean_ctor_set_uint8(x_279, sizeof(void*)*1, x_280);
x_281 = lean_array_get_size(x_8);
x_282 = lean_array_push(x_8, x_279);
lean_ctor_set_tag(x_265, 1);
lean_ctor_set(x_265, 1, x_282);
lean_ctor_set(x_265, 0, x_281);
lean_ctor_set_tag(x_273, 0);
lean_ctor_set(x_273, 0, x_265);
return x_273;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_283 = lean_ctor_get(x_273, 0);
x_284 = lean_ctor_get(x_273, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_273);
x_285 = lean_io_error_to_string(x_283);
x_286 = lean_box(3);
x_287 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_287, 0, x_285);
x_288 = lean_unbox(x_286);
lean_ctor_set_uint8(x_287, sizeof(void*)*1, x_288);
x_289 = lean_array_get_size(x_8);
x_290 = lean_array_push(x_8, x_287);
lean_ctor_set_tag(x_265, 1);
lean_ctor_set(x_265, 1, x_290);
lean_ctor_set(x_265, 0, x_289);
x_291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_291, 0, x_265);
lean_ctor_set(x_291, 1, x_284);
return x_291;
}
}
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_292 = lean_ctor_get(x_265, 1);
lean_inc(x_292);
lean_dec(x_265);
x_293 = l_Lake_dotlessName(x_5);
x_294 = l_Lake_readmeFileContents(x_293);
lean_dec(x_293);
x_295 = l_IO_FS_writeFile(x_264, x_294, x_292);
lean_dec(x_294);
lean_dec(x_264);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
x_230 = x_8;
x_231 = x_296;
goto block_261;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_1);
x_297 = lean_ctor_get(x_295, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_299 = x_295;
} else {
 lean_dec_ref(x_295);
 x_299 = lean_box(0);
}
x_300 = lean_io_error_to_string(x_297);
x_301 = lean_box(3);
x_302 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_302, 0, x_300);
x_303 = lean_unbox(x_301);
lean_ctor_set_uint8(x_302, sizeof(void*)*1, x_303);
x_304 = lean_array_get_size(x_8);
x_305 = lean_array_push(x_8, x_302);
x_306 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
if (lean_is_scalar(x_299)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_299;
 lean_ctor_set_tag(x_307, 0);
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_298);
return x_307;
}
}
}
else
{
lean_object* x_308; 
lean_dec(x_264);
lean_dec(x_5);
x_308 = lean_ctor_get(x_265, 1);
lean_inc(x_308);
lean_dec(x_265);
x_230 = x_8;
x_231 = x_308;
goto block_261;
}
}
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
x_1 = lean_mk_string_unchecked("lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_initPkg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Basic.lean", 10, 10);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = l_Lake_initPkg___closed__0;
x_9 = l_Lake_ConfigLang_fileExtension(x_4);
x_10 = l_System_FilePath_addExtension(x_8, x_9);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lake_joinRelative(x_1, x_10);
lean_dec(x_10);
x_12 = l_System_FilePath_pathExists(x_11, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_1);
x_16 = l_Lake_createLeanActionWorkflow(x_1, x_6, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_172; lean_object* x_184; uint8_t x_185; uint8_t x_186; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = l_Lake_initPkg___closed__1;
x_22 = l_Lean_modToFilePath(x_1, x_2, x_21);
x_23 = l_System_FilePath_pathExists(x_22, x_18);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
lean_inc(x_13);
x_27 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__0___boxed), 2, 1);
lean_closure_set(x_27, 0, x_13);
x_184 = lean_box(1);
x_185 = lean_unbox(x_184);
x_186 = l_Lake_instDecidableEqInitTemplate(x_3, x_185);
if (x_186 == 0)
{
uint8_t x_187; 
x_187 = lean_unbox(x_24);
lean_dec(x_24);
x_172 = x_187;
goto block_183;
}
else
{
lean_dec(x_24);
x_172 = x_186;
goto block_183;
}
block_60:
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_box(1);
x_34 = lean_unbox(x_33);
lean_inc(x_30);
x_35 = l_Lean_Name_toString(x_30, x_34, x_27);
x_36 = l_Lake_libRootFileContents(x_35, x_30);
lean_dec(x_35);
x_37 = l_IO_FS_writeFile(x_28, x_36, x_32);
lean_dec(x_36);
lean_dec(x_28);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_20);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_apply_3(x_29, x_38, x_31, x_39);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_29);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_37, 0);
x_43 = lean_io_error_to_string(x_42);
x_44 = lean_box(3);
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_unbox(x_44);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
x_47 = lean_array_get_size(x_31);
x_48 = lean_array_push(x_31, x_45);
if (lean_is_scalar(x_20)) {
 x_49 = lean_alloc_ctor(1, 2, 0);
} else {
 x_49 = x_20;
 lean_ctor_set_tag(x_49, 1);
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set_tag(x_37, 0);
lean_ctor_set(x_37, 0, x_49);
return x_37;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_50 = lean_ctor_get(x_37, 0);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_37);
x_52 = lean_io_error_to_string(x_50);
x_53 = lean_box(3);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
x_56 = lean_array_get_size(x_31);
x_57 = lean_array_push(x_31, x_54);
if (lean_is_scalar(x_20)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_20;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_51);
return x_59;
}
}
}
block_171:
{
lean_object* x_65; lean_object* x_66; 
lean_inc(x_61);
lean_inc(x_2);
x_65 = l_Lake_InitTemplate_configFileContents(x_3, x_4, x_2, x_61);
x_66 = l_IO_FS_writeFile(x_11, x_65, x_64);
lean_dec(x_65);
lean_dec(x_11);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_26);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_box(x_3);
lean_inc(x_61);
lean_inc(x_2);
lean_inc(x_13);
lean_inc(x_5);
lean_inc(x_1);
x_69 = lean_alloc_closure((void*)(l_Lake_initPkg___lam__1___boxed), 9, 6);
lean_closure_set(x_69, 0, x_1);
lean_closure_set(x_69, 1, x_5);
lean_closure_set(x_69, 2, x_68);
lean_closure_set(x_69, 3, x_13);
lean_closure_set(x_69, 4, x_2);
lean_closure_set(x_69, 5, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_70; uint8_t x_71; lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_27);
lean_dec(x_20);
x_70 = lean_box(0);
x_71 = lean_unbox(x_13);
lean_dec(x_13);
x_72 = l_Lake_initPkg___lam__1(x_1, x_5, x_3, x_71, x_2, x_61, x_70, x_63, x_67);
lean_dec(x_5);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_73 = lean_ctor_get(x_62, 0);
lean_inc(x_73);
lean_dec(x_62);
x_74 = l_Lake_escapeIdent___closed__0;
lean_inc(x_73);
x_75 = l_System_FilePath_withExtension(x_73, x_74);
x_76 = l_Lake_initPkg___closed__2;
lean_inc(x_75);
x_77 = l_Lake_joinRelative(x_75, x_76);
x_78 = l_System_FilePath_pathExists(x_77, x_67);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_78);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_78, 1);
x_83 = lean_ctor_get(x_78, 0);
lean_dec(x_83);
x_84 = l_IO_FS_createDirAll(x_75, x_82);
lean_dec(x_75);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lake_basicFileContents___closed__0;
x_87 = l_IO_FS_writeFile(x_77, x_86, x_85);
lean_dec(x_77);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
lean_free_object(x_78);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_28 = x_73;
x_29 = x_69;
x_30 = x_61;
x_31 = x_63;
x_32 = x_88;
goto block_60;
}
else
{
uint8_t x_89; 
lean_dec(x_73);
lean_dec(x_69);
lean_dec(x_61);
lean_dec(x_27);
lean_dec(x_20);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_87, 0);
x_91 = lean_io_error_to_string(x_90);
x_92 = lean_box(3);
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_91);
x_94 = lean_unbox(x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_94);
x_95 = lean_array_get_size(x_63);
x_96 = lean_array_push(x_63, x_93);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_96);
lean_ctor_set(x_78, 0, x_95);
lean_ctor_set_tag(x_87, 0);
lean_ctor_set(x_87, 0, x_78);
return x_87;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_87, 0);
x_98 = lean_ctor_get(x_87, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_87);
x_99 = lean_io_error_to_string(x_97);
x_100 = lean_box(3);
x_101 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_101, 0, x_99);
x_102 = lean_unbox(x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*1, x_102);
x_103 = lean_array_get_size(x_63);
x_104 = lean_array_push(x_63, x_101);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_104);
lean_ctor_set(x_78, 0, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_78);
lean_ctor_set(x_105, 1, x_98);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_69);
lean_dec(x_61);
lean_dec(x_27);
lean_dec(x_20);
x_106 = !lean_is_exclusive(x_84);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_84, 0);
x_108 = lean_io_error_to_string(x_107);
x_109 = lean_box(3);
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
x_111 = lean_unbox(x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_111);
x_112 = lean_array_get_size(x_63);
x_113 = lean_array_push(x_63, x_110);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_113);
lean_ctor_set(x_78, 0, x_112);
lean_ctor_set_tag(x_84, 0);
lean_ctor_set(x_84, 0, x_78);
return x_84;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_84, 0);
x_115 = lean_ctor_get(x_84, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_84);
x_116 = lean_io_error_to_string(x_114);
x_117 = lean_box(3);
x_118 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_118, 0, x_116);
x_119 = lean_unbox(x_117);
lean_ctor_set_uint8(x_118, sizeof(void*)*1, x_119);
x_120 = lean_array_get_size(x_63);
x_121 = lean_array_push(x_63, x_118);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_121);
lean_ctor_set(x_78, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_78);
lean_ctor_set(x_122, 1, x_115);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_78, 1);
lean_inc(x_123);
lean_dec(x_78);
x_124 = l_IO_FS_createDirAll(x_75, x_123);
lean_dec(x_75);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Lake_basicFileContents___closed__0;
x_127 = l_IO_FS_writeFile(x_77, x_126, x_125);
lean_dec(x_77);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_28 = x_73;
x_29 = x_69;
x_30 = x_61;
x_31 = x_63;
x_32 = x_128;
goto block_60;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_73);
lean_dec(x_69);
lean_dec(x_61);
lean_dec(x_27);
lean_dec(x_20);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_131 = x_127;
} else {
 lean_dec_ref(x_127);
 x_131 = lean_box(0);
}
x_132 = lean_io_error_to_string(x_129);
x_133 = lean_box(3);
x_134 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_134, 0, x_132);
x_135 = lean_unbox(x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_135);
x_136 = lean_array_get_size(x_63);
x_137 = lean_array_push(x_63, x_134);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
if (lean_is_scalar(x_131)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_131;
 lean_ctor_set_tag(x_139, 0);
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_130);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_69);
lean_dec(x_61);
lean_dec(x_27);
lean_dec(x_20);
x_140 = lean_ctor_get(x_124, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_124, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_142 = x_124;
} else {
 lean_dec_ref(x_124);
 x_142 = lean_box(0);
}
x_143 = lean_io_error_to_string(x_140);
x_144 = lean_box(3);
x_145 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_145, 0, x_143);
x_146 = lean_unbox(x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_146);
x_147 = lean_array_get_size(x_63);
x_148 = lean_array_push(x_63, x_145);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
if (lean_is_scalar(x_142)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_142;
 lean_ctor_set_tag(x_150, 0);
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_141);
return x_150;
}
}
}
else
{
lean_object* x_151; 
lean_dec(x_77);
lean_dec(x_75);
x_151 = lean_ctor_get(x_78, 1);
lean_inc(x_151);
lean_dec(x_78);
x_28 = x_73;
x_29 = x_69;
x_30 = x_61;
x_31 = x_63;
x_32 = x_151;
goto block_60;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_27);
lean_dec(x_20);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_66);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_153 = lean_ctor_get(x_66, 0);
x_154 = lean_io_error_to_string(x_153);
x_155 = lean_box(3);
x_156 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_156, 0, x_154);
x_157 = lean_unbox(x_155);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_157);
x_158 = lean_array_get_size(x_63);
x_159 = lean_array_push(x_63, x_156);
if (lean_is_scalar(x_26)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_26;
 lean_ctor_set_tag(x_160, 1);
}
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
lean_ctor_set_tag(x_66, 0);
lean_ctor_set(x_66, 0, x_160);
return x_66;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_66, 0);
x_162 = lean_ctor_get(x_66, 1);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_66);
x_163 = lean_io_error_to_string(x_161);
x_164 = lean_box(3);
x_165 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_165, 0, x_163);
x_166 = lean_unbox(x_164);
lean_ctor_set_uint8(x_165, sizeof(void*)*1, x_166);
x_167 = lean_array_get_size(x_63);
x_168 = lean_array_push(x_63, x_165);
if (lean_is_scalar(x_26)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_26;
 lean_ctor_set_tag(x_169, 1);
}
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_162);
return x_170;
}
}
}
block_183:
{
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
lean_dec(x_22);
x_173 = l_Lake_toUpperCamelCase(x_2);
x_174 = l_Lean_modToFilePath(x_1, x_173, x_21);
x_175 = l_System_FilePath_pathExists(x_174, x_25);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_unbox(x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
lean_dec(x_175);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_174);
x_61 = x_173;
x_62 = x_179;
x_63 = x_19;
x_64 = x_178;
goto block_171;
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_174);
x_180 = lean_ctor_get(x_175, 1);
lean_inc(x_180);
lean_dec(x_175);
x_181 = lean_box(0);
x_61 = x_173;
x_62 = x_181;
x_63 = x_19;
x_64 = x_180;
goto block_171;
}
}
else
{
lean_object* x_182; 
x_182 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_182, 0, x_22);
lean_inc(x_2);
x_61 = x_2;
x_62 = x_182;
x_63 = x_19;
x_64 = x_25;
goto block_171;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
else
{
uint8_t x_188; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_12);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_189 = lean_ctor_get(x_12, 0);
lean_dec(x_189);
x_190 = l_Lake_initPkg___closed__4;
x_191 = lean_array_get_size(x_6);
x_192 = lean_array_push(x_6, x_190);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set(x_12, 0, x_193);
return x_12;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_194 = lean_ctor_get(x_12, 1);
lean_inc(x_194);
lean_dec(x_12);
x_195 = l_Lake_initPkg___closed__4;
x_196 = lean_array_get_size(x_6);
x_197 = lean_array_push(x_6, x_195);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_194);
return x_199;
}
}
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
LEAN_EXPORT lean_object* l_Lake_initPkg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lake_initPkg___lam__1(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_2);
return x_12;
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
x_2 = l_Lake_initPkg___closed__1;
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
x_2 = l_Lake_initPkg___lam__1___closed__19;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_66; uint8_t x_67; 
x_66 = l_Lake_escapeName_x21___closed__4;
x_67 = lean_string_dec_eq(x_1, x_66);
if (x_67 == 0)
{
x_8 = x_1;
x_9 = x_6;
x_10 = x_7;
goto block_59;
}
else
{
lean_object* x_68; 
lean_dec(x_1);
lean_inc(x_5);
x_68 = lean_io_realpath(x_5, x_7);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_69);
x_71 = l_System_FilePath_fileName(x_69);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_5);
lean_dec(x_4);
x_72 = l_Lake_init___closed__0;
x_73 = lean_string_append(x_72, x_69);
lean_dec(x_69);
x_74 = l_Lake_createLeanActionWorkflow___closed__6;
x_75 = lean_string_append(x_73, x_74);
x_76 = lean_box(3);
x_77 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_77, 0, x_75);
x_78 = lean_unbox(x_76);
lean_ctor_set_uint8(x_77, sizeof(void*)*1, x_78);
x_79 = lean_array_get_size(x_6);
x_80 = lean_array_push(x_6, x_77);
x_60 = x_79;
x_61 = x_80;
x_62 = x_70;
goto block_65;
}
else
{
lean_object* x_81; 
lean_dec(x_69);
x_81 = lean_ctor_get(x_71, 0);
lean_inc(x_81);
lean_dec(x_71);
x_8 = x_81;
x_9 = x_6;
x_10 = x_70;
goto block_59;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_5);
lean_dec(x_4);
x_82 = lean_ctor_get(x_68, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_68, 1);
lean_inc(x_83);
lean_dec(x_68);
x_84 = lean_io_error_to_string(x_82);
x_85 = lean_box(3);
x_86 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
x_88 = lean_array_get_size(x_6);
x_89 = lean_array_push(x_6, x_86);
x_60 = x_88;
x_61 = x_89;
x_62 = x_83;
goto block_65;
}
}
block_59:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_byte_size(x_8);
x_13 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_8, x_12, x_11);
x_14 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_8, x_13, x_12);
x_15 = lean_string_utf8_extract(x_8, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_inc(x_15);
x_16 = l_Lake_validatePkgName(x_15, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = l_IO_FS_createDirAll(x_5, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_17);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lake_stringToLegalOrSimpleName(x_15);
x_25 = l_Lake_initPkg(x_5, x_24, x_2, x_3, x_4, x_20, x_23);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_22);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_22, 0);
x_28 = lean_io_error_to_string(x_27);
x_29 = lean_box(3);
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_31);
x_32 = lean_array_get_size(x_20);
x_33 = lean_array_push(x_20, x_30);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_33);
lean_ctor_set(x_17, 0, x_32);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_17);
return x_22;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_22, 0);
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_22);
x_36 = lean_io_error_to_string(x_34);
x_37 = lean_box(3);
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_unbox(x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_39);
x_40 = lean_array_get_size(x_20);
x_41 = lean_array_push(x_20, x_38);
lean_ctor_set_tag(x_17, 1);
lean_ctor_set(x_17, 1, x_41);
lean_ctor_set(x_17, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_35);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_dec(x_17);
x_44 = l_IO_FS_createDirAll(x_5, x_18);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lake_stringToLegalOrSimpleName(x_15);
x_47 = l_Lake_initPkg(x_5, x_46, x_2, x_3, x_4, x_43, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_50 = x_44;
} else {
 lean_dec_ref(x_44);
 x_50 = lean_box(0);
}
x_51 = lean_io_error_to_string(x_48);
x_52 = lean_box(3);
x_53 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = lean_array_get_size(x_43);
x_56 = lean_array_push(x_43, x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_50;
 lean_ctor_set_tag(x_58, 0);
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
}
}
else
{
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
block_65:
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_1, x_9, x_8);
x_11 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_1, x_10, x_9);
x_12 = lean_string_utf8_extract(x_1, x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
lean_inc(x_12);
x_13 = l_Lake_validatePkgName(x_12, x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = l_Lake_stringToLegalOrSimpleName(x_12);
lean_inc(x_19);
x_20 = l_Lake_dotlessName(x_19);
x_21 = l_Lake_joinRelative(x_5, x_20);
lean_dec(x_20);
x_22 = l_IO_FS_createDirAll(x_21, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_14);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lake_initPkg(x_21, x_19, x_2, x_3, x_4, x_17, x_23);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_22, 0);
x_27 = lean_io_error_to_string(x_26);
x_28 = lean_box(3);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
x_31 = lean_array_get_size(x_17);
x_32 = lean_array_push(x_17, x_29);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_32);
lean_ctor_set(x_14, 0, x_31);
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_14);
return x_22;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_22, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_22);
x_35 = lean_io_error_to_string(x_33);
x_36 = lean_box(3);
x_37 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = lean_array_get_size(x_17);
x_40 = lean_array_push(x_17, x_37);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_40);
lean_ctor_set(x_14, 0, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_41, 1, x_34);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_dec(x_14);
x_43 = l_Lake_stringToLegalOrSimpleName(x_12);
lean_inc(x_43);
x_44 = l_Lake_dotlessName(x_43);
x_45 = l_Lake_joinRelative(x_5, x_44);
lean_dec(x_44);
x_46 = l_IO_FS_createDirAll(x_45, x_15);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lake_initPkg(x_45, x_43, x_2, x_3, x_4, x_42, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_4);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_51 = x_46;
} else {
 lean_dec_ref(x_46);
 x_51 = lean_box(0);
}
x_52 = lean_io_error_to_string(x_49);
x_53 = lean_box(3);
x_54 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
x_56 = lean_array_get_size(x_42);
x_57 = lean_array_push(x_42, x_54);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
if (lean_is_scalar(x_51)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_51;
 lean_ctor_set_tag(x_59, 0);
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_50);
return x_59;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
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
l_Lake_mainFileName___closed__0 = _init_l_Lake_mainFileName___closed__0();
lean_mark_persistent(l_Lake_mainFileName___closed__0);
l_Lake_mainFileName___closed__1 = _init_l_Lake_mainFileName___closed__1();
lean_mark_persistent(l_Lake_mainFileName___closed__1);
l_Lake_mainFileName___closed__2 = _init_l_Lake_mainFileName___closed__2();
lean_mark_persistent(l_Lake_mainFileName___closed__2);
l_Lake_mainFileName___closed__3 = _init_l_Lake_mainFileName___closed__3();
lean_mark_persistent(l_Lake_mainFileName___closed__3);
l_Lake_mainFileName = _init_l_Lake_mainFileName();
lean_mark_persistent(l_Lake_mainFileName);
l_Lake_mainFileContents___closed__0 = _init_l_Lake_mainFileContents___closed__0();
lean_mark_persistent(l_Lake_mainFileContents___closed__0);
l_Lake_mainFileContents___closed__1 = _init_l_Lake_mainFileContents___closed__1();
lean_mark_persistent(l_Lake_mainFileContents___closed__1);
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
l_Lake_mathLeanConfigFileContents___closed__0 = _init_l_Lake_mathLeanConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_mathLeanConfigFileContents___closed__0);
l_Lake_mathLeanConfigFileContents___closed__1 = _init_l_Lake_mathLeanConfigFileContents___closed__1();
lean_mark_persistent(l_Lake_mathLeanConfigFileContents___closed__1);
l_Lake_mathTomlConfigFileContents___closed__0 = _init_l_Lake_mathTomlConfigFileContents___closed__0();
lean_mark_persistent(l_Lake_mathTomlConfigFileContents___closed__0);
l_Lake_mathTomlConfigFileContents___closed__1 = _init_l_Lake_mathTomlConfigFileContents___closed__1();
lean_mark_persistent(l_Lake_mathTomlConfigFileContents___closed__1);
l_Lake_readmeFileContents___closed__0 = _init_l_Lake_readmeFileContents___closed__0();
lean_mark_persistent(l_Lake_readmeFileContents___closed__0);
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
l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__0____x40_Lake_CLI_Init___hyg_412_);
l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__1____x40_Lake_CLI_Init___hyg_412_);
l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__2____x40_Lake_CLI_Init___hyg_412_);
l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__3____x40_Lake_CLI_Init___hyg_412_);
l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__4____x40_Lake_CLI_Init___hyg_412_);
l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__5____x40_Lake_CLI_Init___hyg_412_);
l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__6____x40_Lake_CLI_Init___hyg_412_);
l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__7____x40_Lake_CLI_Init___hyg_412_);
l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__8____x40_Lake_CLI_Init___hyg_412_);
l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_412_ = _init_l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_412_();
lean_mark_persistent(l_Lake_reprInitTemplate___closed__9____x40_Lake_CLI_Init___hyg_412_);
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
l_Lake_initPkg___lam__1___closed__0 = _init_l_Lake_initPkg___lam__1___closed__0();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__0);
l_Lake_initPkg___lam__1___closed__1 = _init_l_Lake_initPkg___lam__1___closed__1();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__1);
l_Lake_initPkg___lam__1___closed__2 = _init_l_Lake_initPkg___lam__1___closed__2();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__2);
l_Lake_initPkg___lam__1___closed__3 = _init_l_Lake_initPkg___lam__1___closed__3();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__3);
l_Lake_initPkg___lam__1___closed__4 = _init_l_Lake_initPkg___lam__1___closed__4();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__4);
l_Lake_initPkg___lam__1___closed__5 = _init_l_Lake_initPkg___lam__1___closed__5();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__5);
l_Lake_initPkg___lam__1___closed__6 = _init_l_Lake_initPkg___lam__1___closed__6();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__6);
l_Lake_initPkg___lam__1___closed__7 = _init_l_Lake_initPkg___lam__1___closed__7();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__7);
l_Lake_initPkg___lam__1___closed__8 = _init_l_Lake_initPkg___lam__1___closed__8();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__8);
l_Lake_initPkg___lam__1___closed__9 = _init_l_Lake_initPkg___lam__1___closed__9();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__9);
l_Lake_initPkg___lam__1___closed__10 = _init_l_Lake_initPkg___lam__1___closed__10();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__10);
l_Lake_initPkg___lam__1___closed__11 = _init_l_Lake_initPkg___lam__1___closed__11();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__11);
l_Lake_initPkg___lam__1___closed__12 = _init_l_Lake_initPkg___lam__1___closed__12();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__12);
l_Lake_initPkg___lam__1___closed__13 = _init_l_Lake_initPkg___lam__1___closed__13();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__13);
l_Lake_initPkg___lam__1___closed__14 = _init_l_Lake_initPkg___lam__1___closed__14();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__14);
l_Lake_initPkg___lam__1___closed__15 = _init_l_Lake_initPkg___lam__1___closed__15();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__15);
l_Lake_initPkg___lam__1___closed__16 = _init_l_Lake_initPkg___lam__1___closed__16();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__16);
l_Lake_initPkg___lam__1___closed__17 = _init_l_Lake_initPkg___lam__1___closed__17();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__17);
l_Lake_initPkg___lam__1___closed__18 = _init_l_Lake_initPkg___lam__1___closed__18();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__18);
l_Lake_initPkg___lam__1___closed__19 = _init_l_Lake_initPkg___lam__1___closed__19();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__19);
l_Lake_initPkg___lam__1___closed__20 = _init_l_Lake_initPkg___lam__1___closed__20();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__20);
l_Lake_initPkg___lam__1___closed__21 = _init_l_Lake_initPkg___lam__1___closed__21();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__21);
l_Lake_initPkg___lam__1___closed__22 = _init_l_Lake_initPkg___lam__1___closed__22();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__22);
l_Lake_initPkg___lam__1___closed__23 = _init_l_Lake_initPkg___lam__1___closed__23();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__23);
l_Lake_initPkg___lam__1___closed__24 = _init_l_Lake_initPkg___lam__1___closed__24();
l_Lake_initPkg___lam__1___closed__25 = _init_l_Lake_initPkg___lam__1___closed__25();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__25);
l_Lake_initPkg___lam__1___closed__26 = _init_l_Lake_initPkg___lam__1___closed__26();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__26);
l_Lake_initPkg___lam__1___closed__27 = _init_l_Lake_initPkg___lam__1___closed__27();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__27);
l_Lake_initPkg___lam__1___closed__28 = _init_l_Lake_initPkg___lam__1___closed__28();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__28);
l_Lake_initPkg___lam__1___closed__29 = _init_l_Lake_initPkg___lam__1___closed__29();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__29);
l_Lake_initPkg___lam__1___closed__30 = _init_l_Lake_initPkg___lam__1___closed__30();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__30);
l_Lake_initPkg___lam__1___closed__31 = _init_l_Lake_initPkg___lam__1___closed__31();
lean_mark_persistent(l_Lake_initPkg___lam__1___closed__31);
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
l_Lake_init___closed__0 = _init_l_Lake_init___closed__0();
lean_mark_persistent(l_Lake_init___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
