// Lean compiler output
// Module: Lean.Shell
// Imports: Lean.Elab.Frontend Lean.Elab.ParseImportsFast Lean.Compiler.IR.EmitC
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
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__1;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__2;
uint8_t lean_internal_is_debug(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__10;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__0;
extern lean_object* l_Lean_githash;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__29;
lean_object* l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_decode_lossy_utf8(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__2;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__5;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__9;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__5;
lean_object* l_Lean_Elab_printImports(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__40;
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__2;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__6;
lean_object* l_IO_FS_Stream_lines(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__30;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__21;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__38;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__3;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__11;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__25;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__26;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__7;
lean_object* l_Lean_moduleNameOfFileName(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__8;
uint8_t l_List_isEmpty___redArg(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__6;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__23;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__13;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__0;
extern uint8_t l_Lean_version_isRelease;
lean_object* lean_string_utf8_byte_size(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__27;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__16;
lean_object* lean_get_stdout(lean_object*);
LEAN_EXPORT lean_object* lean_display_header(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object**);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__18;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__10;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__20;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__8;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__15;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__13;
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__36;
lean_object* l_IO_FS_Stream_readBinToEnd(lean_object*, lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__5;
lean_object* lean_emit_llvm(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__5;
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__4;
lean_object* l_Lean_Elab_printImportSrcs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__19;
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__0;
lean_object* lean_get_stdin(lean_object*);
static uint8_t l___private_Lean_Shell_0__Lean_displayHelp___closed__12;
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
lean_object* lean_get_stderr(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__6;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__9;
lean_object* lean_io_prim_handle_write(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object*);
lean_object* lean_io_prim_handle_mk(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__34;
lean_object* l_Lean_ModuleSetup_load(lean_object*, lean_object*);
lean_object* lean_internal_get_build_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object*);
lean_object* l_IO_println___at___Lean_Environment_displayStats_spec__2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__7;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__37;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__17;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__11;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__14;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_runFrontend(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__10;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__7;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__35;
static uint8_t l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__4;
LEAN_EXPORT lean_object* lean_shell_main(lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* lean_run_main(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__24;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__3;
static lean_object* l___private_Lean_Shell_0__Lean_versionHeader___closed__3;
lean_object* lean_init_llvm(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_io_exit(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lean_display_help(uint8_t, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
extern lean_object* l_Lean_versionStringCore;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__28;
uint8_t l_Substring_beq(lean_object*, lean_object*);
lean_object* lean_display_cumulative_profiling_times(lean_object*);
uint8_t lean_internal_has_address_sanitizer(lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__4;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__1;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shortVersionString;
lean_object* l_IO_FS_Stream_putStrLn(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__33;
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_internal_is_multi_thread(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__32;
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2;
extern lean_object* l_System_Platform_target;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__14;
extern lean_object* l_Lean_version_specialDesc;
lean_object* l_Lean_printImportsJson(lean_object*, lean_object*);
static lean_object* l___private_Lean_Shell_0__Lean_shortVersionString___closed__3;
static lean_object* l___private_Lean_Shell_0__Lean_shellMain___closed__4;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__39;
static lean_object* l___private_Lean_Shell_0__Lean_displayHelp___closed__31;
static uint8_t l___private_Lean_Shell_0__Lean_versionHeader___closed__8;
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_ir_emit_c(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_versionHeader;
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_decodeLossyUTF8___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_decode_lossy_utf8(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_runMain___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_run_main(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_initLLVM___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_init_llvm(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_emitLLVM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_emit_llvm(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayCumulativeProfilingTimes___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_display_cumulative_profiling_times(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_hasAddressSanitizer___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_has_address_sanitizer(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isMultiThread___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_is_multi_thread(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_isDebug___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_internal_is_debug(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_Internal_getBuildType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_internal_get_build_type(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
x_2 = l_Lean_version_specialDesc;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__1;
x_2 = l_instDecidableNot___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-pre", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__3;
x_2 = l_Lean_versionStringCore;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__5;
x_2 = l_Lean_versionStringCore;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_version_specialDesc;
x_2 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__6;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shortVersionString() {
_start:
{
uint8_t x_1; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__2;
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = l_Lean_version_isRelease;
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__4;
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Lean_versionStringCore;
return x_4;
}
}
else
{
lean_object* x_5; 
x_5 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__7;
return x_5;
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean (version ", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_get_build_type(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")", 1, 1);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
x_2 = l_Lean_githash;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__5() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = l___private_Lean_Shell_0__Lean_versionHeader___closed__4;
x_2 = l_instDecidableNot___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", commit ", 9, 9);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; 
x_1 = l___private_Lean_Shell_0__Lean_shortVersionString___closed__0;
x_2 = l_System_Platform_target;
x_3 = lean_string_dec_eq(x_2, x_1);
return x_3;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = l___private_Lean_Shell_0__Lean_versionHeader___closed__7;
x_2 = l_instDecidableNot___redArg(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Shell_0__Lean_versionHeader___closed__1;
x_2 = l___private_Lean_Shell_0__Lean_shortVersionString;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_System_Platform_target;
x_2 = l___private_Lean_Shell_0__Lean_versionHeader___closed__9;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_versionHeader() {
_start:
{
lean_object* x_1; lean_object* x_11; lean_object* x_18; uint8_t x_19; 
x_18 = l___private_Lean_Shell_0__Lean_shortVersionString;
x_19 = l___private_Lean_Shell_0__Lean_versionHeader___closed__8;
if (x_19 == 0)
{
x_11 = x_18;
goto block_17;
}
else
{
lean_object* x_20; 
x_20 = l___private_Lean_Shell_0__Lean_versionHeader___closed__10;
x_11 = x_20;
goto block_17;
}
block_10:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l___private_Lean_Shell_0__Lean_versionHeader___closed__0;
x_3 = lean_string_append(x_2, x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Shell_0__Lean_versionHeader___closed__1;
x_5 = lean_string_append(x_3, x_4);
x_6 = l___private_Lean_Shell_0__Lean_versionHeader___closed__2;
x_7 = lean_string_append(x_5, x_6);
x_8 = l___private_Lean_Shell_0__Lean_versionHeader___closed__3;
x_9 = lean_string_append(x_7, x_8);
return x_9;
}
block_17:
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_githash;
x_13 = l___private_Lean_Shell_0__Lean_versionHeader___closed__5;
if (x_13 == 0)
{
x_1 = x_11;
goto block_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lean_Shell_0__Lean_versionHeader___closed__6;
x_15 = lean_string_append(x_11, x_14);
x_16 = lean_string_append(x_15, x_12);
x_1 = x_16;
goto block_10;
}
}
}
}
LEAN_EXPORT lean_object* lean_display_header(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Lean_Shell_0__Lean_versionHeader;
x_3 = l_IO_println___at___Lean_Environment_displayStats_spec__2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      -D name=value      set a configuration option (see set_option command)", 76, 76);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --plugin=file      load and initialize Lean shared library for registering linters etc.", 93, 93);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --load-dynlib=file load shared library to make its symbols available to the interpreter", 93, 93);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --setup=file       JSON file with module setup data (supersedes the file's header)", 88, 88);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --json             report Lean output (e.g., messages) as JSON (one per line)", 83, 83);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -E  --error=kind       report Lean messages of kind as errors", 63, 63);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --deps             just print dependencies of a Lean input", 64, 64);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --src-deps         just print dependency sources of a Lean input", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --print-prefix     print the installation prefix for Lean and exit", 72, 72);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --print-libdir     print the installation directory for Lean's built-in libraries and exit", 96, 96);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --profile          display elaboration/type checking time for each definition/theorem", 91, 91);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --stats            display environment statistics", 55, 55);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_is_debug(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --debug=tag        enable assertions with the given tag", 61, 61);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Miscellaneous", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -h, --help             display this message", 45, 45);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --features         display features compiler provides (eg. LLVM support)", 78, 78);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -v, --version          display version information", 52, 52);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -V, --short-version    display short version number", 53, 53);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -g, --githash          display the git commit hash number used to build this binary", 85, 85);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --run <file>       call the 'main' definition in the given file with the remaining arguments", 98, 98);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -o, --o=oname          create olean file", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -i, --i=iname          create ilean file", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -c, --c=fname          name of the C output file", 50, 50);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -b, --bc=fname         name of the LLVM bitcode file", 54, 54);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --stdin            take input from stdin", 46, 46);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --root=dir         set package root directory from which the module name\n", 79, 79);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         of the input file is calculated\n", 57, 57);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         (default: current working directory)\n", 62, 62);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -t, --trust=num        trust level (default: max) 0 means do not trust any macro,\n", 84, 84);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         and type check all imported modules\n", 61, 61);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -q, --quiet            do not print verbose messages", 54, 54);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -M, --memory=num       maximum amount of memory that should be used by Lean", 77, 77);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         (in megabytes)", 39, 39);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -T, --timeout=num      maximum number of memory allocations per task", 70, 70);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("                         this is a deterministic way of interrupting long running tasks", 87, 87);
return x_1;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_is_multi_thread(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -j, --threads=num      number of threads used to process lean files", 69, 69);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("  -s, --tstack=num       thread stack size in Kb", 48, 48);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --server           start lean in server mode", 50, 50);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("      --worker           start lean in server-worker mode", 57, 57);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_display_help(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_48; lean_object* x_49; 
if (x_1 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_get_stdout(x_2);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_48 = x_134;
x_49 = x_135;
goto block_132;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_get_stderr(x_2);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_48 = x_137;
x_49 = x_138;
goto block_132;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l___private_Lean_Shell_0__Lean_displayHelp___closed__0;
x_6 = l_IO_FS_Stream_putStrLn(x_3, x_5, x_4);
return x_6;
}
block_47:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l___private_Lean_Shell_0__Lean_displayHelp___closed__1;
lean_inc(x_8);
x_11 = l_IO_FS_Stream_putStrLn(x_8, x_10, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l___private_Lean_Shell_0__Lean_displayHelp___closed__2;
lean_inc(x_8);
x_14 = l_IO_FS_Stream_putStrLn(x_8, x_13, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l___private_Lean_Shell_0__Lean_displayHelp___closed__3;
lean_inc(x_8);
x_17 = l_IO_FS_Stream_putStrLn(x_8, x_16, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l___private_Lean_Shell_0__Lean_displayHelp___closed__4;
lean_inc(x_8);
x_20 = l_IO_FS_Stream_putStrLn(x_8, x_19, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l___private_Lean_Shell_0__Lean_displayHelp___closed__5;
lean_inc(x_8);
x_23 = l_IO_FS_Stream_putStrLn(x_8, x_22, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = l___private_Lean_Shell_0__Lean_displayHelp___closed__6;
lean_inc(x_8);
x_26 = l_IO_FS_Stream_putStrLn(x_8, x_25, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Shell_0__Lean_displayHelp___closed__7;
lean_inc(x_8);
x_29 = l_IO_FS_Stream_putStrLn(x_8, x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l___private_Lean_Shell_0__Lean_displayHelp___closed__8;
lean_inc(x_8);
x_32 = l_IO_FS_Stream_putStrLn(x_8, x_31, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l___private_Lean_Shell_0__Lean_displayHelp___closed__9;
lean_inc(x_8);
x_35 = l_IO_FS_Stream_putStrLn(x_8, x_34, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l___private_Lean_Shell_0__Lean_displayHelp___closed__10;
lean_inc(x_8);
x_38 = l_IO_FS_Stream_putStrLn(x_8, x_37, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l___private_Lean_Shell_0__Lean_displayHelp___closed__11;
lean_inc(x_8);
x_41 = l_IO_FS_Stream_putStrLn(x_8, x_40, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l___private_Lean_Shell_0__Lean_displayHelp___closed__12;
if (x_43 == 0)
{
x_3 = x_8;
x_4 = x_42;
goto block_7;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l___private_Lean_Shell_0__Lean_displayHelp___closed__13;
lean_inc(x_8);
x_45 = l_IO_FS_Stream_putStrLn(x_8, x_44, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_3 = x_8;
x_4 = x_46;
goto block_7;
}
else
{
lean_dec(x_8);
return x_45;
}
}
}
else
{
lean_dec(x_8);
return x_41;
}
}
else
{
lean_dec(x_8);
return x_38;
}
}
else
{
lean_dec(x_8);
return x_35;
}
}
else
{
lean_dec(x_8);
return x_32;
}
}
else
{
lean_dec(x_8);
return x_29;
}
}
else
{
lean_dec(x_8);
return x_26;
}
}
else
{
lean_dec(x_8);
return x_23;
}
}
else
{
lean_dec(x_8);
return x_20;
}
}
else
{
lean_dec(x_8);
return x_17;
}
}
else
{
lean_dec(x_8);
return x_14;
}
}
else
{
lean_dec(x_8);
return x_11;
}
}
block_132:
{
lean_object* x_50; lean_object* x_51; 
x_50 = l___private_Lean_Shell_0__Lean_versionHeader;
lean_inc(x_48);
x_51 = l_IO_FS_Stream_putStrLn(x_48, x_50, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l___private_Lean_Shell_0__Lean_displayHelp___closed__14;
lean_inc(x_48);
x_54 = l_IO_FS_Stream_putStrLn(x_48, x_53, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = l___private_Lean_Shell_0__Lean_displayHelp___closed__15;
lean_inc(x_48);
x_57 = l_IO_FS_Stream_putStrLn(x_48, x_56, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = l___private_Lean_Shell_0__Lean_displayHelp___closed__16;
lean_inc(x_48);
x_60 = l_IO_FS_Stream_putStrLn(x_48, x_59, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l___private_Lean_Shell_0__Lean_displayHelp___closed__17;
lean_inc(x_48);
x_63 = l_IO_FS_Stream_putStrLn(x_48, x_62, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l___private_Lean_Shell_0__Lean_displayHelp___closed__18;
lean_inc(x_48);
x_66 = l_IO_FS_Stream_putStrLn(x_48, x_65, x_64);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l___private_Lean_Shell_0__Lean_displayHelp___closed__19;
lean_inc(x_48);
x_69 = l_IO_FS_Stream_putStrLn(x_48, x_68, x_67);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l___private_Lean_Shell_0__Lean_displayHelp___closed__20;
lean_inc(x_48);
x_72 = l_IO_FS_Stream_putStrLn(x_48, x_71, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l___private_Lean_Shell_0__Lean_displayHelp___closed__21;
lean_inc(x_48);
x_75 = l_IO_FS_Stream_putStrLn(x_48, x_74, x_73);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l___private_Lean_Shell_0__Lean_displayHelp___closed__22;
lean_inc(x_48);
x_78 = l_IO_FS_Stream_putStrLn(x_48, x_77, x_76);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l___private_Lean_Shell_0__Lean_displayHelp___closed__23;
lean_inc(x_48);
x_81 = l_IO_FS_Stream_putStrLn(x_48, x_80, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l___private_Lean_Shell_0__Lean_displayHelp___closed__24;
lean_inc(x_48);
x_84 = l_IO_FS_Stream_putStrLn(x_48, x_83, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l___private_Lean_Shell_0__Lean_displayHelp___closed__25;
lean_inc(x_48);
x_87 = l_IO_FS_Stream_putStrLn(x_48, x_86, x_85);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = l___private_Lean_Shell_0__Lean_displayHelp___closed__26;
lean_inc(x_48);
x_90 = l_IO_FS_Stream_putStrLn(x_48, x_89, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = l___private_Lean_Shell_0__Lean_displayHelp___closed__27;
lean_inc(x_48);
x_93 = l_IO_FS_Stream_putStrLn(x_48, x_92, x_91);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l___private_Lean_Shell_0__Lean_displayHelp___closed__28;
lean_inc(x_48);
x_96 = l_IO_FS_Stream_putStrLn(x_48, x_95, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l___private_Lean_Shell_0__Lean_displayHelp___closed__29;
lean_inc(x_48);
x_99 = l_IO_FS_Stream_putStrLn(x_48, x_98, x_97);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_101 = l___private_Lean_Shell_0__Lean_displayHelp___closed__30;
lean_inc(x_48);
x_102 = l_IO_FS_Stream_putStrLn(x_48, x_101, x_100);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l___private_Lean_Shell_0__Lean_displayHelp___closed__31;
lean_inc(x_48);
x_105 = l_IO_FS_Stream_putStrLn(x_48, x_104, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = l___private_Lean_Shell_0__Lean_displayHelp___closed__32;
lean_inc(x_48);
x_108 = l_IO_FS_Stream_putStrLn(x_48, x_107, x_106);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l___private_Lean_Shell_0__Lean_displayHelp___closed__33;
lean_inc(x_48);
x_111 = l_IO_FS_Stream_putStrLn(x_48, x_110, x_109);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l___private_Lean_Shell_0__Lean_displayHelp___closed__34;
lean_inc(x_48);
x_114 = l_IO_FS_Stream_putStrLn(x_48, x_113, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l___private_Lean_Shell_0__Lean_displayHelp___closed__35;
lean_inc(x_48);
x_117 = l_IO_FS_Stream_putStrLn(x_48, x_116, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
lean_dec(x_117);
x_119 = l___private_Lean_Shell_0__Lean_displayHelp___closed__36;
if (x_119 == 0)
{
x_8 = x_48;
x_9 = x_118;
goto block_47;
}
else
{
lean_object* x_120; lean_object* x_121; 
x_120 = l___private_Lean_Shell_0__Lean_displayHelp___closed__37;
lean_inc(x_48);
x_121 = l_IO_FS_Stream_putStrLn(x_48, x_120, x_118);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = l___private_Lean_Shell_0__Lean_displayHelp___closed__38;
lean_inc(x_48);
x_124 = l_IO_FS_Stream_putStrLn(x_48, x_123, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l___private_Lean_Shell_0__Lean_displayHelp___closed__39;
lean_inc(x_48);
x_127 = l_IO_FS_Stream_putStrLn(x_48, x_126, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l___private_Lean_Shell_0__Lean_displayHelp___closed__40;
lean_inc(x_48);
x_130 = l_IO_FS_Stream_putStrLn(x_48, x_129, x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
lean_dec(x_130);
x_8 = x_48;
x_9 = x_131;
goto block_47;
}
else
{
lean_dec(x_48);
return x_130;
}
}
else
{
lean_dec(x_48);
return x_127;
}
}
else
{
lean_dec(x_48);
return x_124;
}
}
else
{
lean_dec(x_48);
return x_121;
}
}
}
else
{
lean_dec(x_48);
return x_117;
}
}
else
{
lean_dec(x_48);
return x_114;
}
}
else
{
lean_dec(x_48);
return x_111;
}
}
else
{
lean_dec(x_48);
return x_108;
}
}
else
{
lean_dec(x_48);
return x_105;
}
}
else
{
lean_dec(x_48);
return x_102;
}
}
else
{
lean_dec(x_48);
return x_99;
}
}
else
{
lean_dec(x_48);
return x_96;
}
}
else
{
lean_dec(x_48);
return x_93;
}
}
else
{
lean_dec(x_48);
return x_90;
}
}
else
{
lean_dec(x_48);
return x_87;
}
}
else
{
lean_dec(x_48);
return x_84;
}
}
else
{
lean_dec(x_48);
return x_81;
}
}
else
{
lean_dec(x_48);
return x_78;
}
}
else
{
lean_dec(x_48);
return x_75;
}
}
else
{
lean_dec(x_48);
return x_72;
}
}
else
{
lean_dec(x_48);
return x_69;
}
}
else
{
lean_dec(x_48);
return x_66;
}
}
else
{
lean_dec(x_48);
return x_63;
}
}
else
{
lean_dec(x_48);
return x_60;
}
}
else
{
lean_dec(x_48);
return x_57;
}
}
else
{
lean_dec(x_48);
return x_54;
}
}
else
{
lean_dec(x_48);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_displayHelp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_display_help(x_3, x_2);
return x_4;
}
}
static uint8_t _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_internal_has_address_sanitizer(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_13; 
x_4 = lean_display_cumulative_profiling_times(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_6 = x_4;
} else {
 lean_dec_ref(x_4);
 x_6 = lean_box(0);
}
x_13 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0;
if (x_13 == 0)
{
lean_dec(x_6);
if (lean_obj_tag(x_1) == 0)
{
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; 
x_14 = 1;
x_15 = lean_io_exit(x_14, x_5);
return x_15;
}
else
{
goto block_12;
}
}
else
{
goto block_12;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
goto block_9;
}
else
{
if (x_13 == 0)
{
goto block_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_16 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2;
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1;
if (lean_is_scalar(x_6)) {
 x_8 = lean_alloc_ctor(0, 2, 0);
} else {
 x_8 = x_6;
}
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
block_12:
{
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = lean_io_exit(x_10, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0___redArg(x_1, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_string_to_utf8(x_5);
lean_dec(x_5);
x_8 = lean_io_prim_handle_write(x_2, x_7, x_6);
lean_dec(x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_4);
if (x_9 == 0)
{
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LLVM code generation", 20, 20);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("C code generation", 17, 17);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to create '", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_stdin", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Shell_0__Lean_shellMain___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("#lang", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Shell_0__Lean_shellMain___closed__7;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Shell_0__Lean_shellMain___closed__8;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_Shell_0__Lean_shellMain___closed__7;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean4", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown language '", 18, 18);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'\n", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Expected exactly one file name", 30, 30);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("<stdin>", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_shell_main(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, uint32_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, uint8_t x_16, uint8_t x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_233; uint8_t x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; uint8_t x_240; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_274; uint8_t x_275; lean_object* x_276; uint8_t x_277; uint8_t x_298; lean_object* x_299; lean_object* x_300; uint8_t x_304; lean_object* x_310; lean_object* x_311; 
if (x_3 == 0)
{
x_304 = x_3;
goto block_309;
}
else
{
if (x_5 == 0)
{
x_304 = x_5;
goto block_309;
}
else
{
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
if (x_2 == 0)
{
lean_object* x_324; 
x_324 = lean_array_mk(x_1);
x_310 = x_324;
x_311 = x_18;
goto block_323;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_1);
x_325 = lean_get_stdin(x_18);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = l_IO_FS_Stream_lines(x_326, x_327);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_310 = x_329;
x_311 = x_330;
goto block_323;
}
else
{
uint8_t x_331; 
x_331 = !lean_is_exclusive(x_328);
if (x_331 == 0)
{
return x_328;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_328, 0);
x_333 = lean_ctor_get(x_328, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_328);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
}
}
block_43:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_6);
x_23 = lean_box(0);
x_24 = lean_apply_2(x_19, x_23, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_init_llvm(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = l___private_Lean_Shell_0__Lean_shellMain___closed__0;
x_29 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_emitLLVM___boxed), 4, 3);
lean_closure_set(x_29, 0, x_20);
lean_closure_set(x_29, 1, x_21);
lean_closure_set(x_29, 2, x_25);
x_30 = lean_box(0);
x_31 = l_Lean_profileitIOUnsafe___redArg(x_28, x_6, x_29, x_30, x_27);
lean_dec(x_6);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_2(x_19, x_32, x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_19);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_31);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
block_102:
{
lean_object* x_51; lean_object* x_52; 
x_51 = l___private_Lean_Shell_0__Lean_shellMain___closed__1;
lean_inc(x_49);
lean_inc(x_6);
x_52 = l_Lean_Elab_runFrontend(x_45, x_6, x_48, x_49, x_7, x_10, x_11, x_14, x_15, x_51, x_16, x_47, x_50);
lean_dec(x_15);
lean_dec(x_11);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
lean_inc(x_53);
x_55 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 3, 1);
lean_closure_set(x_55, 0, x_53);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_56 = lean_box(0);
x_57 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_53, x_56, x_54);
return x_57;
}
else
{
if (x_46 == 0)
{
lean_dec(x_44);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
lean_dec(x_53);
x_19 = x_55;
x_20 = x_58;
x_21 = x_49;
x_22 = x_54;
goto block_43;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
lean_dec(x_53);
x_60 = lean_ctor_get(x_12, 0);
lean_inc(x_60);
lean_dec(x_12);
x_61 = lean_box(1);
x_62 = lean_unbox(x_61);
x_63 = lean_io_prim_handle_mk(x_60, x_62, x_54);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_60);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l___private_Lean_Shell_0__Lean_shellMain___closed__2;
lean_inc(x_49);
lean_inc(x_59);
x_67 = lean_ir_emit_c(x_59, x_49);
x_68 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 3, 2);
lean_closure_set(x_68, 0, x_67);
lean_closure_set(x_68, 1, x_64);
x_69 = lean_box(0);
x_70 = l_Lean_profileitIOUnsafe___redArg(x_66, x_6, x_68, x_69, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_19 = x_55;
x_20 = x_59;
x_21 = x_49;
x_22 = x_71;
goto block_43;
}
else
{
uint8_t x_72; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_13);
lean_dec(x_6);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
return x_70;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_70, 0);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_70);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_13);
lean_dec(x_6);
x_76 = lean_ctor_get(x_63, 1);
lean_inc(x_76);
lean_dec(x_63);
x_77 = l___private_Lean_Shell_0__Lean_shellMain___closed__3;
x_78 = lean_string_append(x_77, x_60);
lean_dec(x_60);
x_79 = l___private_Lean_Shell_0__Lean_shellMain___closed__4;
x_80 = lean_string_append(x_78, x_79);
x_81 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_80, x_76);
if (lean_obj_tag(x_81) == 0)
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_81, 0);
lean_dec(x_83);
x_84 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_81, 0, x_84);
return x_81;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
x_86 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
return x_81;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_81, 0);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_dec(x_55);
lean_dec(x_49);
lean_dec(x_13);
lean_dec(x_12);
x_92 = lean_ctor_get(x_53, 0);
lean_inc(x_92);
lean_dec(x_53);
x_93 = lean_run_main(x_92, x_6, x_44, x_54);
lean_dec(x_44);
lean_dec(x_6);
lean_dec(x_92);
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
return x_93;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_93);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_49);
lean_dec(x_44);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_98 = !lean_is_exclusive(x_52);
if (x_98 == 0)
{
return x_52;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_52, 0);
x_100 = lean_ctor_get(x_52, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_52);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_115:
{
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_44 = x_103;
x_45 = x_104;
x_46 = x_105;
x_47 = x_106;
x_48 = x_107;
x_49 = x_109;
x_50 = x_110;
goto block_102;
}
else
{
uint8_t x_111; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
block_124:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_123; 
lean_dec(x_119);
x_123 = l___private_Lean_Shell_0__Lean_shellMain___closed__6;
x_44 = x_117;
x_45 = x_118;
x_46 = x_120;
x_47 = x_121;
x_48 = x_122;
x_49 = x_123;
x_50 = x_116;
goto block_102;
}
else
{
lean_dec(x_116);
x_103 = x_117;
x_104 = x_118;
x_105 = x_120;
x_106 = x_121;
x_107 = x_122;
x_108 = x_119;
goto block_115;
}
}
block_158:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_132; 
x_132 = lean_box(0);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_133; 
lean_dec(x_8);
x_133 = l___private_Lean_Shell_0__Lean_shellMain___closed__6;
x_44 = x_125;
x_45 = x_130;
x_46 = x_127;
x_47 = x_132;
x_48 = x_129;
x_49 = x_133;
x_50 = x_131;
goto block_102;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_128, 0);
lean_inc(x_134);
lean_dec(x_128);
x_135 = l_Lean_moduleNameOfFileName(x_134, x_8, x_131);
if (lean_obj_tag(x_135) == 0)
{
x_103 = x_125;
x_104 = x_130;
x_105 = x_127;
x_106 = x_132;
x_107 = x_129;
x_108 = x_135;
goto block_115;
}
else
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_136; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
x_116 = x_136;
x_117 = x_125;
x_118 = x_130;
x_119 = x_135;
x_120 = x_127;
x_121 = x_132;
x_122 = x_129;
goto block_124;
}
else
{
if (x_126 == 0)
{
x_103 = x_125;
x_104 = x_130;
x_105 = x_127;
x_106 = x_132;
x_107 = x_129;
x_108 = x_135;
goto block_115;
}
else
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
x_116 = x_137;
x_117 = x_125;
x_118 = x_130;
x_119 = x_135;
x_120 = x_127;
x_121 = x_132;
x_122 = x_129;
goto block_124;
}
}
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_128);
lean_dec(x_8);
x_138 = !lean_is_exclusive(x_9);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_ctor_get(x_9, 0);
x_140 = l_Lean_ModuleSetup_load(x_139, x_131);
lean_dec(x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_ctor_get(x_141, 0);
lean_inc(x_143);
lean_ctor_set(x_9, 0, x_141);
x_44 = x_125;
x_45 = x_130;
x_46 = x_127;
x_47 = x_9;
x_48 = x_129;
x_49 = x_143;
x_50 = x_142;
goto block_102;
}
else
{
uint8_t x_144; 
lean_free_object(x_9);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_125);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_144 = !lean_is_exclusive(x_140);
if (x_144 == 0)
{
return x_140;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_140, 0);
x_146 = lean_ctor_get(x_140, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_140);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_9, 0);
lean_inc(x_148);
lean_dec(x_9);
x_149 = l_Lean_ModuleSetup_load(x_148, x_131);
lean_dec(x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_150);
x_44 = x_125;
x_45 = x_130;
x_46 = x_127;
x_47 = x_153;
x_48 = x_129;
x_49 = x_152;
x_50 = x_151;
goto block_102;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_125);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_154 = lean_ctor_get(x_149, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_156 = x_149;
} else {
 lean_dec_ref(x_149);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
block_232:
{
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_decode_lossy_utf8(x_167);
lean_dec(x_167);
if (x_159 == 0)
{
if (x_165 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_string_utf8_byte_size(x_169);
lean_inc(x_171);
lean_inc(x_169);
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_172, 2, x_171);
x_173 = lean_unsigned_to_nat(5u);
x_174 = l_Substring_nextn(x_172, x_173, x_170);
lean_dec(x_172);
lean_inc(x_169);
x_175 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_175, 0, x_169);
lean_ctor_set(x_175, 1, x_170);
lean_ctor_set(x_175, 2, x_174);
x_176 = l___private_Lean_Shell_0__Lean_shellMain___closed__9;
x_177 = l_Substring_beq(x_175, x_176);
if (x_177 == 0)
{
lean_dec(x_171);
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = x_163;
x_129 = x_164;
x_130 = x_169;
x_131 = x_168;
goto block_158;
}
else
{
uint32_t x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_178 = 10;
x_179 = l_String_posOfAux(x_169, x_178, x_171, x_170);
x_180 = lean_unsigned_to_nat(6u);
x_181 = lean_string_utf8_extract(x_169, x_180, x_179);
x_182 = lean_string_utf8_byte_size(x_181);
x_183 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_181, x_182, x_170);
x_184 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_181, x_183, x_182);
x_185 = lean_string_utf8_extract(x_181, x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_181);
x_186 = l___private_Lean_Shell_0__Lean_shellMain___closed__10;
x_187 = lean_string_dec_eq(x_185, x_186);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_179);
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_188 = l___private_Lean_Shell_0__Lean_shellMain___closed__11;
x_189 = lean_string_append(x_188, x_185);
lean_dec(x_185);
x_190 = l___private_Lean_Shell_0__Lean_shellMain___closed__12;
x_191 = lean_string_append(x_189, x_190);
x_192 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_191, x_168);
if (lean_obj_tag(x_192) == 0)
{
uint8_t x_193; 
x_193 = !lean_is_exclusive(x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_192, 0);
lean_dec(x_194);
x_195 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_192, 0, x_195);
return x_192;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
lean_dec(x_192);
x_197 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_192);
if (x_199 == 0)
{
return x_192;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_192, 0);
x_201 = lean_ctor_get(x_192, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_192);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
lean_object* x_203; 
lean_dec(x_185);
x_203 = lean_string_utf8_extract(x_169, x_179, x_171);
lean_dec(x_171);
lean_dec(x_179);
lean_dec(x_169);
x_125 = x_160;
x_126 = x_161;
x_127 = x_162;
x_128 = x_163;
x_129 = x_164;
x_130 = x_203;
x_131 = x_168;
goto block_158;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; 
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_164);
x_205 = l_Lean_Elab_printImportSrcs(x_169, x_204, x_168);
if (lean_obj_tag(x_205) == 0)
{
uint8_t x_206; 
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; 
x_207 = lean_ctor_get(x_205, 0);
lean_dec(x_207);
x_208 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_205, 0, x_208);
return x_205;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
lean_dec(x_205);
x_210 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
else
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_205);
if (x_212 == 0)
{
return x_205;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_205, 0);
x_214 = lean_ctor_get(x_205, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_205);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_164);
x_217 = l_Lean_Elab_printImports(x_169, x_216, x_168);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_217, 0);
lean_dec(x_219);
x_220 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_217, 0, x_220);
return x_217;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_217, 1);
lean_inc(x_221);
lean_dec(x_217);
x_222 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
else
{
uint8_t x_224; 
x_224 = !lean_is_exclusive(x_217);
if (x_224 == 0)
{
return x_217;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_217, 0);
x_226 = lean_ctor_get(x_217, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_217);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_160);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_228 = !lean_is_exclusive(x_166);
if (x_228 == 0)
{
return x_166;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_166, 0);
x_230 = lean_ctor_get(x_166, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_166);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
block_245:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_get_stdin(x_236);
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_IO_FS_Stream_readBinToEnd(x_242, x_243);
x_159 = x_240;
x_160 = x_233;
x_161 = x_234;
x_162 = x_235;
x_163 = x_237;
x_164 = x_239;
x_165 = x_238;
x_166 = x_244;
goto block_232;
}
block_273:
{
if (lean_obj_tag(x_247) == 0)
{
if (x_2 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_246);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_249 = l___private_Lean_Shell_0__Lean_shellMain___closed__13;
x_250 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_249, x_18);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; uint8_t x_253; lean_object* x_254; 
x_251 = lean_ctor_get(x_250, 1);
lean_inc(x_251);
lean_dec(x_250);
x_252 = lean_box(1);
x_253 = lean_unbox(x_252);
x_254 = lean_display_help(x_253, x_251);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_254, 0);
lean_dec(x_256);
x_257 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_254, 0, x_257);
return x_254;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_254, 1);
lean_inc(x_258);
lean_dec(x_254);
x_259 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
else
{
uint8_t x_261; 
x_261 = !lean_is_exclusive(x_254);
if (x_261 == 0)
{
return x_254;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_254, 0);
x_263 = lean_ctor_get(x_254, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_254);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
uint8_t x_265; 
x_265 = !lean_is_exclusive(x_250);
if (x_265 == 0)
{
return x_250;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_250, 0);
x_267 = lean_ctor_get(x_250, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_250);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
else
{
lean_object* x_269; 
x_269 = l___private_Lean_Shell_0__Lean_shellMain___closed__14;
x_233 = x_246;
x_234 = x_248;
x_235 = x_17;
x_236 = x_18;
x_237 = x_247;
x_238 = x_4;
x_239 = x_269;
x_240 = x_3;
goto block_245;
}
}
else
{
if (x_2 == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_247, 0);
lean_inc(x_270);
x_271 = l_IO_FS_readBinFile(x_270, x_18);
x_159 = x_3;
x_160 = x_246;
x_161 = x_248;
x_162 = x_17;
x_163 = x_247;
x_164 = x_270;
x_165 = x_4;
x_166 = x_271;
goto block_232;
}
else
{
lean_object* x_272; 
x_272 = lean_ctor_get(x_247, 0);
lean_inc(x_272);
x_233 = x_246;
x_234 = x_248;
x_235 = x_17;
x_236 = x_18;
x_237 = x_247;
x_238 = x_4;
x_239 = x_272;
x_240 = x_3;
goto block_245;
}
}
}
block_297:
{
uint8_t x_278; 
x_278 = l_List_isEmpty___redArg(x_274);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_276);
lean_dec(x_274);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_279 = l___private_Lean_Shell_0__Lean_shellMain___closed__13;
x_280 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_279, x_18);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_280, 1);
lean_inc(x_281);
lean_dec(x_280);
x_282 = lean_display_help(x_277, x_281);
if (lean_obj_tag(x_282) == 0)
{
uint8_t x_283; 
x_283 = !lean_is_exclusive(x_282);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_282, 0);
lean_dec(x_284);
x_285 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_282, 0, x_285);
return x_282;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_282, 1);
lean_inc(x_286);
lean_dec(x_282);
x_287 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
else
{
uint8_t x_289; 
x_289 = !lean_is_exclusive(x_282);
if (x_289 == 0)
{
return x_282;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_282, 0);
x_291 = lean_ctor_get(x_282, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_282);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
else
{
uint8_t x_293; 
x_293 = !lean_is_exclusive(x_280);
if (x_293 == 0)
{
return x_280;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_280, 0);
x_295 = lean_ctor_get(x_280, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_280);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
x_246 = x_274;
x_247 = x_276;
x_248 = x_275;
goto block_273;
}
}
block_303:
{
if (x_17 == 0)
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_box(1);
x_302 = lean_unbox(x_301);
x_274 = x_300;
x_275 = x_298;
x_276 = x_299;
x_277 = x_302;
goto block_297;
}
else
{
if (x_298 == 0)
{
x_246 = x_300;
x_247 = x_299;
x_248 = x_298;
goto block_273;
}
else
{
x_274 = x_300;
x_275 = x_298;
x_276 = x_299;
x_277 = x_298;
goto block_297;
}
}
}
block_309:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_305; 
x_305 = lean_box(0);
x_298 = x_304;
x_299 = x_305;
x_300 = x_1;
goto block_303;
}
else
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_1, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_1, 1);
lean_inc(x_307);
lean_dec(x_1);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_306);
x_298 = x_304;
x_299 = x_308;
x_300 = x_307;
goto block_303;
}
}
block_323:
{
lean_object* x_312; 
x_312 = l_Lean_printImportsJson(x_310, x_311);
if (lean_obj_tag(x_312) == 0)
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_312, 0);
lean_dec(x_314);
x_315 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_312, 0, x_315);
return x_312;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_312, 1);
lean_inc(x_316);
lean_dec(x_312);
x_317 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_318 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
else
{
uint8_t x_319; 
x_319 = !lean_is_exclusive(x_312);
if (x_319 == 0)
{
return x_312;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_320 = lean_ctor_get(x_312, 0);
x_321 = lean_ctor_get(x_312, 1);
lean_inc(x_321);
lean_inc(x_320);
lean_dec(x_312);
x_322 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_321);
return x_322;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Shell_0__Lean_shellMain___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Shell_0__Lean_shellMain___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint32_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_19 = lean_unbox(x_2);
lean_dec(x_2);
x_20 = lean_unbox(x_3);
lean_dec(x_3);
x_21 = lean_unbox(x_4);
lean_dec(x_4);
x_22 = lean_unbox(x_5);
lean_dec(x_5);
x_23 = lean_unbox_uint32(x_7);
lean_dec(x_7);
x_24 = lean_unbox(x_14);
lean_dec(x_14);
x_25 = lean_unbox(x_16);
lean_dec(x_16);
x_26 = lean_unbox(x_17);
lean_dec(x_17);
x_27 = lean_shell_main(x_1, x_19, x_20, x_21, x_22, x_6, x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_24, x_15, x_25, x_26, x_18);
return x_27;
}
}
lean_object* initialize_Lean_Elab_Frontend(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_ParseImportsFast(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_EmitC(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Shell(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Frontend(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_ParseImportsFast(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_EmitC(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__0 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__0();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__0);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__1 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__1();
l___private_Lean_Shell_0__Lean_shortVersionString___closed__2 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__2();
l___private_Lean_Shell_0__Lean_shortVersionString___closed__3 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__3();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__3);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__4 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__4();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__4);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__5 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__5();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__5);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__6 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__6();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__6);
l___private_Lean_Shell_0__Lean_shortVersionString___closed__7 = _init_l___private_Lean_Shell_0__Lean_shortVersionString___closed__7();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString___closed__7);
l___private_Lean_Shell_0__Lean_shortVersionString = _init_l___private_Lean_Shell_0__Lean_shortVersionString();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shortVersionString);
l___private_Lean_Shell_0__Lean_versionHeader___closed__0 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__0();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__0);
l___private_Lean_Shell_0__Lean_versionHeader___closed__1 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__1);
l___private_Lean_Shell_0__Lean_versionHeader___closed__2 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__2);
l___private_Lean_Shell_0__Lean_versionHeader___closed__3 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__3();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__3);
l___private_Lean_Shell_0__Lean_versionHeader___closed__4 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__4();
l___private_Lean_Shell_0__Lean_versionHeader___closed__5 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__5();
l___private_Lean_Shell_0__Lean_versionHeader___closed__6 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__6();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__6);
l___private_Lean_Shell_0__Lean_versionHeader___closed__7 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__7();
l___private_Lean_Shell_0__Lean_versionHeader___closed__8 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__8();
l___private_Lean_Shell_0__Lean_versionHeader___closed__9 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__9();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__9);
l___private_Lean_Shell_0__Lean_versionHeader___closed__10 = _init_l___private_Lean_Shell_0__Lean_versionHeader___closed__10();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader___closed__10);
l___private_Lean_Shell_0__Lean_versionHeader = _init_l___private_Lean_Shell_0__Lean_versionHeader();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_versionHeader);
l___private_Lean_Shell_0__Lean_displayHelp___closed__0 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__0();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__0);
l___private_Lean_Shell_0__Lean_displayHelp___closed__1 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__1);
l___private_Lean_Shell_0__Lean_displayHelp___closed__2 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__2);
l___private_Lean_Shell_0__Lean_displayHelp___closed__3 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__3();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__3);
l___private_Lean_Shell_0__Lean_displayHelp___closed__4 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__4();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__4);
l___private_Lean_Shell_0__Lean_displayHelp___closed__5 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__5();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__5);
l___private_Lean_Shell_0__Lean_displayHelp___closed__6 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__6();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__6);
l___private_Lean_Shell_0__Lean_displayHelp___closed__7 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__7();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__7);
l___private_Lean_Shell_0__Lean_displayHelp___closed__8 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__8();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__8);
l___private_Lean_Shell_0__Lean_displayHelp___closed__9 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__9();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__9);
l___private_Lean_Shell_0__Lean_displayHelp___closed__10 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__10();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__10);
l___private_Lean_Shell_0__Lean_displayHelp___closed__11 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__11();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__11);
l___private_Lean_Shell_0__Lean_displayHelp___closed__12 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__12();
l___private_Lean_Shell_0__Lean_displayHelp___closed__13 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__13();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__13);
l___private_Lean_Shell_0__Lean_displayHelp___closed__14 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__14();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__14);
l___private_Lean_Shell_0__Lean_displayHelp___closed__15 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__15();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__15);
l___private_Lean_Shell_0__Lean_displayHelp___closed__16 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__16();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__16);
l___private_Lean_Shell_0__Lean_displayHelp___closed__17 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__17();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__17);
l___private_Lean_Shell_0__Lean_displayHelp___closed__18 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__18();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__18);
l___private_Lean_Shell_0__Lean_displayHelp___closed__19 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__19();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__19);
l___private_Lean_Shell_0__Lean_displayHelp___closed__20 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__20();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__20);
l___private_Lean_Shell_0__Lean_displayHelp___closed__21 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__21();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__21);
l___private_Lean_Shell_0__Lean_displayHelp___closed__22 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__22();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__22);
l___private_Lean_Shell_0__Lean_displayHelp___closed__23 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__23();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__23);
l___private_Lean_Shell_0__Lean_displayHelp___closed__24 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__24();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__24);
l___private_Lean_Shell_0__Lean_displayHelp___closed__25 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__25();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__25);
l___private_Lean_Shell_0__Lean_displayHelp___closed__26 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__26();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__26);
l___private_Lean_Shell_0__Lean_displayHelp___closed__27 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__27();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__27);
l___private_Lean_Shell_0__Lean_displayHelp___closed__28 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__28();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__28);
l___private_Lean_Shell_0__Lean_displayHelp___closed__29 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__29();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__29);
l___private_Lean_Shell_0__Lean_displayHelp___closed__30 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__30();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__30);
l___private_Lean_Shell_0__Lean_displayHelp___closed__31 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__31();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__31);
l___private_Lean_Shell_0__Lean_displayHelp___closed__32 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__32();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__32);
l___private_Lean_Shell_0__Lean_displayHelp___closed__33 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__33();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__33);
l___private_Lean_Shell_0__Lean_displayHelp___closed__34 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__34();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__34);
l___private_Lean_Shell_0__Lean_displayHelp___closed__35 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__35();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__35);
l___private_Lean_Shell_0__Lean_displayHelp___closed__36 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__36();
l___private_Lean_Shell_0__Lean_displayHelp___closed__37 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__37();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__37);
l___private_Lean_Shell_0__Lean_displayHelp___closed__38 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__38();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__38);
l___private_Lean_Shell_0__Lean_displayHelp___closed__39 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__39();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__39);
l___private_Lean_Shell_0__Lean_displayHelp___closed__40 = _init_l___private_Lean_Shell_0__Lean_displayHelp___closed__40();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_displayHelp___closed__40);
l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0 = _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___closed__0();
l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1 = _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__1);
l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2 = _init_l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed__const__2);
l___private_Lean_Shell_0__Lean_shellMain___closed__0 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__0();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__0);
l___private_Lean_Shell_0__Lean_shellMain___closed__1 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__1);
l___private_Lean_Shell_0__Lean_shellMain___closed__2 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__2);
l___private_Lean_Shell_0__Lean_shellMain___closed__3 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__3();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__3);
l___private_Lean_Shell_0__Lean_shellMain___closed__4 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__4();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__4);
l___private_Lean_Shell_0__Lean_shellMain___closed__5 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__5();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__5);
l___private_Lean_Shell_0__Lean_shellMain___closed__6 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__6();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__6);
l___private_Lean_Shell_0__Lean_shellMain___closed__7 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__7();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__7);
l___private_Lean_Shell_0__Lean_shellMain___closed__8 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__8();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__8);
l___private_Lean_Shell_0__Lean_shellMain___closed__9 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__9();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__9);
l___private_Lean_Shell_0__Lean_shellMain___closed__10 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__10();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__10);
l___private_Lean_Shell_0__Lean_shellMain___closed__11 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__11();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__11);
l___private_Lean_Shell_0__Lean_shellMain___closed__12 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__12();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__12);
l___private_Lean_Shell_0__Lean_shellMain___closed__13 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__13();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__13);
l___private_Lean_Shell_0__Lean_shellMain___closed__14 = _init_l___private_Lean_Shell_0__Lean_shellMain___closed__14();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___closed__14);
l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1 = _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1);
l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2 = _init_l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2();
lean_mark_persistent(l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
