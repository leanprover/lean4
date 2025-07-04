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
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_263; uint8_t x_264; lean_object* x_265; uint8_t x_266; uint8_t x_287; lean_object* x_288; lean_object* x_289; uint8_t x_293; lean_object* x_299; lean_object* x_300; 
if (x_3 == 0)
{
x_293 = x_3;
goto block_298;
}
else
{
if (x_5 == 0)
{
x_293 = x_5;
goto block_298;
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
lean_object* x_313; 
x_313 = lean_array_mk(x_1);
x_299 = x_313;
x_300 = x_18;
goto block_312;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_1);
x_314 = lean_get_stdin(x_18);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = l_IO_FS_Stream_lines(x_315, x_316);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_299 = x_318;
x_300 = x_319;
goto block_312;
}
else
{
uint8_t x_320; 
x_320 = !lean_is_exclusive(x_317);
if (x_320 == 0)
{
return x_317;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_317, 0);
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_317);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
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
lean_dec(x_19);
lean_dec(x_6);
x_23 = lean_box(0);
x_24 = lean_apply_2(x_20, x_23, x_22);
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
lean_closure_set(x_29, 0, x_21);
lean_closure_set(x_29, 1, x_19);
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
x_34 = lean_apply_2(x_20, x_32, x_33);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_20);
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
block_101:
{
lean_object* x_50; lean_object* x_51; 
x_50 = l___private_Lean_Shell_0__Lean_shellMain___closed__1;
lean_inc(x_48);
lean_inc(x_6);
x_51 = l_Lean_Elab_runFrontend(x_44, x_6, x_45, x_48, x_7, x_10, x_11, x_14, x_15, x_50, x_16, x_46, x_49);
lean_dec(x_15);
lean_dec(x_11);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_52);
x_54 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__0___boxed), 3, 1);
lean_closure_set(x_54, 0, x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_55 = lean_box(0);
x_56 = l___private_Lean_Shell_0__Lean_shellMain___lam__0(x_52, x_55, x_53);
return x_56;
}
else
{
if (x_17 == 0)
{
lean_dec(x_47);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
lean_dec(x_52);
x_19 = x_48;
x_20 = x_54;
x_21 = x_57;
x_22 = x_53;
goto block_43;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_52, 0);
lean_inc(x_58);
lean_dec(x_52);
x_59 = lean_ctor_get(x_12, 0);
lean_inc(x_59);
lean_dec(x_12);
x_60 = lean_box(1);
x_61 = lean_unbox(x_60);
x_62 = lean_io_prim_handle_mk(x_59, x_61, x_53);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l___private_Lean_Shell_0__Lean_shellMain___closed__2;
lean_inc(x_48);
lean_inc(x_58);
x_66 = lean_ir_emit_c(x_58, x_48);
x_67 = lean_alloc_closure((void*)(l___private_Lean_Shell_0__Lean_shellMain___lam__1___boxed), 3, 2);
lean_closure_set(x_67, 0, x_66);
lean_closure_set(x_67, 1, x_63);
x_68 = lean_box(0);
x_69 = l_Lean_profileitIOUnsafe___redArg(x_65, x_6, x_67, x_68, x_64);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_19 = x_48;
x_20 = x_54;
x_21 = x_58;
x_22 = x_70;
goto block_43;
}
else
{
uint8_t x_71; 
lean_dec(x_58);
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_6);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
return x_69;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_69, 0);
x_73 = lean_ctor_get(x_69, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_69);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_58);
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_6);
x_75 = lean_ctor_get(x_62, 1);
lean_inc(x_75);
lean_dec(x_62);
x_76 = l___private_Lean_Shell_0__Lean_shellMain___closed__3;
x_77 = lean_string_append(x_76, x_59);
lean_dec(x_59);
x_78 = l___private_Lean_Shell_0__Lean_shellMain___closed__4;
x_79 = lean_string_append(x_77, x_78);
x_80 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_79, x_75);
if (lean_obj_tag(x_80) == 0)
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_80, 0);
lean_dec(x_82);
x_83 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_80, 0, x_83);
return x_80;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_80, 1);
lean_inc(x_84);
lean_dec(x_80);
x_85 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_80);
if (x_87 == 0)
{
return x_80;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_80, 0);
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_80);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_13);
lean_dec(x_12);
x_91 = lean_ctor_get(x_52, 0);
lean_inc(x_91);
lean_dec(x_52);
x_92 = lean_run_main(x_91, x_6, x_47, x_53);
lean_dec(x_47);
lean_dec(x_6);
lean_dec(x_91);
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
return x_92;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_92);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_6);
x_97 = !lean_is_exclusive(x_51);
if (x_97 == 0)
{
return x_51;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_51, 0);
x_99 = lean_ctor_get(x_51, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_51);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
block_113:
{
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_44 = x_102;
x_45 = x_103;
x_46 = x_104;
x_47 = x_105;
x_48 = x_107;
x_49 = x_108;
goto block_101;
}
else
{
uint8_t x_109; 
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
return x_106;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
block_121:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_120; 
lean_dec(x_116);
x_120 = l___private_Lean_Shell_0__Lean_shellMain___closed__6;
x_44 = x_114;
x_45 = x_117;
x_46 = x_118;
x_47 = x_119;
x_48 = x_120;
x_49 = x_115;
goto block_101;
}
else
{
lean_dec(x_115);
x_102 = x_114;
x_103 = x_117;
x_104 = x_118;
x_105 = x_119;
x_106 = x_116;
goto block_113;
}
}
block_154:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_128; 
x_128 = lean_box(0);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_129; 
lean_dec(x_8);
x_129 = l___private_Lean_Shell_0__Lean_shellMain___closed__6;
x_44 = x_126;
x_45 = x_123;
x_46 = x_128;
x_47 = x_125;
x_48 = x_129;
x_49 = x_127;
goto block_101;
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_124, 0);
lean_inc(x_130);
lean_dec(x_124);
x_131 = l_Lean_moduleNameOfFileName(x_130, x_8, x_127);
if (lean_obj_tag(x_131) == 0)
{
x_102 = x_126;
x_103 = x_123;
x_104 = x_128;
x_105 = x_125;
x_106 = x_131;
goto block_113;
}
else
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_132; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
x_114 = x_126;
x_115 = x_132;
x_116 = x_131;
x_117 = x_123;
x_118 = x_128;
x_119 = x_125;
goto block_121;
}
else
{
if (x_122 == 0)
{
x_102 = x_126;
x_103 = x_123;
x_104 = x_128;
x_105 = x_125;
x_106 = x_131;
goto block_113;
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
x_114 = x_126;
x_115 = x_133;
x_116 = x_131;
x_117 = x_123;
x_118 = x_128;
x_119 = x_125;
goto block_121;
}
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_124);
lean_dec(x_8);
x_134 = !lean_is_exclusive(x_9);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_9, 0);
x_136 = l_Lean_ModuleSetup_load(x_135, x_127);
lean_dec(x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = lean_ctor_get(x_137, 0);
lean_inc(x_139);
lean_ctor_set(x_9, 0, x_137);
x_44 = x_126;
x_45 = x_123;
x_46 = x_9;
x_47 = x_125;
x_48 = x_139;
x_49 = x_138;
goto block_101;
}
else
{
uint8_t x_140; 
lean_free_object(x_9);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_140 = !lean_is_exclusive(x_136);
if (x_140 == 0)
{
return x_136;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_136, 0);
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_136);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_9, 0);
lean_inc(x_144);
lean_dec(x_9);
x_145 = l_Lean_ModuleSetup_load(x_144, x_127);
lean_dec(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_146);
x_44 = x_126;
x_45 = x_123;
x_46 = x_149;
x_47 = x_125;
x_48 = x_148;
x_49 = x_147;
goto block_101;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_123);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_6);
x_150 = lean_ctor_get(x_145, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_152 = x_145;
} else {
 lean_dec_ref(x_145);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
}
}
block_225:
{
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_decode_lossy_utf8(x_160);
lean_dec(x_160);
if (x_3 == 0)
{
if (x_4 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_163 = lean_unsigned_to_nat(0u);
x_164 = lean_string_utf8_byte_size(x_162);
lean_inc(x_164);
lean_inc(x_162);
x_165 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
lean_ctor_set(x_165, 2, x_164);
x_166 = lean_unsigned_to_nat(5u);
x_167 = l_Substring_nextn(x_165, x_166, x_163);
lean_dec(x_165);
lean_inc(x_162);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_163);
lean_ctor_set(x_168, 2, x_167);
x_169 = l___private_Lean_Shell_0__Lean_shellMain___closed__9;
x_170 = l_Substring_beq(x_168, x_169);
if (x_170 == 0)
{
lean_dec(x_164);
x_122 = x_155;
x_123 = x_157;
x_124 = x_156;
x_125 = x_158;
x_126 = x_162;
x_127 = x_161;
goto block_154;
}
else
{
uint32_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_171 = 10;
x_172 = l_String_posOfAux(x_162, x_171, x_164, x_163);
x_173 = lean_unsigned_to_nat(6u);
x_174 = lean_string_utf8_extract(x_162, x_173, x_172);
x_175 = lean_string_utf8_byte_size(x_174);
x_176 = l_Substring_takeWhileAux___at___Lean_Syntax_decodeStringGap_spec__0(x_174, x_175, x_163);
x_177 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_174, x_176, x_175);
x_178 = lean_string_utf8_extract(x_174, x_176, x_177);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_174);
x_179 = l___private_Lean_Shell_0__Lean_shellMain___closed__10;
x_180 = lean_string_dec_eq(x_178, x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_172);
lean_dec(x_164);
lean_dec(x_162);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_181 = l___private_Lean_Shell_0__Lean_shellMain___closed__11;
x_182 = lean_string_append(x_181, x_178);
lean_dec(x_178);
x_183 = l___private_Lean_Shell_0__Lean_shellMain___closed__12;
x_184 = lean_string_append(x_182, x_183);
x_185 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_184, x_161);
if (lean_obj_tag(x_185) == 0)
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_185, 0);
lean_dec(x_187);
x_188 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_185, 0, x_188);
return x_185;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_185, 1);
lean_inc(x_189);
lean_dec(x_185);
x_190 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_185);
if (x_192 == 0)
{
return x_185;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_185, 0);
x_194 = lean_ctor_get(x_185, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_185);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; 
lean_dec(x_178);
x_196 = lean_string_utf8_extract(x_162, x_172, x_164);
lean_dec(x_164);
lean_dec(x_172);
lean_dec(x_162);
x_122 = x_155;
x_123 = x_157;
x_124 = x_156;
x_125 = x_158;
x_126 = x_196;
x_127 = x_161;
goto block_154;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_157);
x_198 = l_Lean_Elab_printImportSrcs(x_162, x_197, x_161);
if (lean_obj_tag(x_198) == 0)
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_198, 0);
lean_dec(x_200);
x_201 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_198, 0, x_201);
return x_198;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_198, 1);
lean_inc(x_202);
lean_dec(x_198);
x_203 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
uint8_t x_205; 
x_205 = !lean_is_exclusive(x_198);
if (x_205 == 0)
{
return x_198;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_198, 0);
x_207 = lean_ctor_get(x_198, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_198);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_157);
x_210 = l_Lean_Elab_printImports(x_162, x_209, x_161);
if (lean_obj_tag(x_210) == 0)
{
uint8_t x_211; 
x_211 = !lean_is_exclusive(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_210, 0);
lean_dec(x_212);
x_213 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_210, 0, x_213);
return x_210;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_210, 1);
lean_inc(x_214);
lean_dec(x_210);
x_215 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_210);
if (x_217 == 0)
{
return x_210;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_210, 0);
x_219 = lean_ctor_get(x_210, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_210);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_221 = !lean_is_exclusive(x_159);
if (x_221 == 0)
{
return x_159;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_159, 0);
x_223 = lean_ctor_get(x_159, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_159);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
block_236:
{
if (x_2 == 0)
{
lean_object* x_231; 
x_231 = l_IO_FS_readBinFile(x_229, x_230);
x_155 = x_226;
x_156 = x_227;
x_157 = x_229;
x_158 = x_228;
x_159 = x_231;
goto block_225;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_get_stdin(x_230);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = l_IO_FS_Stream_readBinToEnd(x_233, x_234);
x_155 = x_226;
x_156 = x_227;
x_157 = x_229;
x_158 = x_228;
x_159 = x_235;
goto block_225;
}
}
block_262:
{
if (lean_obj_tag(x_237) == 0)
{
if (x_2 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_238);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_240 = l___private_Lean_Shell_0__Lean_shellMain___closed__13;
x_241 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_240, x_18);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_243 = lean_box(1);
x_244 = lean_unbox(x_243);
x_245 = lean_display_help(x_244, x_242);
if (lean_obj_tag(x_245) == 0)
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_245, 0);
lean_dec(x_247);
x_248 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_245, 0, x_248);
return x_245;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_249 = lean_ctor_get(x_245, 1);
lean_inc(x_249);
lean_dec(x_245);
x_250 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_251 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
else
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_245);
if (x_252 == 0)
{
return x_245;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_253 = lean_ctor_get(x_245, 0);
x_254 = lean_ctor_get(x_245, 1);
lean_inc(x_254);
lean_inc(x_253);
lean_dec(x_245);
x_255 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
return x_255;
}
}
}
else
{
uint8_t x_256; 
x_256 = !lean_is_exclusive(x_241);
if (x_256 == 0)
{
return x_241;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_241, 0);
x_258 = lean_ctor_get(x_241, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_241);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
else
{
lean_object* x_260; 
x_260 = l___private_Lean_Shell_0__Lean_shellMain___closed__14;
x_226 = x_239;
x_227 = x_237;
x_228 = x_238;
x_229 = x_260;
x_230 = x_18;
goto block_236;
}
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_237, 0);
lean_inc(x_261);
x_226 = x_239;
x_227 = x_237;
x_228 = x_238;
x_229 = x_261;
x_230 = x_18;
goto block_236;
}
}
block_286:
{
uint8_t x_267; 
x_267 = l_List_isEmpty___redArg(x_265);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_268 = l___private_Lean_Shell_0__Lean_shellMain___closed__13;
x_269 = l_IO_eprintln___at_____private_Init_System_IO_0__IO_eprintlnAux_spec__0(x_268, x_18);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = lean_display_help(x_266, x_270);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_271, 0);
lean_dec(x_273);
x_274 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
lean_ctor_set(x_271, 0, x_274);
return x_271;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_271, 1);
lean_inc(x_275);
lean_dec(x_271);
x_276 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__1;
x_277 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_277, 0, x_276);
lean_ctor_set(x_277, 1, x_275);
return x_277;
}
}
else
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_271);
if (x_278 == 0)
{
return x_271;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_271, 0);
x_280 = lean_ctor_get(x_271, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_271);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
else
{
uint8_t x_282; 
x_282 = !lean_is_exclusive(x_269);
if (x_282 == 0)
{
return x_269;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_269, 0);
x_284 = lean_ctor_get(x_269, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_269);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
return x_285;
}
}
}
else
{
x_237 = x_263;
x_238 = x_265;
x_239 = x_264;
goto block_262;
}
}
block_292:
{
if (x_17 == 0)
{
lean_object* x_290; uint8_t x_291; 
x_290 = lean_box(1);
x_291 = lean_unbox(x_290);
x_263 = x_288;
x_264 = x_287;
x_265 = x_289;
x_266 = x_291;
goto block_286;
}
else
{
if (x_287 == 0)
{
x_237 = x_288;
x_238 = x_289;
x_239 = x_287;
goto block_262;
}
else
{
x_263 = x_288;
x_264 = x_287;
x_265 = x_289;
x_266 = x_287;
goto block_286;
}
}
}
block_298:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_294; 
x_294 = lean_box(0);
x_287 = x_293;
x_288 = x_294;
x_289 = x_1;
goto block_292;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_1, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_1, 1);
lean_inc(x_296);
lean_dec(x_1);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_295);
x_287 = x_293;
x_288 = x_297;
x_289 = x_296;
goto block_292;
}
}
block_312:
{
lean_object* x_301; 
x_301 = l_Lean_printImportsJson(x_299, x_300);
if (lean_obj_tag(x_301) == 0)
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_301);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_301, 0);
lean_dec(x_303);
x_304 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
lean_ctor_set(x_301, 0, x_304);
return x_301;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_301, 1);
lean_inc(x_305);
lean_dec(x_301);
x_306 = l___private_Lean_Shell_0__Lean_shellMain___boxed__const__2;
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
else
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_301);
if (x_308 == 0)
{
return x_301;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_301, 0);
x_310 = lean_ctor_get(x_301, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_301);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
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
