// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: public import Lake.Load.Config public import Lake.Build.Context public import Lake.Util.Exit import Lake.Build.Run import Lake.Build.Module import Lake.Load.Package import Lake.Load.Lean.Elab import Lake.Load.Workspace import Lake.Util.IO
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
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1;
static lean_object* l_Lake_setupFile___closed__5;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Run_0__Lake_mkMonitorContext(lean_object*, lean_object*);
uint8_t l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t);
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
static lean_object* l_Lake_setupFile___closed__4;
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(lean_object*);
lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*);
lean_object* l_instMonadST(lean_object*);
lean_object* lean_io_getenv(lean_object*);
static lean_object* l_Lake_serve___closed__3;
lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
static lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0;
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_get_stdout();
lean_object* lean_io_process_child_wait(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
static lean_object* l_Lake_setupFile___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*);
static lean_object* l_Lake_serve___closed__1;
lean_object* l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_loadWorkspace___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_stderr();
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0;
LEAN_EXPORT uint32_t l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lake_serve___closed__0;
static lean_object* l_Lake_setupFile___closed__0;
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___boxed(lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_serve_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__2;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_invalidConfigEnvVar___closed__0;
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_setupFile___closed__6;
extern lean_object* l_Lake_configModuleName;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_serve_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lake_setupServerModule___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lake_realConfigFile(lean_object*);
static uint32_t _init_l_Lake_noConfigFileCode() {
_start:
{
uint32_t x_1; 
x_1 = 2;
return x_1;
}
}
static lean_object* _init_l_Lake_invalidConfigEnvVar___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LAKE_INVALID_CONFIG", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_invalidConfigEnvVar() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_invalidConfigEnvVar___closed__0;
return x_1;
}
}
static lean_object* _init_l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0;
x_4 = lean_box(0);
x_5 = l_instInhabitedOfMonad___redArg(x_3, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_1(x_6, lean_box(0));
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stdout();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___00IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.CLI.Serve", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.setupFile.print!", 21, 21);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to print `setup-file` result: ", 37, 37);
return x_1;
}
}
LEAN_EXPORT uint32_t l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(lean_object* x_1) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(x_1);
if (lean_obj_tag(x_3) == 0)
{
uint32_t x_4; 
lean_dec_ref(x_3);
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0;
x_7 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1;
x_8 = lean_unsigned_to_nat(80u);
x_9 = lean_unsigned_to_nat(6u);
x_10 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2;
x_11 = lean_io_error_to_string(x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = l_mkPanicMessageWithDecl(x_6, x_7, x_8, x_9, x_12);
lean_dec_ref(x_12);
x_14 = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(x_13);
x_15 = 1;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_get_stderr();
x_4 = lean_ctor_get(x_3, 4);
lean_inc_ref(x_4);
lean_dec_ref(x_3);
x_5 = lean_apply_2(x_4, x_1, lean_box(0));
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake.setupFile.eprint!", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to print `setup-file` error: ", 36, 36);
return x_1;
}
}
static lean_object* _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nOriginal error:\n", 17, 17);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(lean_object* x_1) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec_ref(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0;
x_7 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0;
x_8 = lean_unsigned_to_nat(84u);
x_9 = lean_unsigned_to_nat(6u);
x_10 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1;
x_11 = lean_io_error_to_string(x_5);
x_12 = lean_string_append(x_10, x_11);
lean_dec_ref(x_11);
x_13 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_string_append(x_14, x_1);
lean_dec_ref(x_1);
x_16 = l_mkPanicMessageWithDecl(x_6, x_7, x_8, x_9, x_15);
lean_dec_ref(x_15);
x_17 = l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_setupFile___lam__0(x_1, x_6, x_7, x_4);
lean_dec_ref(x_4);
return x_8;
}
}
static lean_object* _init_l_Lake_setupFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.\n", 96, 96);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("job computation", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to build module dependencies.\n", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to load the Lake workspace.\n", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT uint32_t l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_inc_ref(x_2);
x_6 = l_Lake_resolvePath(x_2);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 8);
lean_inc_ref(x_8);
x_9 = l_Lake_realConfigFile(x_8);
x_10 = lean_string_utf8_byte_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_string_dec_eq(x_9, x_6);
lean_dec_ref(x_9);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lake_invalidConfigEnvVar___closed__0;
x_15 = lean_io_getenv(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint32_t x_20; 
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_16);
x_18 = l_Lake_setupFile___closed__0;
x_19 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_18);
x_20 = 1;
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_15);
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 1);
x_23 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 2);
x_24 = lean_ctor_get(x_21, 0);
x_25 = l_Lake_OutStream_get(x_24);
lean_inc_ref(x_25);
x_26 = l_Lake_AnsiMode_isEnabled(x_25, x_23);
x_27 = lean_box(x_22);
x_28 = lean_box(x_26);
x_29 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_29, 0, x_25);
lean_closure_set(x_29, 1, x_27);
lean_closure_set(x_29, 2, x_28);
x_30 = l_Lake_loadWorkspace(x_1, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lake_setupFile___closed__1;
x_33 = lean_st_mk_ref(x_32);
lean_inc(x_33);
x_34 = l___private_Lake_Build_Run_0__Lake_mkMonitorContext(x_4, x_33);
x_35 = lean_alloc_closure((void*)(l_Lake_setupServerModule___boxed), 10, 3);
lean_closure_set(x_35, 0, x_2);
lean_closure_set(x_35, 1, x_6);
lean_closure_set(x_35, 2, x_3);
lean_inc_ref(x_4);
lean_inc(x_31);
x_36 = l___private_Lake_Build_Run_0__Lake_mkBuildContext_x27(x_31, x_4, x_33);
x_37 = l_Lake_setupFile___closed__2;
lean_inc_ref(x_34);
x_38 = l___private_Lake_Build_Run_0__Lake_monitorBuild(lean_box(0), x_34, x_36, x_35, x_37);
x_39 = l___private_Lake_Build_Run_0__Lake_Workspace_finalizeBuild(lean_box(0), x_31, x_4, x_34, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_instToJsonModuleSetup_toJson(x_40);
x_42 = l_Lean_Json_compress(x_41);
x_43 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; uint32_t x_46; 
lean_dec_ref(x_39);
x_44 = l_Lake_setupFile___closed__3;
x_45 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_44);
x_46 = 1;
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint32_t x_49; 
lean_dec_ref(x_30);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_47 = l_Lake_setupFile___closed__4;
x_48 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_47);
x_49 = 1;
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint32_t x_62; 
lean_inc_ref(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_50 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_50);
lean_dec_ref(x_7);
x_51 = lean_ctor_get(x_50, 4);
lean_inc_ref(x_51);
lean_dec_ref(x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_52);
lean_dec_ref(x_51);
x_53 = l_Lake_configModuleName;
x_54 = lean_box(0);
x_55 = lean_box(1);
x_56 = l_Lake_setupFile___closed__5;
x_57 = l_Lake_setupFile___closed__6;
x_58 = lean_array_push(x_57, x_52);
x_59 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_54);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_55);
lean_ctor_set(x_59, 4, x_56);
lean_ctor_set(x_59, 5, x_58);
lean_ctor_set(x_59, 6, x_55);
lean_ctor_set_uint8(x_59, sizeof(void*)*7, x_12);
x_60 = l_Lean_instToJsonModuleSetup_toJson(x_59);
x_61 = l_Lean_Json_compress(x_60);
x_62 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(x_61);
return x_62;
}
}
else
{
uint32_t x_63; 
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_63 = 2;
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = l_Lake_setupFile(x_1, x_2, x_3, x_4);
x_7 = lean_box_uint32(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_10 = lean_array_uget(x_4, x_5);
x_11 = l_Lake_OutStream_logEntry(x_1, x_10, x_2, x_3);
lean_dec(x_10);
x_12 = 1;
x_13 = lean_usize_add(x_5, x_12);
x_5 = x_13;
x_7 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_7);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(x_1, x_9, x_10, x_4, x_11, x_12, x_7);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_serve_spec__0(lean_object* x_1) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___00Lake_serve_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_eprintln___at___00Lake_serve_spec__0(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_serve___closed__0() {
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
static lean_object* _init_l_Lake_serve___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--server", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_serve___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_serve___closed__1;
x_2 = l_Lake_setupFile___closed__6;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_serve___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warning: package configuration has errors, falling back to plain `lean --server`", 80, 80);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_serve(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_50; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
lean_inc_ref(x_1);
x_25 = lean_alloc_closure((void*)(l_Lake_loadWorkspace___boxed), 3, 1);
lean_closure_set(x_25, 0, x_1);
x_26 = l_Lake_LoggerIO_captureLog___redArg(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_array_get_size(x_28);
x_57 = lean_nat_dec_lt(x_55, x_56);
if (x_57 == 0)
{
x_30 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = 1;
x_59 = 0;
x_60 = lean_box(1);
x_61 = lean_box(0);
x_62 = lean_nat_dec_le(x_56, x_56);
if (x_62 == 0)
{
if (x_57 == 0)
{
x_30 = lean_box(0);
goto block_49;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_56);
x_65 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(x_60, x_58, x_59, x_28, x_63, x_64, x_61);
x_50 = x_65;
goto block_54;
}
}
else
{
size_t x_66; size_t x_67; lean_object* x_68; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_56);
x_68 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_serve_spec__1(x_60, x_58, x_59, x_28, x_66, x_67, x_61);
x_50 = x_68;
goto block_54;
}
}
block_24:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_7 = l_Lake_serve___closed__0;
x_8 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = lean_ctor_get(x_9, 7);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = l_Lake_serve___closed__2;
x_12 = l_Array_append___redArg(x_11, x_5);
lean_dec_ref(x_5);
x_13 = l_Array_append___redArg(x_12, x_2);
x_14 = lean_box(0);
x_15 = 1;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_4);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_16);
x_18 = lean_io_process_spawn(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_io_process_child_wait(x_7, x_19);
lean_dec(x_19);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
block_49:
{
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_28);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec_ref(x_27);
x_32 = lean_ctor_get(x_31, 0);
x_33 = lean_ctor_get(x_32, 6);
x_34 = lean_ctor_get(x_33, 4);
lean_inc_ref(x_34);
x_35 = l_Lake_Workspace_augmentedEnvVars(x_31);
x_4 = x_35;
x_5 = x_34;
x_6 = lean_box(0);
goto block_24;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_27);
x_36 = l_Lake_serve___closed__3;
x_37 = l_IO_eprintln___at___00Lake_serve_spec__0(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_37);
x_38 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_38);
x_39 = l_Lake_Env_baseVars(x_38);
x_40 = l_Lake_invalidConfigEnvVar___closed__0;
x_41 = l_Lake_Log_toString(x_28);
lean_dec(x_28);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_29)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_29;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_push(x_39, x_43);
x_45 = l_Lake_setupFile___closed__5;
x_4 = x_44;
x_5 = x_45;
x_6 = lean_box(0);
goto block_24;
}
else
{
uint8_t x_46; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
}
block_54:
{
if (lean_obj_tag(x_50) == 0)
{
lean_dec_ref(x_50);
x_30 = lean_box(0);
goto block_49;
}
else
{
uint8_t x_51; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_serve(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin);
lean_object* initialize_Lake_Build_Context(uint8_t builtin);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin);
lean_object* initialize_Lake_Build_Run(uint8_t builtin);
lean_object* initialize_Lake_Build_Module(uint8_t builtin);
lean_object* initialize_Lake_Load_Package(uint8_t builtin);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin);
lean_object* initialize_Lake_Load_Workspace(uint8_t builtin);
lean_object* initialize_Lake_Util_IO(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Serve(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Run(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Elab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Workspace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_noConfigFileCode = _init_l_Lake_noConfigFileCode();
l_Lake_invalidConfigEnvVar___closed__0 = _init_l_Lake_invalidConfigEnvVar___closed__0();
lean_mark_persistent(l_Lake_invalidConfigEnvVar___closed__0);
l_Lake_invalidConfigEnvVar = _init_l_Lake_invalidConfigEnvVar();
lean_mark_persistent(l_Lake_invalidConfigEnvVar);
l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0 = _init_l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0();
lean_mark_persistent(l_panic___at___00__private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__1___closed__0);
l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0);
l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1);
l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2);
l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0);
l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1);
l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2);
l_Lake_setupFile___closed__0 = _init_l_Lake_setupFile___closed__0();
lean_mark_persistent(l_Lake_setupFile___closed__0);
l_Lake_setupFile___closed__1 = _init_l_Lake_setupFile___closed__1();
lean_mark_persistent(l_Lake_setupFile___closed__1);
l_Lake_setupFile___closed__2 = _init_l_Lake_setupFile___closed__2();
lean_mark_persistent(l_Lake_setupFile___closed__2);
l_Lake_setupFile___closed__3 = _init_l_Lake_setupFile___closed__3();
lean_mark_persistent(l_Lake_setupFile___closed__3);
l_Lake_setupFile___closed__4 = _init_l_Lake_setupFile___closed__4();
lean_mark_persistent(l_Lake_setupFile___closed__4);
l_Lake_setupFile___closed__5 = _init_l_Lake_setupFile___closed__5();
lean_mark_persistent(l_Lake_setupFile___closed__5);
l_Lake_setupFile___closed__6 = _init_l_Lake_setupFile___closed__6();
lean_mark_persistent(l_Lake_setupFile___closed__6);
l_Lake_serve___closed__0 = _init_l_Lake_serve___closed__0();
lean_mark_persistent(l_Lake_serve___closed__0);
l_Lake_serve___closed__1 = _init_l_Lake_serve___closed__1();
lean_mark_persistent(l_Lake_serve___closed__1);
l_Lake_serve___closed__2 = _init_l_Lake_serve___closed__2();
lean_mark_persistent(l_Lake_serve___closed__2);
l_Lake_serve___closed__3 = _init_l_Lake_serve___closed__3();
lean_mark_persistent(l_Lake_serve___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
