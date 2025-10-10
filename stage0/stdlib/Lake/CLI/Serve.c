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
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
static lean_object* l_Lake_setupFile___closed__4;
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(lean_object*, lean_object*);
lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*, lean_object*);
lean_object* l_instMonadST(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__3;
lean_object* l_Lake_Env_baseVars(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
lean_object* lean_get_stdout(lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
static lean_object* l_Lake_setupFile___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__1;
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
lean_object* lean_get_stderr(lean_object*);
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0;
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__2;
LEAN_EXPORT lean_object* l_IO_eprint___at_____private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__0;
static lean_object* l_Lake_setupFile___closed__0;
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2(lean_object*, lean_object*);
static lean_object* l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2___closed__0;
static lean_object* l_Lake_setupFile___closed__2;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
LEAN_EXPORT lean_object* l_IO_eprintln___at___Lake_serve_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__2;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_invalidConfigEnvVar___closed__0;
static lean_object* l_Lake_setupFile___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_instToJsonModuleSetup_toJson(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_configModuleName;
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lake_setupServerModule(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stdout(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_IO_println___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___IO_println___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0_spec__0(x_4, x_2);
return x_5;
}
}
static lean_object* _init_l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadST(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2___closed__0;
x_4 = lean_box(0);
x_5 = l_instInhabitedOfMonad___redArg(x_3, x_4);
x_6 = lean_panic_fn(x_5, x_1);
x_7 = lean_apply_1(x_6, x_2);
return x_7;
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
static lean_object* _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_println___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_dec(x_5);
x_6 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__1;
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__1;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_dec_ref(x_3);
x_12 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0;
x_13 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1;
x_14 = lean_unsigned_to_nat(80u);
x_15 = lean_unsigned_to_nat(6u);
x_16 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2;
x_17 = lean_io_error_to_string(x_10);
x_18 = lean_string_append(x_16, x_17);
lean_dec_ref(x_17);
x_19 = l_mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_18);
lean_dec_ref(x_18);
x_20 = l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2(x_19, x_11);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__2;
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__2;
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at_____private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_get_stderr(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_4, 4);
lean_inc_ref(x_6);
lean_dec(x_4);
x_7 = lean_apply_2(x_6, x_1, x_5);
return x_7;
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
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc_ref(x_1);
x_3 = l_IO_eprint___at_____private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec_ref(x_3);
x_10 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0;
x_11 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__0;
x_12 = lean_unsigned_to_nat(84u);
x_13 = lean_unsigned_to_nat(6u);
x_14 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__1;
x_15 = lean_io_error_to_string(x_8);
x_16 = lean_string_append(x_14, x_15);
lean_dec_ref(x_15);
x_17 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21___closed__2;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_1);
lean_dec_ref(x_1);
x_20 = l_mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_19);
lean_dec_ref(x_19);
x_21 = l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2(x_20, x_9);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_setupFile___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to build module dependencies.\n", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to load the Lake workspace.\n", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.\n", 96, 96);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_configModuleName;
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 2;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_2);
x_16 = l_Lake_resolvePath(x_2, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec_ref(x_16);
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 7);
lean_inc_ref(x_20);
x_21 = l_Lake_realConfigFile(x_20, x_18);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_string_utf8_byte_size(x_23);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
uint8_t x_28; 
lean_free_object(x_21);
x_28 = lean_string_dec_eq(x_23, x_17);
lean_dec(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lake_invalidConfigEnvVar___closed__0;
x_30 = lean_io_getenv(x_29, x_24);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = lean_ctor_get_uint8(x_32, sizeof(void*)*1 + 1);
x_35 = lean_ctor_get_uint8(x_32, sizeof(void*)*1 + 2);
x_36 = lean_ctor_get(x_32, 0);
x_37 = l_Lake_OutStream_get(x_36, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
lean_inc(x_38);
x_40 = l_Lake_AnsiMode_isEnabled(x_38, x_35, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = lean_box(x_34);
x_44 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_44, 0, x_38);
lean_closure_set(x_44, 1, x_43);
lean_closure_set(x_44, 2, x_41);
x_45 = l_Lake_loadWorkspace(x_1, x_44, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_alloc_closure((void*)(l_Lake_setupServerModule), 10, 3);
lean_closure_set(x_48, 0, x_2);
lean_closure_set(x_48, 1, x_17);
lean_closure_set(x_48, 2, x_3);
x_49 = l_Lake_Workspace_runFetchM___redArg(x_46, x_48, x_4, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec_ref(x_49);
x_52 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_52);
lean_dec(x_50);
x_53 = lean_io_wait(x_52, x_51);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec_ref(x_53);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = l_Lean_instToJsonModuleSetup_toJson(x_56);
x_58 = l_Lean_Json_compress(x_57);
x_59 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(x_58, x_55);
return x_59;
}
else
{
lean_object* x_60; 
lean_dec_ref(x_54);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_dec_ref(x_53);
x_6 = x_60;
goto block_15;
}
}
else
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_49, 1);
lean_inc(x_61);
lean_dec_ref(x_49);
x_6 = x_61;
goto block_15;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_62 = lean_ctor_get(x_45, 1);
lean_inc(x_62);
lean_dec_ref(x_45);
x_63 = l_Lake_setupFile___closed__1;
x_64 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_63, x_62);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = l_Lake_setupFile___boxed__const__1;
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = lean_ctor_get(x_30, 1);
lean_inc(x_71);
lean_dec_ref(x_30);
x_72 = lean_ctor_get(x_31, 0);
lean_inc(x_72);
lean_dec_ref(x_31);
x_73 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_72, x_71);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lake_setupFile___closed__2;
x_76 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_75, x_74);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set(x_76, 0, x_79);
return x_76;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
x_81 = l_Lake_setupFile___boxed__const__1;
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_inc_ref(x_19);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_83 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_83);
lean_dec_ref(x_19);
x_84 = lean_ctor_get(x_83, 4);
lean_inc_ref(x_84);
lean_dec_ref(x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc_ref(x_85);
lean_dec_ref(x_84);
x_86 = l_Lake_setupFile___closed__3;
x_87 = lean_box(0);
x_88 = lean_box(1);
x_89 = l_Lake_setupFile___closed__4;
x_90 = l_Lake_setupFile___closed__5;
x_91 = lean_array_push(x_90, x_85);
x_92 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_92, 0, x_86);
lean_ctor_set(x_92, 1, x_87);
lean_ctor_set(x_92, 2, x_88);
lean_ctor_set(x_92, 3, x_89);
lean_ctor_set(x_92, 4, x_91);
lean_ctor_set(x_92, 5, x_88);
lean_ctor_set_uint8(x_92, sizeof(void*)*6, x_27);
x_93 = l_Lean_instToJsonModuleSetup_toJson(x_92);
x_94 = l_Lean_Json_compress(x_93);
x_95 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(x_94, x_24);
return x_95;
}
}
else
{
lean_object* x_96; 
lean_dec(x_23);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_96 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set(x_21, 0, x_96);
return x_21;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_21, 0);
x_98 = lean_ctor_get(x_21, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_21);
x_99 = lean_string_utf8_byte_size(x_97);
x_100 = lean_unsigned_to_nat(0u);
x_101 = lean_nat_dec_eq(x_99, x_100);
lean_dec(x_99);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = lean_string_dec_eq(x_97, x_17);
lean_dec(x_97);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = l_Lake_invalidConfigEnvVar___closed__0;
x_104 = lean_io_getenv(x_103, x_98);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_106 = lean_ctor_get(x_4, 0);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec_ref(x_104);
x_108 = lean_ctor_get_uint8(x_106, sizeof(void*)*1 + 1);
x_109 = lean_ctor_get_uint8(x_106, sizeof(void*)*1 + 2);
x_110 = lean_ctor_get(x_106, 0);
x_111 = l_Lake_OutStream_get(x_110, x_107);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec_ref(x_111);
lean_inc(x_112);
x_114 = l_Lake_AnsiMode_isEnabled(x_112, x_109, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = lean_box(x_108);
x_118 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_118, 0, x_112);
lean_closure_set(x_118, 1, x_117);
lean_closure_set(x_118, 2, x_115);
x_119 = l_Lake_loadWorkspace(x_1, x_118, x_116);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_alloc_closure((void*)(l_Lake_setupServerModule), 10, 3);
lean_closure_set(x_122, 0, x_2);
lean_closure_set(x_122, 1, x_17);
lean_closure_set(x_122, 2, x_3);
x_123 = l_Lake_Workspace_runFetchM___redArg(x_120, x_122, x_4, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec_ref(x_123);
x_126 = lean_ctor_get(x_124, 0);
lean_inc_ref(x_126);
lean_dec(x_124);
x_127 = lean_io_wait(x_126, x_125);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec_ref(x_128);
x_131 = l_Lean_instToJsonModuleSetup_toJson(x_130);
x_132 = l_Lean_Json_compress(x_131);
x_133 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(x_132, x_129);
return x_133;
}
else
{
lean_object* x_134; 
lean_dec_ref(x_128);
x_134 = lean_ctor_get(x_127, 1);
lean_inc(x_134);
lean_dec_ref(x_127);
x_6 = x_134;
goto block_15;
}
}
else
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_123, 1);
lean_inc(x_135);
lean_dec_ref(x_123);
x_6 = x_135;
goto block_15;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_136 = lean_ctor_get(x_119, 1);
lean_inc(x_136);
lean_dec_ref(x_119);
x_137 = l_Lake_setupFile___closed__1;
x_138 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_137, x_136);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
x_141 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_143 = lean_ctor_get(x_104, 1);
lean_inc(x_143);
lean_dec_ref(x_104);
x_144 = lean_ctor_get(x_105, 0);
lean_inc(x_144);
lean_dec_ref(x_105);
x_145 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_144, x_143);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec_ref(x_145);
x_147 = l_Lake_setupFile___closed__2;
x_148 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_147, x_146);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
x_151 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_150)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_150;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_149);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_inc_ref(x_19);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_153 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_153);
lean_dec_ref(x_19);
x_154 = lean_ctor_get(x_153, 4);
lean_inc_ref(x_154);
lean_dec_ref(x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc_ref(x_155);
lean_dec_ref(x_154);
x_156 = l_Lake_setupFile___closed__3;
x_157 = lean_box(0);
x_158 = lean_box(1);
x_159 = l_Lake_setupFile___closed__4;
x_160 = l_Lake_setupFile___closed__5;
x_161 = lean_array_push(x_160, x_155);
x_162 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_162, 0, x_156);
lean_ctor_set(x_162, 1, x_157);
lean_ctor_set(x_162, 2, x_158);
lean_ctor_set(x_162, 3, x_159);
lean_ctor_set(x_162, 4, x_161);
lean_ctor_set(x_162, 5, x_158);
lean_ctor_set_uint8(x_162, sizeof(void*)*6, x_101);
x_163 = l_Lean_instToJsonModuleSetup_toJson(x_162);
x_164 = l_Lean_Json_compress(x_163);
x_165 = l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21(x_164, x_98);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; 
lean_dec(x_97);
lean_dec(x_17);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_166 = l_Lake_setupFile___boxed__const__2;
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_98);
return x_167;
}
}
block_15:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lake_setupFile___closed__0;
x_8 = l___private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21(x_7, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
x_11 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lake_setupFile___boxed__const__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
x_7 = lean_unbox(x_3);
x_8 = l_Lake_setupFile___lam__0(x_1, x_6, x_7, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_IO_eprintln___at___Lake_serve_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at_____private_Lake_CLI_Serve_0__Lake_setupFile_eprint_x21_spec__0(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_5, x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_10 = lean_array_uget(x_4, x_5);
x_11 = l_Lake_OutStream_logEntry(x_1, x_10, x_2, x_3, x_8);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_5, x_14);
x_5 = x_15;
x_7 = x_12;
x_8 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
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
x_2 = l_Lake_setupFile___closed__5;
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
LEAN_EXPORT lean_object* l_Lake_serve(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_inc_ref(x_1);
x_27 = lean_alloc_closure((void*)(l_Lake_loadWorkspace), 3, 1);
lean_closure_set(x_27, 0, x_1);
x_28 = l_Lake_LoggerIO_captureLog___redArg(x_27, x_3);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
x_56 = lean_unsigned_to_nat(0u);
x_57 = lean_array_get_size(x_32);
x_58 = lean_nat_dec_lt(x_56, x_57);
if (x_58 == 0)
{
lean_dec(x_57);
x_34 = x_30;
goto block_55;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_le(x_57, x_57);
if (x_59 == 0)
{
lean_dec(x_57);
x_34 = x_30;
goto block_55;
}
else
{
uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_60 = 1;
x_61 = 0;
x_62 = lean_box(1);
x_63 = lean_box(0);
x_64 = 0;
x_65 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__1(x_62, x_60, x_61, x_32, x_64, x_65, x_63, x_30);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec_ref(x_66);
x_34 = x_67;
goto block_55;
}
}
block_26:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_ctor_get(x_8, 7);
lean_inc_ref(x_9);
lean_dec_ref(x_8);
x_10 = l_Lake_serve___closed__0;
x_11 = l_Lake_serve___closed__2;
x_12 = l_Array_append___redArg(x_11, x_5);
lean_dec_ref(x_5);
x_13 = l_Array_append___redArg(x_12, x_2);
x_14 = lean_box(0);
x_15 = 1;
x_16 = 0;
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_14);
lean_ctor_set(x_17, 4, x_4);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_16);
x_18 = lean_io_process_spawn(x_17, x_6);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_io_process_child_wait(x_10, x_19, x_20);
lean_dec(x_19);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_18);
if (x_22 == 0)
{
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 0);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_18);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
block_55:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lake_serve___closed__3;
x_36 = l_IO_eprintln___at___Lake_serve_spec__0(x_35, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_38);
x_39 = l_Lake_Env_baseVars(x_38);
x_40 = l_Lake_invalidConfigEnvVar___closed__0;
x_41 = l_Lake_Log_toString(x_32);
lean_dec(x_32);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
if (lean_is_scalar(x_33)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_33;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_array_push(x_39, x_43);
x_45 = l_Lake_setupFile___closed__4;
x_4 = x_44;
x_5 = x_45;
x_6 = x_37;
goto block_26;
}
else
{
uint8_t x_46; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_33);
lean_dec(x_32);
x_50 = lean_ctor_get(x_31, 0);
lean_inc(x_50);
lean_dec_ref(x_31);
x_51 = lean_ctor_get(x_50, 0);
x_52 = lean_ctor_get(x_51, 4);
x_53 = lean_ctor_get(x_52, 4);
lean_inc_ref(x_53);
x_54 = l_Lake_Workspace_augmentedEnvVars(x_50);
x_4 = x_54;
x_5 = x_53;
x_6 = x_34;
goto block_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__1(x_1, x_9, x_10, x_4, x_11, x_12, x_7, x_8);
lean_dec_ref(x_4);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_serve(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
lean_object* initialize_Lake_Load_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Context(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Serve(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Load_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Context(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Run(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Lean_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load_Workspace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_noConfigFileCode = _init_l_Lake_noConfigFileCode();
l_Lake_invalidConfigEnvVar___closed__0 = _init_l_Lake_invalidConfigEnvVar___closed__0();
lean_mark_persistent(l_Lake_invalidConfigEnvVar___closed__0);
l_Lake_invalidConfigEnvVar = _init_l_Lake_invalidConfigEnvVar();
lean_mark_persistent(l_Lake_invalidConfigEnvVar);
l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2___closed__0 = _init_l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2___closed__0();
lean_mark_persistent(l_panic___at_____private_Lake_CLI_Serve_0__Lake_setupFile_print_x21_spec__2___closed__0);
l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__0);
l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__1);
l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___closed__2);
l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__1 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__1();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__1);
l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__2 = _init_l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__2();
lean_mark_persistent(l___private_Lake_CLI_Serve_0__Lake_setupFile_print_x21___boxed__const__2);
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
l_Lake_setupFile___boxed__const__1 = _init_l_Lake_setupFile___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___boxed__const__1);
l_Lake_setupFile___boxed__const__2 = _init_l_Lake_setupFile___boxed__const__2();
lean_mark_persistent(l_Lake_setupFile___boxed__const__2);
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
