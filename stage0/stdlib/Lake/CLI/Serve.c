// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: Lake.Load.Config Lake.Build.Context Lake.Util.MainM Lake.Build.Run Lake.Build.Module Lake.Load.Package Lake.Load.Lean.Elab Lake.Load.Workspace Lake.Util.MainM Lake.Util.IO
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
lean_object* l_Lean_toJsonModuleSetup____x40_Lean_Setup_3122765986____hygCtx___hyg_119_(lean_object*);
static lean_object* l_Lake_setupFile___closed__5;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprint___at___Lake_setupFile_spec__2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
static lean_object* l_Lake_setupFile___closed__4;
lean_object* l_Lake_LoggerIO_captureLog___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
static lean_object* l_Lake_setupFile___closed__3;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__1;
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___boxed__const__2;
lean_object* lean_get_stderr(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__0;
static lean_object* l_Lake_setupFile___closed__0;
LEAN_EXPORT lean_object* l_Lake_setupFile___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___closed__2;
static lean_object* l_Lake_setupFile___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___boxed__const__1;
static lean_object* l_Lake_serve___closed__2;
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at___Lake_setupFile_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_eprintln___at___Lake_setupFile_spec__3(lean_object*, lean_object*);
static lean_object* l_Lake_invalidConfigEnvVar___closed__0;
static lean_object* l_Lake_setupFile___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_IO_println___at___Lake_setupFile_spec__0(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
static lean_object* l_Lake_setupFile___closed__6;
extern lean_object* l_Lake_configModuleName;
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_IO_print___at___IO_println___at___Lake_setupFile_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_println___at___Lake_setupFile_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_print___at___IO_println___at___Lake_setupFile_spec__0_spec__0(x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_IO_eprint___at___Lake_setupFile_spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_IO_eprintln___at___Lake_setupFile_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 10;
x_4 = lean_string_push(x_1, x_3);
x_5 = l_IO_eprint___at___Lake_setupFile_spec__2(x_4, x_2);
return x_5;
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
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_setupFile___closed__0;
x_2 = lean_mk_io_user_error(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to load workspace", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = l_Lake_setupFile___closed__2;
x_2 = 3;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_setupFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.", 95, 95);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_configModuleName;
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__7() {
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
lean_object* x_6; lean_object* x_7; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc_ref(x_2);
x_22 = l_Lake_resolvePath(x_2, x_5);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_ctor_get(x_1, 6);
lean_inc_ref(x_26);
x_27 = l_Lake_realConfigFile(x_26, x_24);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_string_utf8_byte_size(x_29);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_31, x_32);
lean_dec(x_31);
if (x_33 == 0)
{
uint8_t x_34; 
lean_free_object(x_27);
x_34 = lean_string_dec_eq(x_29, x_23);
lean_dec(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lake_invalidConfigEnvVar___closed__0;
x_36 = lean_io_getenv(x_35, x_30);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = lean_box(1);
x_40 = l_Lake_OutStream_get(x_39, x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_44 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_41);
x_45 = l_Lake_AnsiMode_isEnabled(x_41, x_44, x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec_ref(x_45);
x_48 = lean_box(x_43);
x_49 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_49, 0, x_41);
lean_closure_set(x_49, 1, x_48);
lean_closure_set(x_49, 2, x_46);
x_50 = l_Lake_loadWorkspace(x_1, x_49, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec_ref(x_50);
x_53 = lean_alloc_closure((void*)(l_Lake_setupServerModule), 10, 3);
lean_closure_set(x_53, 0, x_2);
lean_closure_set(x_53, 1, x_23);
lean_closure_set(x_53, 2, x_3);
x_54 = l_Lake_Workspace_runFetchM___redArg(x_51, x_53, x_4, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_ctor_get(x_55, 0);
lean_inc_ref(x_57);
lean_dec(x_55);
x_58 = lean_io_wait(x_57, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = l_Lean_toJsonModuleSetup____x40_Lean_Setup_3122765986____hygCtx___hyg_119_(x_61);
x_63 = l_Lean_Json_compress(x_62);
x_64 = l_IO_println___at___Lake_setupFile_spec__0(x_63, x_60);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_69 = lean_ctor_get(x_64, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec_ref(x_64);
x_71 = lean_io_error_to_string(x_69);
x_72 = 1;
x_73 = 0;
x_74 = 3;
x_75 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_75, 0, x_71);
lean_ctor_set_uint8(x_75, sizeof(void*)*1, x_74);
x_76 = l_Lake_OutStream_logEntry(x_39, x_75, x_72, x_73, x_70);
lean_dec_ref(x_75);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
x_79 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_76, 1);
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
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_59);
x_83 = lean_ctor_get(x_58, 1);
lean_inc(x_83);
lean_dec_ref(x_58);
x_84 = l_Lake_setupFile___closed__1;
x_6 = x_84;
x_7 = x_83;
goto block_21;
}
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_54, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_54, 1);
lean_inc(x_86);
lean_dec_ref(x_54);
x_6 = x_85;
x_7 = x_86;
goto block_21;
}
}
else
{
lean_object* x_87; uint8_t x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_23);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_87 = lean_ctor_get(x_50, 1);
lean_inc(x_87);
lean_dec_ref(x_50);
x_88 = 1;
x_89 = 0;
x_90 = l_Lake_setupFile___closed__3;
x_91 = l_Lake_OutStream_logEntry(x_39, x_90, x_88, x_89, x_87);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
x_94 = l_Lake_setupFile___boxed__const__1;
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
x_96 = l_Lake_setupFile___boxed__const__1;
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_23);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_98 = lean_ctor_get(x_36, 1);
lean_inc(x_98);
lean_dec_ref(x_36);
x_99 = lean_ctor_get(x_37, 0);
lean_inc(x_99);
lean_dec_ref(x_37);
x_100 = l_IO_eprint___at___Lake_setupFile_spec__2(x_99, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = l_Lake_setupFile___closed__4;
x_103 = l_IO_eprintln___at___Lake_setupFile_spec__3(x_102, x_101);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
lean_dec(x_105);
x_106 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_103, 1);
lean_ctor_set(x_103, 0, x_106);
return x_103;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_dec(x_103);
x_108 = l_Lake_setupFile___boxed__const__1;
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_110 = lean_ctor_get(x_103, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_103, 1);
lean_inc(x_111);
lean_dec_ref(x_103);
x_112 = lean_io_error_to_string(x_110);
x_113 = 1;
x_114 = 0;
x_115 = lean_box(1);
x_116 = 3;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
x_118 = l_Lake_OutStream_logEntry(x_115, x_117, x_113, x_114, x_111);
lean_dec_ref(x_117);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_118, 0);
lean_dec(x_120);
x_121 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_118, 1);
lean_ctor_set(x_118, 0, x_121);
return x_118;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_118, 1);
lean_inc(x_122);
lean_dec(x_118);
x_123 = l_Lake_setupFile___boxed__const__1;
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_125 = lean_ctor_get(x_100, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_100, 1);
lean_inc(x_126);
lean_dec_ref(x_100);
x_127 = lean_io_error_to_string(x_125);
x_128 = 1;
x_129 = 0;
x_130 = lean_box(1);
x_131 = 3;
x_132 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set_uint8(x_132, sizeof(void*)*1, x_131);
x_133 = l_Lake_OutStream_logEntry(x_130, x_132, x_128, x_129, x_126);
lean_dec_ref(x_132);
x_134 = !lean_is_exclusive(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_133, 0);
lean_dec(x_135);
x_136 = l_Lake_setupFile___boxed__const__1;
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
x_138 = l_Lake_setupFile___boxed__const__1;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_inc_ref(x_25);
lean_dec(x_23);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_140 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_140);
lean_dec_ref(x_25);
x_141 = lean_ctor_get(x_140, 4);
lean_inc_ref(x_141);
lean_dec_ref(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc_ref(x_142);
lean_dec_ref(x_141);
x_143 = l_Lake_setupFile___closed__5;
x_144 = lean_box(0);
x_145 = lean_box(1);
x_146 = l_Lake_setupFile___closed__6;
x_147 = l_Lake_setupFile___closed__7;
x_148 = lean_array_push(x_147, x_142);
x_149 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_149, 0, x_143);
lean_ctor_set(x_149, 1, x_144);
lean_ctor_set(x_149, 2, x_145);
lean_ctor_set(x_149, 3, x_146);
lean_ctor_set(x_149, 4, x_148);
lean_ctor_set(x_149, 5, x_145);
lean_ctor_set_uint8(x_149, sizeof(void*)*6, x_33);
x_150 = l_Lean_toJsonModuleSetup____x40_Lean_Setup_3122765986____hygCtx___hyg_119_(x_149);
x_151 = l_Lean_Json_compress(x_150);
x_152 = l_IO_println___at___Lake_setupFile_spec__0(x_151, x_30);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
return x_152;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_152);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; uint8_t x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_157 = lean_ctor_get(x_152, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_152, 1);
lean_inc(x_158);
lean_dec_ref(x_152);
x_159 = lean_io_error_to_string(x_157);
x_160 = 1;
x_161 = 0;
x_162 = lean_box(1);
x_163 = 3;
x_164 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_164, 0, x_159);
lean_ctor_set_uint8(x_164, sizeof(void*)*1, x_163);
x_165 = l_Lake_OutStream_logEntry(x_162, x_164, x_160, x_161, x_158);
lean_dec_ref(x_164);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_165, 0);
lean_dec(x_167);
x_168 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_165, 1);
lean_ctor_set(x_165, 0, x_168);
return x_165;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_165, 1);
lean_inc(x_169);
lean_dec(x_165);
x_170 = l_Lake_setupFile___boxed__const__1;
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
}
}
else
{
lean_object* x_172; 
lean_dec(x_29);
lean_dec(x_23);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_172 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 0, x_172);
return x_27;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_173 = lean_ctor_get(x_27, 0);
x_174 = lean_ctor_get(x_27, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_27);
x_175 = lean_string_utf8_byte_size(x_173);
x_176 = lean_unsigned_to_nat(0u);
x_177 = lean_nat_dec_eq(x_175, x_176);
lean_dec(x_175);
if (x_177 == 0)
{
uint8_t x_178; 
x_178 = lean_string_dec_eq(x_173, x_23);
lean_dec(x_173);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = l_Lake_invalidConfigEnvVar___closed__0;
x_180 = lean_io_getenv(x_179, x_174);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
lean_dec_ref(x_180);
x_183 = lean_box(1);
x_184 = l_Lake_OutStream_get(x_183, x_182);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_188 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
lean_inc(x_185);
x_189 = l_Lake_AnsiMode_isEnabled(x_185, x_188, x_186);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec_ref(x_189);
x_192 = lean_box(x_187);
x_193 = lean_alloc_closure((void*)(l_Lake_setupFile___lam__0___boxed), 5, 3);
lean_closure_set(x_193, 0, x_185);
lean_closure_set(x_193, 1, x_192);
lean_closure_set(x_193, 2, x_190);
x_194 = l_Lake_loadWorkspace(x_1, x_193, x_191);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec_ref(x_194);
x_197 = lean_alloc_closure((void*)(l_Lake_setupServerModule), 10, 3);
lean_closure_set(x_197, 0, x_2);
lean_closure_set(x_197, 1, x_23);
lean_closure_set(x_197, 2, x_3);
x_198 = l_Lake_Workspace_runFetchM___redArg(x_195, x_197, x_4, x_196);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec_ref(x_198);
x_201 = lean_ctor_get(x_199, 0);
lean_inc_ref(x_201);
lean_dec(x_199);
x_202 = lean_io_wait(x_201, x_200);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec_ref(x_202);
x_205 = lean_ctor_get(x_203, 0);
lean_inc(x_205);
lean_dec_ref(x_203);
x_206 = l_Lean_toJsonModuleSetup____x40_Lean_Setup_3122765986____hygCtx___hyg_119_(x_205);
x_207 = l_Lean_Json_compress(x_206);
x_208 = l_IO_println___at___Lake_setupFile_spec__0(x_207, x_204);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_211 = x_208;
} else {
 lean_dec_ref(x_208);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; uint8_t x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_213 = lean_ctor_get(x_208, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_208, 1);
lean_inc(x_214);
lean_dec_ref(x_208);
x_215 = lean_io_error_to_string(x_213);
x_216 = 1;
x_217 = 0;
x_218 = 3;
x_219 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_219, 0, x_215);
lean_ctor_set_uint8(x_219, sizeof(void*)*1, x_218);
x_220 = l_Lake_OutStream_logEntry(x_183, x_219, x_216, x_217, x_214);
lean_dec_ref(x_219);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_222 = x_220;
} else {
 lean_dec_ref(x_220);
 x_222 = lean_box(0);
}
x_223 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_222)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_222;
 lean_ctor_set_tag(x_224, 1);
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; 
lean_dec_ref(x_203);
x_225 = lean_ctor_get(x_202, 1);
lean_inc(x_225);
lean_dec_ref(x_202);
x_226 = l_Lake_setupFile___closed__1;
x_6 = x_226;
x_7 = x_225;
goto block_21;
}
}
else
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_198, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_198, 1);
lean_inc(x_228);
lean_dec_ref(x_198);
x_6 = x_227;
x_7 = x_228;
goto block_21;
}
}
else
{
lean_object* x_229; uint8_t x_230; uint8_t x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_23);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_229 = lean_ctor_get(x_194, 1);
lean_inc(x_229);
lean_dec_ref(x_194);
x_230 = 1;
x_231 = 0;
x_232 = l_Lake_setupFile___closed__3;
x_233 = l_Lake_OutStream_logEntry(x_183, x_232, x_230, x_231, x_229);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_235 = x_233;
} else {
 lean_dec_ref(x_233);
 x_235 = lean_box(0);
}
x_236 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_235)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_235;
 lean_ctor_set_tag(x_237, 1);
}
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_234);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_23);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_238 = lean_ctor_get(x_180, 1);
lean_inc(x_238);
lean_dec_ref(x_180);
x_239 = lean_ctor_get(x_181, 0);
lean_inc(x_239);
lean_dec_ref(x_181);
x_240 = l_IO_eprint___at___Lake_setupFile_spec__2(x_239, x_238);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec_ref(x_240);
x_242 = l_Lake_setupFile___closed__4;
x_243 = l_IO_eprintln___at___Lake_setupFile_spec__3(x_242, x_241);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
x_246 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(1, 2, 0);
} else {
 x_247 = x_245;
 lean_ctor_set_tag(x_247, 1);
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; uint8_t x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_248 = lean_ctor_get(x_243, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_243, 1);
lean_inc(x_249);
lean_dec_ref(x_243);
x_250 = lean_io_error_to_string(x_248);
x_251 = 1;
x_252 = 0;
x_253 = lean_box(1);
x_254 = 3;
x_255 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_255, 0, x_250);
lean_ctor_set_uint8(x_255, sizeof(void*)*1, x_254);
x_256 = l_Lake_OutStream_logEntry(x_253, x_255, x_251, x_252, x_249);
lean_dec_ref(x_255);
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_258 = x_256;
} else {
 lean_dec_ref(x_256);
 x_258 = lean_box(0);
}
x_259 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_258)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_258;
 lean_ctor_set_tag(x_260, 1);
}
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_257);
return x_260;
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; uint8_t x_265; lean_object* x_266; uint8_t x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_261 = lean_ctor_get(x_240, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_240, 1);
lean_inc(x_262);
lean_dec_ref(x_240);
x_263 = lean_io_error_to_string(x_261);
x_264 = 1;
x_265 = 0;
x_266 = lean_box(1);
x_267 = 3;
x_268 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_268, 0, x_263);
lean_ctor_set_uint8(x_268, sizeof(void*)*1, x_267);
x_269 = l_Lake_OutStream_logEntry(x_266, x_268, x_264, x_265, x_262);
lean_dec_ref(x_268);
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_271 = x_269;
} else {
 lean_dec_ref(x_269);
 x_271 = lean_box(0);
}
x_272 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_271)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_271;
 lean_ctor_set_tag(x_273, 1);
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_270);
return x_273;
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_inc_ref(x_25);
lean_dec(x_23);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_274 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_274);
lean_dec_ref(x_25);
x_275 = lean_ctor_get(x_274, 4);
lean_inc_ref(x_275);
lean_dec_ref(x_274);
x_276 = lean_ctor_get(x_275, 0);
lean_inc_ref(x_276);
lean_dec_ref(x_275);
x_277 = l_Lake_setupFile___closed__5;
x_278 = lean_box(0);
x_279 = lean_box(1);
x_280 = l_Lake_setupFile___closed__6;
x_281 = l_Lake_setupFile___closed__7;
x_282 = lean_array_push(x_281, x_276);
x_283 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_278);
lean_ctor_set(x_283, 2, x_279);
lean_ctor_set(x_283, 3, x_280);
lean_ctor_set(x_283, 4, x_282);
lean_ctor_set(x_283, 5, x_279);
lean_ctor_set_uint8(x_283, sizeof(void*)*6, x_177);
x_284 = l_Lean_toJsonModuleSetup____x40_Lean_Setup_3122765986____hygCtx___hyg_119_(x_283);
x_285 = l_Lean_Json_compress(x_284);
x_286 = l_IO_println___at___Lake_setupFile_spec__0(x_285, x_174);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
if (lean_is_exclusive(x_286)) {
 lean_ctor_release(x_286, 0);
 lean_ctor_release(x_286, 1);
 x_289 = x_286;
} else {
 lean_dec_ref(x_286);
 x_289 = lean_box(0);
}
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_288);
return x_290;
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_291 = lean_ctor_get(x_286, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_286, 1);
lean_inc(x_292);
lean_dec_ref(x_286);
x_293 = lean_io_error_to_string(x_291);
x_294 = 1;
x_295 = 0;
x_296 = lean_box(1);
x_297 = 3;
x_298 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_298, 0, x_293);
lean_ctor_set_uint8(x_298, sizeof(void*)*1, x_297);
x_299 = l_Lake_OutStream_logEntry(x_296, x_298, x_294, x_295, x_292);
lean_dec_ref(x_298);
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_301 = x_299;
} else {
 lean_dec_ref(x_299);
 x_301 = lean_box(0);
}
x_302 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_301)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_301;
 lean_ctor_set_tag(x_303, 1);
}
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_300);
return x_303;
}
}
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_173);
lean_dec(x_23);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_304 = l_Lake_setupFile___boxed__const__2;
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_174);
return x_305;
}
}
block_21:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_io_error_to_string(x_6);
x_9 = 1;
x_10 = 0;
x_11 = lean_box(1);
x_12 = 3;
x_13 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_12);
x_14 = l_Lake_OutStream_logEntry(x_11, x_13, x_9, x_10, x_7);
lean_dec_ref(x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lake_setupFile___boxed__const__1;
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8) {
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
x_2 = l_Lake_setupFile___closed__7;
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
x_66 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(x_62, x_60, x_61, x_32, x_64, x_65, x_63, x_30);
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
x_36 = l_IO_eprintln___at___Lake_setupFile_spec__3(x_35, x_34);
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
x_45 = l_Lake_setupFile___closed__6;
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
x_52 = lean_ctor_get(x_51, 3);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_13 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lake_serve_spec__0(x_1, x_9, x_10, x_4, x_11, x_12, x_7, x_8);
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
lean_object* initialize_Lake_Util_MainM(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Run(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Lean_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load_Workspace(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_MainM(uint8_t builtin, lean_object*);
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
res = initialize_Lake_Util_MainM(builtin, lean_io_mk_world());
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
res = initialize_Lake_Util_MainM(builtin, lean_io_mk_world());
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
l_Lake_setupFile___closed__7 = _init_l_Lake_setupFile___closed__7();
lean_mark_persistent(l_Lake_setupFile___closed__7);
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
