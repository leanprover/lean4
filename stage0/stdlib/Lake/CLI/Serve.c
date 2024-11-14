// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: Init Lake.Load Lake.Build Lake.Util.MainM Lean.Util.FileSetupInfo
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
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__4___boxed__const__1;
lean_object* l_System_FilePath_join(lean_object*, lean_object*);
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanSrcPath(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_serve___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__2;
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
uint8_t l_Lake_Verbosity_minLogLv(uint8_t);
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___lambda__4___closed__3;
lean_object* l_Lake_buildImportsAndDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__3___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_println___at_Lean_Environment_displayStats___spec__3(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
static lean_object* l_Lake_setupFile___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_invalidConfigEnvVar___closed__1;
lean_object* l_String_toName(lean_object*);
lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2___boxed__const__1;
lean_object* l_Lake_LoggerIO_captureLog___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_setupFile___lambda__4___closed__4;
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_setupFile___closed__1;
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lake_MainM_runLogIO_replay(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_configFileExists(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_LeanOptions_fromOptions_x3f___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t _init_l_Lake_noConfigFileCode() {
_start:
{
uint32_t x_1; 
x_1 = 2;
return x_1;
}
}
static lean_object* _init_l_Lake_invalidConfigEnvVar___closed__1() {
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
x_1 = l_Lake_invalidConfigEnvVar___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_5);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = 1;
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_7, x_2, x_15);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = l_Lean_RBNode_insert___at_Lean_LeanOptions_fromOptions_x3f___spec__1(x_4, x_7, x_8);
x_2 = x_10;
x_4 = x_11;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_String_toName(x_4);
x_7 = l_Lake_Workspace_findModule_x3f(x_6, x_1);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_5;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_array_push(x_2, x_9);
x_2 = x_10;
x_3 = x_5;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__2___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_4);
x_6 = l_Lean_Json_compress(x_5);
x_7 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_6, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_io_error_to_string(x_12);
x_15 = 3;
x_16 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_15);
x_17 = lean_box(1);
x_18 = 1;
x_19 = 0;
x_20 = l_Lake_OutStream_logEntry(x_17, x_16, x_18, x_19, x_13);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = l_Lake_setupFile___lambda__2___boxed__const__1;
lean_ctor_set_tag(x_20, 1);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lake_setupFile___lambda__2___boxed__const__1;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lake_logToStream(x_3, x_1, x_5, x_2, x_4);
return x_6;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__4___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_setupFile___lambda__4___closed__1;
x_2 = lean_array_get_size(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__4___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__4___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_setupFile___lambda__4___closed__3;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___lambda__4___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_8 = l_Lake_Verbosity_minLogLv(x_7);
x_9 = lean_box(1);
x_10 = l_Lake_OutStream_get(x_9, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 2;
lean_inc(x_11);
x_14 = l_Lake_AnsiMode_isEnabled(x_11, x_13, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_18 = lean_box(x_8);
x_19 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__1___boxed), 5, 3);
lean_closure_set(x_19, 0, x_11);
lean_closure_set(x_19, 1, x_18);
lean_closure_set(x_19, 2, x_15);
x_20 = l_Lake_loadWorkspace(x_2, x_19, x_16);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_71; lean_object* x_72; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_116; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_104 = l_Lake_setupFile___lambda__4___closed__1;
x_105 = l_List_foldl___at_Lake_setupFile___spec__3(x_21, x_104, x_4);
lean_inc(x_3);
x_106 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_106, 0, x_3);
lean_closure_set(x_106, 1, x_105);
lean_inc(x_21);
x_116 = l_Lake_Workspace_runFetchM___rarg(x_21, x_106, x_1, x_22);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 0);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_io_wait(x_119, x_118);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
lean_dec(x_17);
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
lean_dec(x_124);
x_125 = lean_ctor_get(x_120, 1);
lean_inc(x_125);
lean_dec(x_120);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
lean_dec(x_123);
lean_ctor_set(x_121, 1, x_104);
lean_ctor_set(x_121, 0, x_126);
x_71 = x_121;
x_72 = x_125;
goto block_103;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
lean_dec(x_121);
x_128 = lean_ctor_get(x_120, 1);
lean_inc(x_128);
lean_dec(x_120);
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_104);
x_71 = x_130;
x_72 = x_128;
goto block_103;
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_121);
x_131 = lean_ctor_get(x_120, 1);
lean_inc(x_131);
lean_dec(x_120);
x_132 = l_Lake_setupFile___lambda__4___closed__4;
x_107 = x_132;
x_108 = x_131;
goto block_115;
}
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_116, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_116, 1);
lean_inc(x_134);
lean_dec(x_116);
x_107 = x_133;
x_108 = x_134;
goto block_115;
}
block_70:
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lake_Workspace_leanPath(x_21);
x_27 = l_Lake_Workspace_leanSrcPath(x_21);
lean_inc(x_27);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_24);
x_29 = l_Lean_searchModuleNameOfFileName(x_3, x_27, x_25);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_21);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = l_Lake_setupFile___lambda__2(x_28, x_32, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lake_Workspace_findModule_x3f(x_35, x_21);
lean_dec(x_21);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
x_38 = l_Lake_setupFile___lambda__2(x_28, x_37, x_34);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 4);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Array_append___rarg(x_44, x_45);
lean_dec(x_45);
x_47 = lean_ctor_get(x_40, 1);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = l_Array_append___rarg(x_46, x_49);
lean_dec(x_49);
x_51 = lean_ctor_get(x_48, 4);
lean_inc(x_51);
lean_dec(x_48);
x_52 = l_Array_append___rarg(x_50, x_51);
lean_dec(x_51);
x_53 = lean_array_size(x_52);
x_54 = 0;
x_55 = l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1(x_53, x_54, x_52);
x_56 = lean_box(0);
x_57 = lean_array_get_size(x_55);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_lt(x_58, x_57);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec(x_57);
lean_dec(x_55);
x_60 = l_Lake_setupFile___lambda__2(x_28, x_56, x_34);
return x_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_57, x_57);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_57);
lean_dec(x_55);
x_62 = l_Lake_setupFile___lambda__2(x_28, x_56, x_34);
return x_62;
}
else
{
size_t x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_64 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_55, x_54, x_63, x_56);
lean_dec(x_55);
x_65 = l_Lake_setupFile___lambda__2(x_28, x_64, x_34);
return x_65;
}
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_21);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_23);
if (x_66 == 0)
{
return x_23;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_23, 0);
x_68 = lean_ctor_get(x_23, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_23);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
block_103:
{
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = l_Lake_OutStream_get(x_9, x_72);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_76);
x_78 = l_Lake_AnsiMode_isEnabled(x_76, x_13, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_box(x_8);
x_82 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__1___boxed), 5, 3);
lean_closure_set(x_82, 0, x_76);
lean_closure_set(x_82, 1, x_81);
lean_closure_set(x_82, 2, x_79);
x_83 = l_Lake_MainM_runLogIO_replay(x_74, x_82, x_80);
lean_dec(x_74);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set(x_83, 0, x_73);
x_23 = x_83;
goto block_70;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_73);
lean_ctor_set(x_87, 1, x_86);
x_23 = x_87;
goto block_70;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_dec(x_71);
x_89 = l_Lake_OutStream_get(x_9, x_72);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_90);
x_92 = l_Lake_AnsiMode_isEnabled(x_90, x_13, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__3___boxed), 4, 2);
lean_closure_set(x_95, 0, x_90);
lean_closure_set(x_95, 1, x_93);
x_96 = l_Lake_MainM_runLogIO_replay(x_88, x_95, x_94);
lean_dec(x_88);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
lean_dec(x_98);
x_99 = l_Lake_setupFile___lambda__4___boxed__const__1;
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 0, x_99);
x_23 = x_96;
goto block_70;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = l_Lake_setupFile___lambda__4___boxed__const__1;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_23 = x_102;
goto block_70;
}
}
}
block_115:
{
lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_io_error_to_string(x_107);
x_110 = 3;
x_111 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set_uint8(x_111, sizeof(void*)*1, x_110);
x_112 = lean_array_push(x_104, x_111);
x_113 = l_Lake_setupFile___lambda__4___closed__2;
if (lean_is_scalar(x_17)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_17;
 lean_ctor_set_tag(x_114, 1);
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
x_71 = x_114;
x_72 = x_108;
goto block_103;
}
}
else
{
uint8_t x_135; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_20);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_20, 0);
lean_dec(x_136);
x_137 = l_Lake_setupFile___lambda__4___boxed__const__1;
lean_ctor_set(x_20, 0, x_137);
return x_20;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_20, 1);
lean_inc(x_138);
lean_dec(x_20);
x_139 = l_Lake_setupFile___lambda__4___boxed__const__1;
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
static lean_object* _init_l_Lake_setupFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Invalid Lake configuration.  Please restart the server after fixing the Lake configuration file.", 96, 96);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = l_Lake_noConfigFileCode;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___boxed__const__2() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = l_System_FilePath_join(x_6, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = l_System_FilePath_join(x_8, x_9);
lean_dec(x_9);
x_11 = l_Lake_configFileExists(x_10, x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
lean_dec(x_15);
x_16 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_11, 1);
lean_ctor_set(x_11, 0, x_16);
return x_11;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = l_Lake_setupFile___boxed__const__1;
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = l_Lake_invalidConfigEnvVar;
x_22 = lean_io_getenv(x_21, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = l_Lake_setupFile___lambda__4(x_4, x_1, x_2, x_3, x_25, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
x_29 = l_IO_eprint___at_IO_eprintln___spec__1(x_28, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lake_setupFile___closed__1;
x_32 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_31, x_30);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_32, 1);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = l_Lake_setupFile___boxed__const__2;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; 
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_io_error_to_string(x_39);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_box(1);
x_45 = 1;
x_46 = 0;
x_47 = l_Lake_OutStream_logEntry(x_44, x_43, x_45, x_46, x_40);
lean_dec(x_43);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = l_Lake_setupFile___boxed__const__2;
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_ctor_get(x_29, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_29, 1);
lean_inc(x_55);
lean_dec(x_29);
x_56 = lean_io_error_to_string(x_54);
x_57 = 3;
x_58 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_57);
x_59 = lean_box(1);
x_60 = 1;
x_61 = 0;
x_62 = l_Lake_OutStream_logEntry(x_59, x_58, x_60, x_61, x_55);
lean_dec(x_58);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
x_65 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_62, 1);
lean_ctor_set(x_62, 0, x_65);
return x_62;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
lean_dec(x_62);
x_67 = l_Lake_setupFile___boxed__const__2;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at_Lake_setupFile___spec__3(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_setupFile___lambda__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lake_setupFile___lambda__3(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_setupFile___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_box(1);
x_9 = 1;
x_10 = 0;
x_11 = l_Lake_OutStream_logEntry(x_8, x_7, x_9, x_10, x_5);
lean_dec(x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_5);
return x_17;
}
}
}
static lean_object* _init_l_Lake_serve___lambda__1___closed__1() {
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
static lean_object* _init_l_Lake_serve___lambda__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("--server", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_serve___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_serve___lambda__1___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_serve___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_serve___lambda__1___closed__3;
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_7, 1);
x_9 = lean_ctor_get(x_8, 7);
x_10 = l_Lake_serve___lambda__1___closed__4;
x_11 = l_Array_append___rarg(x_10, x_6);
x_12 = l_Array_append___rarg(x_11, x_2);
x_13 = lean_box(0);
x_14 = l_Lake_serve___lambda__1___closed__1;
x_15 = 0;
lean_inc(x_5);
lean_inc(x_9);
x_16 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_9);
lean_ctor_set(x_16, 2, x_12);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_5);
lean_ctor_set_uint8(x_16, sizeof(void*)*5, x_15);
x_17 = lean_io_process_spawn(x_16, x_4);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_io_process_child_wait(x_14, x_18, x_19);
lean_dec(x_18);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 0);
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lake_serve___closed__1() {
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_loadWorkspace), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lake_LoggerIO_captureLog___rarg(x_4, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lake_serve___closed__1;
x_16 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_15, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = l_Lake_Env_baseVars(x_18);
x_20 = l_Lake_Log_toString(x_11);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_7, 1, x_21);
lean_ctor_set(x_7, 0, x_22);
x_23 = lean_array_push(x_19, x_7);
x_24 = l_Lake_setupFile___lambda__4___closed__1;
lean_ctor_set(x_5, 1, x_24);
lean_ctor_set(x_5, 0, x_23);
x_25 = l_Lake_serve___lambda__1(x_1, x_2, x_5, x_17);
lean_dec(x_5);
lean_dec(x_1);
return x_25;
}
else
{
uint8_t x_26; 
lean_free_object(x_7);
lean_dec(x_11);
lean_free_object(x_5);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_free_object(x_5);
x_30 = lean_ctor_get(x_10, 0);
lean_inc(x_30);
lean_dec(x_10);
lean_inc(x_30);
x_31 = l_Lake_Workspace_augmentedEnvVars(x_30);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 6);
lean_inc(x_34);
lean_dec(x_33);
lean_ctor_set(x_7, 1, x_34);
lean_ctor_set(x_7, 0, x_31);
x_35 = l_Lake_serve___lambda__1(x_1, x_2, x_7, x_9);
lean_dec(x_7);
lean_dec(x_1);
return x_35;
}
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_12, x_12);
if (x_36 == 0)
{
lean_dec(x_12);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = l_Lake_serve___closed__1;
x_38 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_37, x_9);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
x_41 = l_Lake_Env_baseVars(x_40);
x_42 = l_Lake_Log_toString(x_11);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_7, 1, x_43);
lean_ctor_set(x_7, 0, x_44);
x_45 = lean_array_push(x_41, x_7);
x_46 = l_Lake_setupFile___lambda__4___closed__1;
lean_ctor_set(x_5, 1, x_46);
lean_ctor_set(x_5, 0, x_45);
x_47 = l_Lake_serve___lambda__1(x_1, x_2, x_5, x_39);
lean_dec(x_5);
lean_dec(x_1);
return x_47;
}
else
{
uint8_t x_48; 
lean_free_object(x_7);
lean_dec(x_11);
lean_free_object(x_5);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_38);
if (x_48 == 0)
{
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_38, 0);
x_50 = lean_ctor_get(x_38, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_38);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_11);
lean_free_object(x_5);
x_52 = lean_ctor_get(x_10, 0);
lean_inc(x_52);
lean_dec(x_10);
lean_inc(x_52);
x_53 = l_Lake_Workspace_augmentedEnvVars(x_52);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_ctor_get(x_54, 2);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 6);
lean_inc(x_56);
lean_dec(x_55);
lean_ctor_set(x_7, 1, x_56);
lean_ctor_set(x_7, 0, x_53);
x_57 = l_Lake_serve___lambda__1(x_1, x_2, x_7, x_9);
lean_dec(x_7);
lean_dec(x_1);
return x_57;
}
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
lean_free_object(x_5);
x_58 = 0;
x_59 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_60 = lean_box(0);
x_61 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_11, x_58, x_59, x_60, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_61, 1);
x_64 = lean_ctor_get(x_61, 0);
lean_dec(x_64);
x_65 = l_Lake_serve___closed__1;
x_66 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_65, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = l_Lake_Env_baseVars(x_68);
x_70 = l_Lake_Log_toString(x_11);
lean_dec(x_11);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_7, 1, x_71);
lean_ctor_set(x_7, 0, x_72);
x_73 = lean_array_push(x_69, x_7);
x_74 = l_Lake_setupFile___lambda__4___closed__1;
lean_ctor_set(x_61, 1, x_74);
lean_ctor_set(x_61, 0, x_73);
x_75 = l_Lake_serve___lambda__1(x_1, x_2, x_61, x_67);
lean_dec(x_61);
lean_dec(x_1);
return x_75;
}
else
{
uint8_t x_76; 
lean_free_object(x_61);
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_1);
x_76 = !lean_is_exclusive(x_66);
if (x_76 == 0)
{
return x_66;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_66, 0);
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_66);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
lean_dec(x_61);
x_81 = l_Lake_serve___closed__1;
x_82 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_81, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
x_85 = l_Lake_Env_baseVars(x_84);
x_86 = l_Lake_Log_toString(x_11);
lean_dec(x_11);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_7, 1, x_87);
lean_ctor_set(x_7, 0, x_88);
x_89 = lean_array_push(x_85, x_7);
x_90 = l_Lake_setupFile___lambda__4___closed__1;
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lake_serve___lambda__1(x_1, x_2, x_91, x_83);
lean_dec(x_91);
lean_dec(x_1);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_free_object(x_7);
lean_dec(x_11);
lean_dec(x_1);
x_93 = lean_ctor_get(x_82, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_82, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_95 = x_82;
} else {
 lean_dec_ref(x_82);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_11);
x_97 = lean_ctor_get(x_61, 1);
lean_inc(x_97);
lean_dec(x_61);
x_98 = lean_ctor_get(x_10, 0);
lean_inc(x_98);
lean_dec(x_10);
lean_inc(x_98);
x_99 = l_Lake_Workspace_augmentedEnvVars(x_98);
x_100 = lean_ctor_get(x_98, 0);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_100, 2);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get(x_101, 6);
lean_inc(x_102);
lean_dec(x_101);
lean_ctor_set(x_7, 1, x_102);
lean_ctor_set(x_7, 0, x_99);
x_103 = l_Lake_serve___lambda__1(x_1, x_2, x_7, x_97);
lean_dec(x_7);
lean_dec(x_1);
return x_103;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_104 = lean_ctor_get(x_5, 1);
x_105 = lean_ctor_get(x_7, 0);
x_106 = lean_ctor_get(x_7, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_7);
x_107 = lean_array_get_size(x_106);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_dec_lt(x_108, x_107);
if (x_109 == 0)
{
lean_dec(x_107);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = l_Lake_serve___closed__1;
x_111 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_110, x_104);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_1, 0);
lean_inc(x_113);
x_114 = l_Lake_Env_baseVars(x_113);
x_115 = l_Lake_Log_toString(x_106);
lean_dec(x_106);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = l_Lake_invalidConfigEnvVar;
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_114, x_118);
x_120 = l_Lake_setupFile___lambda__4___closed__1;
lean_ctor_set(x_5, 1, x_120);
lean_ctor_set(x_5, 0, x_119);
x_121 = l_Lake_serve___lambda__1(x_1, x_2, x_5, x_112);
lean_dec(x_5);
lean_dec(x_1);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_106);
lean_free_object(x_5);
lean_dec(x_1);
x_122 = lean_ctor_get(x_111, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_111, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_124 = x_111;
} else {
 lean_dec_ref(x_111);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_106);
lean_free_object(x_5);
x_126 = lean_ctor_get(x_105, 0);
lean_inc(x_126);
lean_dec(x_105);
lean_inc(x_126);
x_127 = l_Lake_Workspace_augmentedEnvVars(x_126);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_128, 2);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get(x_129, 6);
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_127);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lake_serve___lambda__1(x_1, x_2, x_131, x_104);
lean_dec(x_131);
lean_dec(x_1);
return x_132;
}
}
else
{
uint8_t x_133; 
x_133 = lean_nat_dec_le(x_107, x_107);
if (x_133 == 0)
{
lean_dec(x_107);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Lake_serve___closed__1;
x_135 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_134, x_104);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_137 = lean_ctor_get(x_1, 0);
lean_inc(x_137);
x_138 = l_Lake_Env_baseVars(x_137);
x_139 = l_Lake_Log_toString(x_106);
lean_dec(x_106);
x_140 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_140, 0, x_139);
x_141 = l_Lake_invalidConfigEnvVar;
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_140);
x_143 = lean_array_push(x_138, x_142);
x_144 = l_Lake_setupFile___lambda__4___closed__1;
lean_ctor_set(x_5, 1, x_144);
lean_ctor_set(x_5, 0, x_143);
x_145 = l_Lake_serve___lambda__1(x_1, x_2, x_5, x_136);
lean_dec(x_5);
lean_dec(x_1);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_106);
lean_free_object(x_5);
lean_dec(x_1);
x_146 = lean_ctor_get(x_135, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_135, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_148 = x_135;
} else {
 lean_dec_ref(x_135);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_106);
lean_free_object(x_5);
x_150 = lean_ctor_get(x_105, 0);
lean_inc(x_150);
lean_dec(x_105);
lean_inc(x_150);
x_151 = l_Lake_Workspace_augmentedEnvVars(x_150);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_ctor_get(x_152, 2);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_ctor_get(x_153, 6);
lean_inc(x_154);
lean_dec(x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_151);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lake_serve___lambda__1(x_1, x_2, x_155, x_104);
lean_dec(x_155);
lean_dec(x_1);
return x_156;
}
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; 
lean_free_object(x_5);
x_157 = 0;
x_158 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_159 = lean_box(0);
x_160 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_106, x_157, x_158, x_159, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = l_Lake_serve___closed__1;
x_164 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_163, x_161);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
x_167 = l_Lake_Env_baseVars(x_166);
x_168 = l_Lake_Log_toString(x_106);
lean_dec(x_106);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = l_Lake_invalidConfigEnvVar;
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = lean_array_push(x_167, x_171);
x_173 = l_Lake_setupFile___lambda__4___closed__1;
if (lean_is_scalar(x_162)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_162;
}
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_175 = l_Lake_serve___lambda__1(x_1, x_2, x_174, x_165);
lean_dec(x_174);
lean_dec(x_1);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_162);
lean_dec(x_106);
lean_dec(x_1);
x_176 = lean_ctor_get(x_164, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_164, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_178 = x_164;
} else {
 lean_dec_ref(x_164);
 x_178 = lean_box(0);
}
if (lean_is_scalar(x_178)) {
 x_179 = lean_alloc_ctor(1, 2, 0);
} else {
 x_179 = x_178;
}
lean_ctor_set(x_179, 0, x_176);
lean_ctor_set(x_179, 1, x_177);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_106);
x_180 = lean_ctor_get(x_160, 1);
lean_inc(x_180);
lean_dec(x_160);
x_181 = lean_ctor_get(x_105, 0);
lean_inc(x_181);
lean_dec(x_105);
lean_inc(x_181);
x_182 = l_Lake_Workspace_augmentedEnvVars(x_181);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
lean_dec(x_181);
x_184 = lean_ctor_get(x_183, 2);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_184, 6);
lean_inc(x_185);
lean_dec(x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_182);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Lake_serve___lambda__1(x_1, x_2, x_186, x_180);
lean_dec(x_186);
lean_dec(x_1);
return x_187;
}
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_188 = lean_ctor_get(x_5, 0);
x_189 = lean_ctor_get(x_5, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_5);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_192 = x_188;
} else {
 lean_dec_ref(x_188);
 x_192 = lean_box(0);
}
x_193 = lean_array_get_size(x_191);
x_194 = lean_unsigned_to_nat(0u);
x_195 = lean_nat_dec_lt(x_194, x_193);
if (x_195 == 0)
{
lean_dec(x_193);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_196; lean_object* x_197; 
x_196 = l_Lake_serve___closed__1;
x_197 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_196, x_189);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec(x_197);
x_199 = lean_ctor_get(x_1, 0);
lean_inc(x_199);
x_200 = l_Lake_Env_baseVars(x_199);
x_201 = l_Lake_Log_toString(x_191);
lean_dec(x_191);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
x_203 = l_Lake_invalidConfigEnvVar;
if (lean_is_scalar(x_192)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_192;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
x_205 = lean_array_push(x_200, x_204);
x_206 = l_Lake_setupFile___lambda__4___closed__1;
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
x_208 = l_Lake_serve___lambda__1(x_1, x_2, x_207, x_198);
lean_dec(x_207);
lean_dec(x_1);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_1);
x_209 = lean_ctor_get(x_197, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_197, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_211 = x_197;
} else {
 lean_dec_ref(x_197);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_191);
x_213 = lean_ctor_get(x_190, 0);
lean_inc(x_213);
lean_dec(x_190);
lean_inc(x_213);
x_214 = l_Lake_Workspace_augmentedEnvVars(x_213);
x_215 = lean_ctor_get(x_213, 0);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_215, 2);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get(x_216, 6);
lean_inc(x_217);
lean_dec(x_216);
if (lean_is_scalar(x_192)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_192;
}
lean_ctor_set(x_218, 0, x_214);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lake_serve___lambda__1(x_1, x_2, x_218, x_189);
lean_dec(x_218);
lean_dec(x_1);
return x_219;
}
}
else
{
uint8_t x_220; 
x_220 = lean_nat_dec_le(x_193, x_193);
if (x_220 == 0)
{
lean_dec(x_193);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_221; lean_object* x_222; 
x_221 = l_Lake_serve___closed__1;
x_222 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_221, x_189);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_ctor_get(x_1, 0);
lean_inc(x_224);
x_225 = l_Lake_Env_baseVars(x_224);
x_226 = l_Lake_Log_toString(x_191);
lean_dec(x_191);
x_227 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = l_Lake_invalidConfigEnvVar;
if (lean_is_scalar(x_192)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_192;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_227);
x_230 = lean_array_push(x_225, x_229);
x_231 = l_Lake_setupFile___lambda__4___closed__1;
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lake_serve___lambda__1(x_1, x_2, x_232, x_223);
lean_dec(x_232);
lean_dec(x_1);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_1);
x_234 = lean_ctor_get(x_222, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_222, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_236 = x_222;
} else {
 lean_dec_ref(x_222);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_191);
x_238 = lean_ctor_get(x_190, 0);
lean_inc(x_238);
lean_dec(x_190);
lean_inc(x_238);
x_239 = l_Lake_Workspace_augmentedEnvVars(x_238);
x_240 = lean_ctor_get(x_238, 0);
lean_inc(x_240);
lean_dec(x_238);
x_241 = lean_ctor_get(x_240, 2);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_ctor_get(x_241, 6);
lean_inc(x_242);
lean_dec(x_241);
if (lean_is_scalar(x_192)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_192;
}
lean_ctor_set(x_243, 0, x_239);
lean_ctor_set(x_243, 1, x_242);
x_244 = l_Lake_serve___lambda__1(x_1, x_2, x_243, x_189);
lean_dec(x_243);
lean_dec(x_1);
return x_244;
}
}
else
{
size_t x_245; size_t x_246; lean_object* x_247; lean_object* x_248; 
x_245 = 0;
x_246 = lean_usize_of_nat(x_193);
lean_dec(x_193);
x_247 = lean_box(0);
x_248 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_191, x_245, x_246, x_247, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_250 = x_248;
} else {
 lean_dec_ref(x_248);
 x_250 = lean_box(0);
}
x_251 = l_Lake_serve___closed__1;
x_252 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_251, x_249);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = lean_ctor_get(x_1, 0);
lean_inc(x_254);
x_255 = l_Lake_Env_baseVars(x_254);
x_256 = l_Lake_Log_toString(x_191);
lean_dec(x_191);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
x_258 = l_Lake_invalidConfigEnvVar;
if (lean_is_scalar(x_192)) {
 x_259 = lean_alloc_ctor(0, 2, 0);
} else {
 x_259 = x_192;
}
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_257);
x_260 = lean_array_push(x_255, x_259);
x_261 = l_Lake_setupFile___lambda__4___closed__1;
if (lean_is_scalar(x_250)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_250;
}
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = l_Lake_serve___lambda__1(x_1, x_2, x_262, x_253);
lean_dec(x_262);
lean_dec(x_1);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec(x_250);
lean_dec(x_192);
lean_dec(x_191);
lean_dec(x_1);
x_264 = lean_ctor_get(x_252, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_252, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_266 = x_252;
} else {
 lean_dec_ref(x_252);
 x_266 = lean_box(0);
}
if (lean_is_scalar(x_266)) {
 x_267 = lean_alloc_ctor(1, 2, 0);
} else {
 x_267 = x_266;
}
lean_ctor_set(x_267, 0, x_264);
lean_ctor_set(x_267, 1, x_265);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_191);
x_268 = lean_ctor_get(x_248, 1);
lean_inc(x_268);
lean_dec(x_248);
x_269 = lean_ctor_get(x_190, 0);
lean_inc(x_269);
lean_dec(x_190);
lean_inc(x_269);
x_270 = l_Lake_Workspace_augmentedEnvVars(x_269);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
lean_dec(x_269);
x_272 = lean_ctor_get(x_271, 2);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_ctor_get(x_272, 6);
lean_inc(x_273);
lean_dec(x_272);
if (lean_is_scalar(x_192)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_192;
}
lean_ctor_set(x_274, 0, x_270);
lean_ctor_set(x_274, 1, x_273);
x_275 = l_Lake_serve___lambda__1(x_1, x_2, x_274, x_268);
lean_dec(x_274);
lean_dec(x_1);
return x_275;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_serve___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_serve(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Load(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_MainM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FileSetupInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Serve(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Load(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_MainM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FileSetupInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_noConfigFileCode = _init_l_Lake_noConfigFileCode();
l_Lake_invalidConfigEnvVar___closed__1 = _init_l_Lake_invalidConfigEnvVar___closed__1();
lean_mark_persistent(l_Lake_invalidConfigEnvVar___closed__1);
l_Lake_invalidConfigEnvVar = _init_l_Lake_invalidConfigEnvVar();
lean_mark_persistent(l_Lake_invalidConfigEnvVar);
l_Lake_setupFile___lambda__2___boxed__const__1 = _init_l_Lake_setupFile___lambda__2___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___lambda__2___boxed__const__1);
l_Lake_setupFile___lambda__4___closed__1 = _init_l_Lake_setupFile___lambda__4___closed__1();
lean_mark_persistent(l_Lake_setupFile___lambda__4___closed__1);
l_Lake_setupFile___lambda__4___closed__2 = _init_l_Lake_setupFile___lambda__4___closed__2();
lean_mark_persistent(l_Lake_setupFile___lambda__4___closed__2);
l_Lake_setupFile___lambda__4___closed__3 = _init_l_Lake_setupFile___lambda__4___closed__3();
lean_mark_persistent(l_Lake_setupFile___lambda__4___closed__3);
l_Lake_setupFile___lambda__4___closed__4 = _init_l_Lake_setupFile___lambda__4___closed__4();
lean_mark_persistent(l_Lake_setupFile___lambda__4___closed__4);
l_Lake_setupFile___lambda__4___boxed__const__1 = _init_l_Lake_setupFile___lambda__4___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___lambda__4___boxed__const__1);
l_Lake_setupFile___closed__1 = _init_l_Lake_setupFile___closed__1();
lean_mark_persistent(l_Lake_setupFile___closed__1);
l_Lake_setupFile___boxed__const__1 = _init_l_Lake_setupFile___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___boxed__const__1);
l_Lake_setupFile___boxed__const__2 = _init_l_Lake_setupFile___boxed__const__2();
lean_mark_persistent(l_Lake_setupFile___boxed__const__2);
l_Lake_serve___lambda__1___closed__1 = _init_l_Lake_serve___lambda__1___closed__1();
lean_mark_persistent(l_Lake_serve___lambda__1___closed__1);
l_Lake_serve___lambda__1___closed__2 = _init_l_Lake_serve___lambda__1___closed__2();
lean_mark_persistent(l_Lake_serve___lambda__1___closed__2);
l_Lake_serve___lambda__1___closed__3 = _init_l_Lake_serve___lambda__1___closed__3();
lean_mark_persistent(l_Lake_serve___lambda__1___closed__3);
l_Lake_serve___lambda__1___closed__4 = _init_l_Lake_serve___lambda__1___closed__4();
lean_mark_persistent(l_Lake_serve___lambda__1___closed__4);
l_Lake_serve___closed__1 = _init_l_Lake_serve___closed__1();
lean_mark_persistent(l_Lake_serve___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
