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
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
lean_object* l_IO_println___at_Lean_instEval___spec__1(lean_object*, lean_object*);
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
lean_object* l_Lake_loadWorkspace(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1___boxed__const__1;
lean_object* l_Lean_searchModuleNameOfFileName(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
static lean_object* l_Lake_setupFile___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_invalidConfigEnvVar___closed__1;
lean_object* l_String_toName(lean_object*);
lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lake_setupFile___lambda__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_4);
x_6 = l_Lean_Json_compress(x_5);
x_7 = l_IO_println___at_Lean_instEval___spec__1(x_6, x_3);
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
x_23 = l_Lake_setupFile___lambda__1___boxed__const__1;
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
x_25 = l_Lake_setupFile___lambda__1___boxed__const__1;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
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
uint8_t x_7; uint8_t x_8; lean_object* x_9; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 3);
x_8 = l_Lake_Verbosity_minLogLv(x_7);
x_133 = 0;
x_134 = l_Lake_setupFile___lambda__4___closed__1;
x_135 = l_Lake_loadWorkspace(x_4, x_133, x_134, x_6);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_box(1);
x_141 = l_Lake_OutStream_get(x_140, x_137);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec(x_141);
x_144 = 2;
lean_inc(x_142);
x_145 = l_Lake_AnsiMode_isEnabled(x_142, x_144, x_143);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_box(x_8);
x_149 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_149, 0, x_142);
lean_closure_set(x_149, 1, x_148);
lean_closure_set(x_149, 2, x_146);
x_150 = l_Lake_MainM_runLogIO_replay(x_139, x_149, x_147);
lean_dec(x_139);
x_151 = !lean_is_exclusive(x_150);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_ctor_get(x_150, 0);
lean_dec(x_152);
lean_ctor_set(x_150, 0, x_138);
x_9 = x_150;
goto block_132;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_138);
lean_ctor_set(x_154, 1, x_153);
x_9 = x_154;
goto block_132;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_155 = lean_ctor_get(x_135, 1);
lean_inc(x_155);
lean_dec(x_135);
x_156 = lean_ctor_get(x_136, 1);
lean_inc(x_156);
lean_dec(x_136);
x_157 = lean_box(1);
x_158 = l_Lake_OutStream_get(x_157, x_155);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = 2;
lean_inc(x_159);
x_162 = l_Lake_AnsiMode_isEnabled(x_159, x_161, x_160);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__3___boxed), 4, 2);
lean_closure_set(x_165, 0, x_159);
lean_closure_set(x_165, 1, x_163);
x_166 = l_Lake_MainM_runLogIO_replay(x_156, x_165, x_164);
lean_dec(x_156);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_166, 0);
lean_dec(x_168);
x_169 = l_Lake_setupFile___lambda__4___boxed__const__1;
lean_ctor_set_tag(x_166, 1);
lean_ctor_set(x_166, 0, x_169);
x_9 = x_166;
goto block_132;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_166, 1);
lean_inc(x_170);
lean_dec(x_166);
x_171 = l_Lake_setupFile___lambda__4___boxed__const__1;
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_171);
lean_ctor_set(x_172, 1, x_170);
x_9 = x_172;
goto block_132;
}
}
block_132:
{
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_60; lean_object* x_61; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_109; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_97 = l_Lake_setupFile___lambda__4___closed__1;
x_98 = l_List_foldl___at_Lake_setupFile___spec__3(x_10, x_97, x_3);
lean_inc(x_2);
x_99 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_99, 0, x_2);
lean_closure_set(x_99, 1, x_98);
lean_inc(x_10);
x_109 = l_Lake_Workspace_runFetchM___rarg(x_10, x_99, x_1, x_11);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_io_wait(x_112, x_111);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_ctor_get(x_114, 1);
lean_dec(x_117);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
lean_dec(x_113);
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
lean_dec(x_116);
lean_ctor_set(x_114, 1, x_97);
lean_ctor_set(x_114, 0, x_119);
x_60 = x_114;
x_61 = x_118;
goto block_96;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_114, 0);
lean_inc(x_120);
lean_dec(x_114);
x_121 = lean_ctor_get(x_113, 1);
lean_inc(x_121);
lean_dec(x_113);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_97);
x_60 = x_123;
x_61 = x_121;
goto block_96;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_114);
x_124 = lean_ctor_get(x_113, 1);
lean_inc(x_124);
lean_dec(x_113);
x_125 = l_Lake_setupFile___lambda__4___closed__4;
x_100 = x_125;
x_101 = x_124;
goto block_108;
}
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_109, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_109, 1);
lean_inc(x_127);
lean_dec(x_109);
x_100 = x_126;
x_101 = x_127;
goto block_108;
}
block_59:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lake_Workspace_leanPath(x_10);
x_16 = l_Lake_Workspace_leanSrcPath(x_10);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_13);
x_18 = l_Lean_searchModuleNameOfFileName(x_2, x_16, x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
x_22 = l_Lake_setupFile___lambda__1(x_17, x_21, x_20);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = l_Lake_Workspace_findModule_x3f(x_24, x_10);
lean_dec(x_10);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = l_Lake_setupFile___lambda__1(x_17, x_26, x_23);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 4);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Array_append___rarg(x_33, x_34);
lean_dec(x_34);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = l_Array_append___rarg(x_35, x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 4);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Array_append___rarg(x_39, x_40);
lean_dec(x_40);
x_42 = lean_array_size(x_41);
x_43 = 0;
x_44 = l_Array_mapMUnsafe_map___at_Lake_setupFile___spec__1(x_42, x_43, x_41);
x_45 = lean_box(0);
x_46 = lean_array_get_size(x_44);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_lt(x_47, x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_44);
x_49 = l_Lake_setupFile___lambda__1(x_17, x_45, x_23);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_46, x_46);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_46);
lean_dec(x_44);
x_51 = l_Lake_setupFile___lambda__1(x_17, x_45, x_23);
return x_51;
}
else
{
size_t x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_53 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_44, x_43, x_52, x_45);
lean_dec(x_44);
x_54 = l_Lake_setupFile___lambda__1(x_17, x_53, x_23);
return x_54;
}
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_10);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_12);
if (x_55 == 0)
{
return x_12;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_12, 0);
x_57 = lean_ctor_get(x_12, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_12);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
block_96:
{
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_box(1);
x_65 = l_Lake_OutStream_get(x_64, x_61);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = 2;
lean_inc(x_66);
x_69 = l_Lake_AnsiMode_isEnabled(x_66, x_68, x_67);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_box(x_8);
x_73 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__2___boxed), 5, 3);
lean_closure_set(x_73, 0, x_66);
lean_closure_set(x_73, 1, x_72);
lean_closure_set(x_73, 2, x_70);
x_74 = l_Lake_MainM_runLogIO_replay(x_63, x_73, x_71);
lean_dec(x_63);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_62);
x_12 = x_74;
goto block_59;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_62);
lean_ctor_set(x_78, 1, x_77);
x_12 = x_78;
goto block_59;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
lean_dec(x_60);
x_80 = lean_box(1);
x_81 = l_Lake_OutStream_get(x_80, x_61);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = 2;
lean_inc(x_82);
x_85 = l_Lake_AnsiMode_isEnabled(x_82, x_84, x_83);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__3___boxed), 4, 2);
lean_closure_set(x_88, 0, x_82);
lean_closure_set(x_88, 1, x_86);
x_89 = l_Lake_MainM_runLogIO_replay(x_79, x_88, x_87);
lean_dec(x_79);
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_89, 0);
lean_dec(x_91);
x_92 = l_Lake_setupFile___lambda__4___boxed__const__1;
lean_ctor_set_tag(x_89, 1);
lean_ctor_set(x_89, 0, x_92);
x_12 = x_89;
goto block_59;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 1);
lean_inc(x_93);
lean_dec(x_89);
x_94 = l_Lake_setupFile___lambda__4___boxed__const__1;
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
x_12 = x_95;
goto block_59;
}
}
}
block_108:
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_102 = lean_io_error_to_string(x_100);
x_103 = 3;
x_104 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set_uint8(x_104, sizeof(void*)*1, x_103);
x_105 = lean_array_push(x_97, x_104);
x_106 = l_Lake_setupFile___lambda__4___closed__2;
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
x_60 = x_107;
x_61 = x_101;
goto block_96;
}
}
else
{
uint8_t x_128; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_9);
if (x_128 == 0)
{
return x_9;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_9, 0);
x_130 = lean_ctor_get(x_9, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_9);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
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
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = l_System_FilePath_join(x_6, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 3);
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
x_26 = l_Lake_setupFile___lambda__4(x_4, x_2, x_3, x_1, x_25, x_24);
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lake_setupFile___lambda__2(x_1, x_6, x_7, x_4, x_5);
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
lean_object* x_4; lean_object* x_5; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = 0;
x_190 = l_Lake_setupFile___lambda__4___closed__1;
lean_inc(x_1);
x_191 = l_Lake_loadWorkspace(x_1, x_189, x_190, x_3);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = !lean_is_exclusive(x_192);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_192, 0);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_192, 0, x_196);
x_4 = x_192;
x_5 = x_193;
goto block_188;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_192, 0);
x_198 = lean_ctor_get(x_192, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_192);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_197);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
x_4 = x_200;
x_5 = x_193;
goto block_188;
}
}
else
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_191, 1);
lean_inc(x_201);
lean_dec(x_191);
x_202 = !lean_is_exclusive(x_192);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_192, 0);
lean_dec(x_203);
x_204 = lean_box(0);
lean_ctor_set_tag(x_192, 0);
lean_ctor_set(x_192, 0, x_204);
x_4 = x_192;
x_5 = x_201;
goto block_188;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_192, 1);
lean_inc(x_205);
lean_dec(x_192);
x_206 = lean_box(0);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_205);
x_4 = x_207;
x_5 = x_201;
goto block_188;
}
}
block_188:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_array_get_size(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_lt(x_10, x_9);
if (x_11 == 0)
{
lean_dec(x_9);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lake_serve___closed__1;
x_13 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_12, x_5);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = l_Lake_Env_baseVars(x_15);
x_17 = l_Lake_Log_toString(x_8);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_4, 1, x_18);
lean_ctor_set(x_4, 0, x_19);
x_20 = lean_array_push(x_16, x_4);
x_21 = l_Lake_setupFile___lambda__4___closed__1;
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lake_serve___lambda__1(x_1, x_2, x_22, x_14);
lean_dec(x_22);
lean_dec(x_1);
return x_23;
}
else
{
uint8_t x_24; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_8);
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
lean_dec(x_7);
lean_inc(x_28);
x_29 = l_Lake_Workspace_augmentedEnvVars(x_28);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_30, 2);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 6);
lean_inc(x_32);
lean_dec(x_31);
lean_ctor_set(x_4, 1, x_32);
lean_ctor_set(x_4, 0, x_29);
x_33 = l_Lake_serve___lambda__1(x_1, x_2, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_9, x_9);
if (x_34 == 0)
{
lean_dec(x_9);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Lake_serve___closed__1;
x_36 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_35, x_5);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_1, 0);
lean_inc(x_38);
x_39 = l_Lake_Env_baseVars(x_38);
x_40 = l_Lake_Log_toString(x_8);
lean_dec(x_8);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_4, 1, x_41);
lean_ctor_set(x_4, 0, x_42);
x_43 = lean_array_push(x_39, x_4);
x_44 = l_Lake_setupFile___lambda__4___closed__1;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lake_serve___lambda__1(x_1, x_2, x_45, x_37);
lean_dec(x_45);
lean_dec(x_1);
return x_46;
}
else
{
uint8_t x_47; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_36);
if (x_47 == 0)
{
return x_36;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_36, 0);
x_49 = lean_ctor_get(x_36, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_36);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_8);
x_51 = lean_ctor_get(x_7, 0);
lean_inc(x_51);
lean_dec(x_7);
lean_inc(x_51);
x_52 = l_Lake_Workspace_augmentedEnvVars(x_51);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_54, 6);
lean_inc(x_55);
lean_dec(x_54);
lean_ctor_set(x_4, 1, x_55);
lean_ctor_set(x_4, 0, x_52);
x_56 = l_Lake_serve___lambda__1(x_1, x_2, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_56;
}
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; lean_object* x_60; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_59 = lean_box(0);
x_60 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_8, x_57, x_58, x_59, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_60, 1);
x_63 = lean_ctor_get(x_60, 0);
lean_dec(x_63);
x_64 = l_Lake_serve___closed__1;
x_65 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_64, x_62);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = l_Lake_Env_baseVars(x_67);
x_69 = l_Lake_Log_toString(x_8);
lean_dec(x_8);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_4, 1, x_70);
lean_ctor_set(x_4, 0, x_71);
x_72 = lean_array_push(x_68, x_4);
x_73 = l_Lake_setupFile___lambda__4___closed__1;
lean_ctor_set(x_60, 1, x_73);
lean_ctor_set(x_60, 0, x_72);
x_74 = l_Lake_serve___lambda__1(x_1, x_2, x_60, x_66);
lean_dec(x_60);
lean_dec(x_1);
return x_74;
}
else
{
uint8_t x_75; 
lean_free_object(x_60);
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_65);
if (x_75 == 0)
{
return x_65;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_65, 0);
x_77 = lean_ctor_get(x_65, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_65);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_60, 1);
lean_inc(x_79);
lean_dec(x_60);
x_80 = l_Lake_serve___closed__1;
x_81 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_80, x_79);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
x_84 = l_Lake_Env_baseVars(x_83);
x_85 = l_Lake_Log_toString(x_8);
lean_dec(x_8);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = l_Lake_invalidConfigEnvVar;
lean_ctor_set(x_4, 1, x_86);
lean_ctor_set(x_4, 0, x_87);
x_88 = lean_array_push(x_84, x_4);
x_89 = l_Lake_setupFile___lambda__4___closed__1;
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lake_serve___lambda__1(x_1, x_2, x_90, x_82);
lean_dec(x_90);
lean_dec(x_1);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_1);
x_92 = lean_ctor_get(x_81, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_81, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_94 = x_81;
} else {
 lean_dec_ref(x_81);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_8);
x_96 = lean_ctor_get(x_60, 1);
lean_inc(x_96);
lean_dec(x_60);
x_97 = lean_ctor_get(x_7, 0);
lean_inc(x_97);
lean_dec(x_7);
lean_inc(x_97);
x_98 = l_Lake_Workspace_augmentedEnvVars(x_97);
x_99 = lean_ctor_get(x_97, 0);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_ctor_get(x_99, 2);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_100, 6);
lean_inc(x_101);
lean_dec(x_100);
lean_ctor_set(x_4, 1, x_101);
lean_ctor_set(x_4, 0, x_98);
x_102 = l_Lake_serve___lambda__1(x_1, x_2, x_4, x_96);
lean_dec(x_4);
lean_dec(x_1);
return x_102;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_103 = lean_ctor_get(x_4, 0);
x_104 = lean_ctor_get(x_4, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_4);
x_105 = lean_array_get_size(x_104);
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_nat_dec_lt(x_106, x_105);
if (x_107 == 0)
{
lean_dec(x_105);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Lake_serve___closed__1;
x_109 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_108, x_5);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = l_Lake_Env_baseVars(x_111);
x_113 = l_Lake_Log_toString(x_104);
lean_dec(x_104);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Lake_invalidConfigEnvVar;
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
x_117 = lean_array_push(x_112, x_116);
x_118 = l_Lake_setupFile___lambda__4___closed__1;
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = l_Lake_serve___lambda__1(x_1, x_2, x_119, x_110);
lean_dec(x_119);
lean_dec(x_1);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_104);
lean_dec(x_1);
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
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_104);
x_125 = lean_ctor_get(x_103, 0);
lean_inc(x_125);
lean_dec(x_103);
lean_inc(x_125);
x_126 = l_Lake_Workspace_augmentedEnvVars(x_125);
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_127, 2);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_ctor_get(x_128, 6);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Lake_serve___lambda__1(x_1, x_2, x_130, x_5);
lean_dec(x_130);
lean_dec(x_1);
return x_131;
}
}
else
{
uint8_t x_132; 
x_132 = lean_nat_dec_le(x_105, x_105);
if (x_132 == 0)
{
lean_dec(x_105);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_133; lean_object* x_134; 
x_133 = l_Lake_serve___closed__1;
x_134 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_133, x_5);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = lean_ctor_get(x_1, 0);
lean_inc(x_136);
x_137 = l_Lake_Env_baseVars(x_136);
x_138 = l_Lake_Log_toString(x_104);
lean_dec(x_104);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = l_Lake_invalidConfigEnvVar;
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
x_142 = lean_array_push(x_137, x_141);
x_143 = l_Lake_setupFile___lambda__4___closed__1;
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = l_Lake_serve___lambda__1(x_1, x_2, x_144, x_135);
lean_dec(x_144);
lean_dec(x_1);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_104);
lean_dec(x_1);
x_146 = lean_ctor_get(x_134, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_134, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_148 = x_134;
} else {
 lean_dec_ref(x_134);
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
lean_dec(x_104);
x_150 = lean_ctor_get(x_103, 0);
lean_inc(x_150);
lean_dec(x_103);
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
x_156 = l_Lake_serve___lambda__1(x_1, x_2, x_155, x_5);
lean_dec(x_155);
lean_dec(x_1);
return x_156;
}
}
else
{
size_t x_157; size_t x_158; lean_object* x_159; lean_object* x_160; 
x_157 = 0;
x_158 = lean_usize_of_nat(x_105);
lean_dec(x_105);
x_159 = lean_box(0);
x_160 = l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(x_104, x_157, x_158, x_159, x_5);
if (lean_obj_tag(x_103) == 0)
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
x_168 = l_Lake_Log_toString(x_104);
lean_dec(x_104);
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
lean_dec(x_104);
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
lean_dec(x_104);
x_180 = lean_ctor_get(x_160, 1);
lean_inc(x_180);
lean_dec(x_160);
x_181 = lean_ctor_get(x_103, 0);
lean_inc(x_181);
lean_dec(x_103);
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
l_Lake_setupFile___lambda__1___boxed__const__1 = _init_l_Lake_setupFile___lambda__1___boxed__const__1();
lean_mark_persistent(l_Lake_setupFile___lambda__1___boxed__const__1);
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
