// Lean compiler output
// Module: Lake.CLI.Serve
// Imports: Lake.Load Lake.Build Lake.Util.MainM Lean.Util.FileSetupInfo
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
static lean_object* l_Lake_setupFile___closed__5;
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(lean_object*);
lean_object* l_Lake_Workspace_findModuleBySrc_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_instOrdBuildType;
lean_object* l_Lake_AnsiMode_isEnabled(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lake_Log_toString(lean_object*);
static lean_object* l_Lake_setupFile___closed__4;
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanSrcPath(lean_object*);
lean_object* lean_io_getenv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanSrcPath(lean_object*);
extern lean_object* l_Lake_Module_depsFacet;
lean_object* l_Lake_Env_baseVars(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lake_OutStream_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_serve(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT uint32_t l_Lake_noConfigFileCode;
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* lean_io_process_child_wait(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Workspace_augmentedEnvVars(lean_object*);
static lean_object* l_Lake_setupFile___closed__3;
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_resolvePath(lean_object*, lean_object*);
static lean_object* l_Lake_serve___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_serve___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__2;
lean_object* l_Lake_BuildInfo_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_logToStream(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_invalidConfigEnvVar;
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
lean_object* l_Lake_loadWorkspace(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_process_spawn(lean_object*, lean_object*);
lean_object* l_Lake_Workspace_leanPath(lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__2;
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_OutStream_logEntry(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lake_BuildType_leanOptions(uint8_t);
static lean_object* l_Lake_serve___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLe___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_buildImportsAndDeps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lake_serve___lambda__1___closed__4;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lake_setupFile___closed__2;
lean_object* l_IO_println___at_Lean_Environment_displayStats___spec__3(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setupFile___boxed__const__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lake_invalidConfigEnvVar___closed__1;
lean_object* l_String_toName(lean_object*);
lean_object* l_Lake_Workspace_runFetchM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_LoggerIO_captureLog___rarg(lean_object*, lean_object*);
lean_object* l_Lake_Env_leanPath(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Lake_setupFile___closed__1;
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lake_Module_keyword;
static lean_object* l_Lake_setupFile___closed__6;
lean_object* lean_io_wait(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_IO_eprint___at_IO_eprintln___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lake_serve___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lake_realConfigFile(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_3 = l_Lake_Workspace_leanPath(x_1);
x_4 = l_Lake_Workspace_leanSrcPath(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_array_size(x_5);
x_7 = 0;
x_8 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(x_6, x_7, x_5);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_array_size(x_9);
x_11 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(x_10, x_7, x_9);
x_12 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_4);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lake_setupFile___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_logToStream(x_4, x_1, x_2, x_3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_setupFile___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to load workspace", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 3;
x_2 = l_Lake_setupFile___closed__1;
x_3 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_setupFile___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("build failed", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_setupFile___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_setupFile___closed__4;
x_2 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_setupFile___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to configure the Lake workspace. Please restart the server after fixing the error above.", 95, 95);
return x_1;
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
x_1 = l_Lake_noConfigFileCode;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_setupFile(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_22; uint8_t x_23; 
x_22 = l_Lake_resolvePath(x_2, x_5);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_277; lean_object* x_278; uint8_t x_279; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_277 = lean_ctor_get(x_1, 6);
lean_inc(x_277);
x_278 = l_Lake_realConfigFile(x_277, x_25);
x_279 = !lean_is_exclusive(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_280 = lean_ctor_get(x_278, 0);
x_281 = lean_ctor_get(x_278, 1);
x_282 = lean_string_utf8_byte_size(x_280);
x_283 = lean_unsigned_to_nat(0u);
x_284 = lean_nat_dec_eq(x_282, x_283);
lean_dec(x_282);
if (x_284 == 0)
{
uint8_t x_285; 
lean_free_object(x_278);
x_285 = lean_string_dec_eq(x_280, x_24);
lean_dec(x_280);
if (x_285 == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_free_object(x_22);
x_286 = l_Lake_invalidConfigEnvVar;
x_287 = lean_io_getenv(x_286, x_281);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; uint8_t x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_291 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
x_292 = lean_box(1);
x_293 = l_Lake_OutStream_get(x_292, x_289);
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
lean_inc(x_294);
x_296 = l_Lake_AnsiMode_isEnabled(x_294, x_291, x_295);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_box(x_290);
x_300 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__1___boxed), 5, 3);
lean_closure_set(x_300, 0, x_294);
lean_closure_set(x_300, 1, x_299);
lean_closure_set(x_300, 2, x_297);
x_301 = l_Lake_loadWorkspace(x_1, x_300, x_298);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_302);
x_26 = x_304;
x_27 = x_303;
goto block_276;
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_301, 1);
lean_inc(x_305);
lean_dec(x_301);
x_306 = lean_box(0);
x_26 = x_306;
x_27 = x_305;
goto block_276;
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_307 = lean_ctor_get(x_287, 1);
lean_inc(x_307);
lean_dec(x_287);
x_308 = lean_ctor_get(x_288, 0);
lean_inc(x_308);
lean_dec(x_288);
x_309 = l_IO_eprint___at_IO_eprintln___spec__1(x_308, x_307);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec(x_309);
x_311 = l_Lake_setupFile___closed__6;
x_312 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_311, x_310);
if (lean_obj_tag(x_312) == 0)
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_312, 0);
lean_dec(x_314);
x_315 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_312, 1);
lean_ctor_set(x_312, 0, x_315);
return x_312;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_312, 1);
lean_inc(x_316);
lean_dec(x_312);
x_317 = l_Lake_setupFile___boxed__const__1;
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_317);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; uint8_t x_322; lean_object* x_323; lean_object* x_324; uint8_t x_325; uint8_t x_326; lean_object* x_327; uint8_t x_328; 
x_319 = lean_ctor_get(x_312, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_312, 1);
lean_inc(x_320);
lean_dec(x_312);
x_321 = lean_io_error_to_string(x_319);
x_322 = 3;
x_323 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*1, x_322);
x_324 = lean_box(1);
x_325 = 1;
x_326 = 0;
x_327 = l_Lake_OutStream_logEntry(x_324, x_323, x_325, x_326, x_320);
lean_dec(x_323);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_327, 0);
lean_dec(x_329);
x_330 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_327, 1);
lean_ctor_set(x_327, 0, x_330);
return x_327;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_327, 1);
lean_inc(x_331);
lean_dec(x_327);
x_332 = l_Lake_setupFile___boxed__const__1;
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; uint8_t x_341; lean_object* x_342; uint8_t x_343; 
x_334 = lean_ctor_get(x_309, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_309, 1);
lean_inc(x_335);
lean_dec(x_309);
x_336 = lean_io_error_to_string(x_334);
x_337 = 3;
x_338 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set_uint8(x_338, sizeof(void*)*1, x_337);
x_339 = lean_box(1);
x_340 = 1;
x_341 = 0;
x_342 = l_Lake_OutStream_logEntry(x_339, x_338, x_340, x_341, x_335);
lean_dec(x_338);
x_343 = !lean_is_exclusive(x_342);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; 
x_344 = lean_ctor_get(x_342, 0);
lean_dec(x_344);
x_345 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_342, 1);
lean_ctor_set(x_342, 0, x_345);
return x_342;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_342, 1);
lean_inc(x_346);
lean_dec(x_342);
x_347 = l_Lake_setupFile___boxed__const__1;
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_347);
lean_ctor_set(x_348, 1, x_346);
return x_348;
}
}
}
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_349 = lean_ctor_get(x_1, 0);
lean_inc(x_349);
lean_dec(x_1);
x_350 = l_Lake_Env_leanPath(x_349);
x_351 = l_Lake_Env_leanSrcPath(x_349);
x_352 = lean_box(0);
x_353 = lean_ctor_get(x_349, 0);
lean_inc(x_353);
lean_dec(x_349);
x_354 = lean_ctor_get(x_353, 4);
lean_inc(x_354);
lean_dec(x_353);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_352);
lean_ctor_set(x_22, 0, x_354);
x_355 = lean_array_mk(x_22);
x_356 = l_Lake_setupFile___closed__3;
x_357 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_357, 0, x_350);
lean_ctor_set(x_357, 1, x_351);
lean_ctor_set(x_357, 2, x_356);
lean_ctor_set(x_357, 3, x_355);
x_358 = lean_box(0);
x_359 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
x_360 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_359);
x_361 = l_Lean_Json_compress(x_360);
x_362 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_361, x_281);
if (lean_obj_tag(x_362) == 0)
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_362);
if (x_363 == 0)
{
return x_362;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_362, 0);
x_365 = lean_ctor_get(x_362, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_362);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; uint8_t x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; uint8_t x_374; lean_object* x_375; uint8_t x_376; 
x_367 = lean_ctor_get(x_362, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_362, 1);
lean_inc(x_368);
lean_dec(x_362);
x_369 = lean_io_error_to_string(x_367);
x_370 = 3;
x_371 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_371, 0, x_369);
lean_ctor_set_uint8(x_371, sizeof(void*)*1, x_370);
x_372 = lean_box(1);
x_373 = 1;
x_374 = 0;
x_375 = l_Lake_OutStream_logEntry(x_372, x_371, x_373, x_374, x_368);
lean_dec(x_371);
x_376 = !lean_is_exclusive(x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_375, 0);
lean_dec(x_377);
x_378 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_375, 1);
lean_ctor_set(x_375, 0, x_378);
return x_375;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_375, 1);
lean_inc(x_379);
lean_dec(x_375);
x_380 = l_Lake_setupFile___boxed__const__1;
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_380);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
}
}
else
{
lean_object* x_382; 
lean_dec(x_280);
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_382 = l_Lake_setupFile___boxed__const__2;
lean_ctor_set_tag(x_278, 1);
lean_ctor_set(x_278, 0, x_382);
return x_278;
}
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_383 = lean_ctor_get(x_278, 0);
x_384 = lean_ctor_get(x_278, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_278);
x_385 = lean_string_utf8_byte_size(x_383);
x_386 = lean_unsigned_to_nat(0u);
x_387 = lean_nat_dec_eq(x_385, x_386);
lean_dec(x_385);
if (x_387 == 0)
{
uint8_t x_388; 
x_388 = lean_string_dec_eq(x_383, x_24);
lean_dec(x_383);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_free_object(x_22);
x_389 = l_Lake_invalidConfigEnvVar;
x_390 = lean_io_getenv(x_389, x_384);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; uint8_t x_393; uint8_t x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
lean_dec(x_390);
x_393 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_394 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
x_395 = lean_box(1);
x_396 = l_Lake_OutStream_get(x_395, x_392);
x_397 = lean_ctor_get(x_396, 0);
lean_inc(x_397);
x_398 = lean_ctor_get(x_396, 1);
lean_inc(x_398);
lean_dec(x_396);
lean_inc(x_397);
x_399 = l_Lake_AnsiMode_isEnabled(x_397, x_394, x_398);
x_400 = lean_ctor_get(x_399, 0);
lean_inc(x_400);
x_401 = lean_ctor_get(x_399, 1);
lean_inc(x_401);
lean_dec(x_399);
x_402 = lean_box(x_393);
x_403 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__1___boxed), 5, 3);
lean_closure_set(x_403, 0, x_397);
lean_closure_set(x_403, 1, x_402);
lean_closure_set(x_403, 2, x_400);
x_404 = l_Lake_loadWorkspace(x_1, x_403, x_401);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
x_407 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_407, 0, x_405);
x_26 = x_407;
x_27 = x_406;
goto block_276;
}
else
{
lean_object* x_408; lean_object* x_409; 
x_408 = lean_ctor_get(x_404, 1);
lean_inc(x_408);
lean_dec(x_404);
x_409 = lean_box(0);
x_26 = x_409;
x_27 = x_408;
goto block_276;
}
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_410 = lean_ctor_get(x_390, 1);
lean_inc(x_410);
lean_dec(x_390);
x_411 = lean_ctor_get(x_391, 0);
lean_inc(x_411);
lean_dec(x_391);
x_412 = l_IO_eprint___at_IO_eprintln___spec__1(x_411, x_410);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
lean_dec(x_412);
x_414 = l_Lake_setupFile___closed__6;
x_415 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_414, x_413);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; 
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 x_417 = x_415;
} else {
 lean_dec_ref(x_415);
 x_417 = lean_box(0);
}
x_418 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_417)) {
 x_419 = lean_alloc_ctor(1, 2, 0);
} else {
 x_419 = x_417;
 lean_ctor_set_tag(x_419, 1);
}
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_416);
return x_419;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; uint8_t x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_420 = lean_ctor_get(x_415, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_415, 1);
lean_inc(x_421);
lean_dec(x_415);
x_422 = lean_io_error_to_string(x_420);
x_423 = 3;
x_424 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set_uint8(x_424, sizeof(void*)*1, x_423);
x_425 = lean_box(1);
x_426 = 1;
x_427 = 0;
x_428 = l_Lake_OutStream_logEntry(x_425, x_424, x_426, x_427, x_421);
lean_dec(x_424);
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 x_430 = x_428;
} else {
 lean_dec_ref(x_428);
 x_430 = lean_box(0);
}
x_431 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_430)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_430;
 lean_ctor_set_tag(x_432, 1);
}
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_429);
return x_432;
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_433 = lean_ctor_get(x_412, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_412, 1);
lean_inc(x_434);
lean_dec(x_412);
x_435 = lean_io_error_to_string(x_433);
x_436 = 3;
x_437 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set_uint8(x_437, sizeof(void*)*1, x_436);
x_438 = lean_box(1);
x_439 = 1;
x_440 = 0;
x_441 = l_Lake_OutStream_logEntry(x_438, x_437, x_439, x_440, x_434);
lean_dec(x_437);
x_442 = lean_ctor_get(x_441, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_443 = x_441;
} else {
 lean_dec_ref(x_441);
 x_443 = lean_box(0);
}
x_444 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_443)) {
 x_445 = lean_alloc_ctor(1, 2, 0);
} else {
 x_445 = x_443;
 lean_ctor_set_tag(x_445, 1);
}
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_442);
return x_445;
}
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_446 = lean_ctor_get(x_1, 0);
lean_inc(x_446);
lean_dec(x_1);
x_447 = l_Lake_Env_leanPath(x_446);
x_448 = l_Lake_Env_leanSrcPath(x_446);
x_449 = lean_box(0);
x_450 = lean_ctor_get(x_446, 0);
lean_inc(x_450);
lean_dec(x_446);
x_451 = lean_ctor_get(x_450, 4);
lean_inc(x_451);
lean_dec(x_450);
lean_ctor_set_tag(x_22, 1);
lean_ctor_set(x_22, 1, x_449);
lean_ctor_set(x_22, 0, x_451);
x_452 = lean_array_mk(x_22);
x_453 = l_Lake_setupFile___closed__3;
x_454 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_454, 0, x_447);
lean_ctor_set(x_454, 1, x_448);
lean_ctor_set(x_454, 2, x_453);
lean_ctor_set(x_454, 3, x_452);
x_455 = lean_box(0);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_454);
lean_ctor_set(x_456, 1, x_455);
x_457 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_456);
x_458 = l_Lean_Json_compress(x_457);
x_459 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_458, x_384);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_462 = x_459;
} else {
 lean_dec_ref(x_459);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(0, 2, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_460);
lean_ctor_set(x_463, 1, x_461);
return x_463;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; uint8_t x_470; uint8_t x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_464 = lean_ctor_get(x_459, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_459, 1);
lean_inc(x_465);
lean_dec(x_459);
x_466 = lean_io_error_to_string(x_464);
x_467 = 3;
x_468 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set_uint8(x_468, sizeof(void*)*1, x_467);
x_469 = lean_box(1);
x_470 = 1;
x_471 = 0;
x_472 = l_Lake_OutStream_logEntry(x_469, x_468, x_470, x_471, x_465);
lean_dec(x_468);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_474 = x_472;
} else {
 lean_dec_ref(x_472);
 x_474 = lean_box(0);
}
x_475 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_474)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_474;
 lean_ctor_set_tag(x_476, 1);
}
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_473);
return x_476;
}
}
}
else
{
lean_object* x_477; lean_object* x_478; 
lean_dec(x_383);
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_477 = l_Lake_setupFile___boxed__const__2;
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_384);
return x_478;
}
}
block_276:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; 
lean_dec(x_24);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_box(1);
x_29 = l_Lake_setupFile___closed__2;
x_30 = 1;
x_31 = 0;
x_32 = l_Lake_OutStream_logEntry(x_28, x_29, x_30, x_31, x_27);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = l_Lake_setupFile___boxed__const__1;
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
x_37 = l_Lake_setupFile___boxed__const__1;
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_26, 0);
lean_inc(x_39);
lean_dec(x_26);
lean_inc(x_24);
x_40 = l_Lake_Workspace_findModuleBySrc_x3f(x_24, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l_Lake_setupFile___closed__3;
x_42 = l_List_foldl___at_Lake_setupFile___spec__1(x_39, x_41, x_3);
x_43 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_43, 0, x_24);
lean_closure_set(x_43, 1, x_42);
lean_inc(x_39);
x_44 = l_Lake_Workspace_runFetchM___rarg(x_39, x_43, x_4, x_27);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_io_wait(x_47, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = !lean_is_exclusive(x_49);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_49, 0);
x_53 = lean_ctor_get(x_49, 1);
lean_dec(x_53);
x_54 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_52);
lean_dec(x_39);
x_55 = lean_box(0);
lean_ctor_set(x_49, 1, x_55);
lean_ctor_set(x_49, 0, x_54);
x_56 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_49);
x_57 = l_Lean_Json_compress(x_56);
x_58 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_57, x_50);
if (lean_obj_tag(x_58) == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
return x_58;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_58);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; 
x_63 = lean_ctor_get(x_58, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 1);
lean_inc(x_64);
lean_dec(x_58);
x_65 = lean_io_error_to_string(x_63);
x_66 = 3;
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
x_68 = lean_box(1);
x_69 = 1;
x_70 = 0;
x_71 = l_Lake_OutStream_logEntry(x_68, x_67, x_69, x_70, x_64);
lean_dec(x_67);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
lean_dec(x_73);
x_74 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = l_Lake_setupFile___boxed__const__1;
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_49, 0);
lean_inc(x_78);
lean_dec(x_49);
x_79 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_78);
lean_dec(x_39);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_81);
x_83 = l_Lean_Json_compress(x_82);
x_84 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_83, x_50);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_inc(x_90);
lean_dec(x_84);
x_91 = lean_io_error_to_string(x_89);
x_92 = 3;
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_92);
x_94 = lean_box(1);
x_95 = 1;
x_96 = 0;
x_97 = l_Lake_OutStream_logEntry(x_94, x_93, x_95, x_96, x_90);
lean_dec(x_93);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_99)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_99;
 lean_ctor_set_tag(x_101, 1);
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_98);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_49);
lean_dec(x_39);
x_102 = lean_ctor_get(x_48, 1);
lean_inc(x_102);
lean_dec(x_48);
x_103 = l_Lake_setupFile___closed__5;
x_6 = x_103;
x_7 = x_102;
goto block_21;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_39);
x_104 = lean_ctor_get(x_44, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_44, 1);
lean_inc(x_105);
lean_dec(x_44);
x_6 = x_104;
x_7 = x_105;
goto block_21;
}
}
else
{
uint8_t x_106; 
lean_dec(x_24);
lean_dec(x_3);
x_106 = !lean_is_exclusive(x_40);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_40, 0);
x_108 = lean_ctor_get(x_107, 2);
lean_inc(x_108);
lean_ctor_set_tag(x_40, 0);
lean_ctor_set(x_40, 0, x_108);
x_109 = l_Lake_Module_keyword;
x_110 = l_Lake_Module_depsFacet;
lean_inc(x_107);
x_111 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_111, 0, x_40);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_111, 2, x_107);
lean_ctor_set(x_111, 3, x_110);
x_112 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_112, 0, x_111);
lean_closure_set(x_112, 1, lean_box(0));
lean_inc(x_39);
x_113 = l_Lake_Workspace_runFetchM___rarg(x_39, x_112, x_4, x_27);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_io_wait(x_116, x_115);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_121 = x_118;
} else {
 lean_dec_ref(x_118);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
x_123 = lean_ctor_get(x_107, 0);
lean_inc(x_123);
lean_dec(x_107);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 3);
lean_inc(x_125);
lean_dec(x_124);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_ctor_get_uint8(x_126, sizeof(void*)*13);
x_128 = lean_ctor_get(x_123, 2);
lean_inc(x_128);
lean_dec(x_123);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get_uint8(x_129, sizeof(void*)*13);
x_131 = l_Lake_instOrdBuildType;
x_132 = lean_box(x_127);
x_133 = lean_box(x_130);
x_134 = l_Ord_instDecidableRelLe___rarg(x_131, x_132, x_133);
x_135 = lean_ctor_get(x_126, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_126, 4);
lean_inc(x_136);
lean_dec(x_126);
x_137 = l_Array_append___rarg(x_135, x_136);
lean_dec(x_136);
x_138 = lean_ctor_get(x_129, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_129, 4);
lean_inc(x_139);
lean_dec(x_129);
x_140 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_120);
lean_dec(x_39);
if (x_134 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_166 = l_Lake_BuildType_leanOptions(x_130);
x_167 = l_Array_append___rarg(x_166, x_137);
lean_dec(x_137);
x_168 = l_Array_append___rarg(x_167, x_138);
lean_dec(x_138);
x_169 = l_Array_append___rarg(x_168, x_139);
lean_dec(x_139);
x_170 = lean_array_get_size(x_169);
x_171 = lean_unsigned_to_nat(0u);
x_172 = lean_nat_dec_lt(x_171, x_170);
if (x_172 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
x_141 = x_122;
goto block_165;
}
else
{
uint8_t x_173; 
x_173 = lean_nat_dec_le(x_170, x_170);
if (x_173 == 0)
{
lean_dec(x_170);
lean_dec(x_169);
x_141 = x_122;
goto block_165;
}
else
{
size_t x_174; size_t x_175; lean_object* x_176; 
x_174 = 0;
x_175 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_176 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_169, x_174, x_175, x_122);
lean_dec(x_169);
x_141 = x_176;
goto block_165;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_177 = l_Lake_BuildType_leanOptions(x_127);
x_178 = l_Array_append___rarg(x_177, x_137);
lean_dec(x_137);
x_179 = l_Array_append___rarg(x_178, x_138);
lean_dec(x_138);
x_180 = l_Array_append___rarg(x_179, x_139);
lean_dec(x_139);
x_181 = lean_array_get_size(x_180);
x_182 = lean_unsigned_to_nat(0u);
x_183 = lean_nat_dec_lt(x_182, x_181);
if (x_183 == 0)
{
lean_dec(x_181);
lean_dec(x_180);
x_141 = x_122;
goto block_165;
}
else
{
uint8_t x_184; 
x_184 = lean_nat_dec_le(x_181, x_181);
if (x_184 == 0)
{
lean_dec(x_181);
lean_dec(x_180);
x_141 = x_122;
goto block_165;
}
else
{
size_t x_185; size_t x_186; lean_object* x_187; 
x_185 = 0;
x_186 = lean_usize_of_nat(x_181);
lean_dec(x_181);
x_187 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_180, x_185, x_186, x_122);
lean_dec(x_180);
x_141 = x_187;
goto block_165;
}
}
}
block_165:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
if (lean_is_scalar(x_121)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_121;
}
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_142);
x_144 = l_Lean_Json_compress(x_143);
x_145 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_144, x_119);
if (lean_obj_tag(x_145) == 0)
{
uint8_t x_146; 
x_146 = !lean_is_exclusive(x_145);
if (x_146 == 0)
{
return x_145;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_145, 0);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_145);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; uint8_t x_157; lean_object* x_158; uint8_t x_159; 
x_150 = lean_ctor_get(x_145, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 1);
lean_inc(x_151);
lean_dec(x_145);
x_152 = lean_io_error_to_string(x_150);
x_153 = 3;
x_154 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set_uint8(x_154, sizeof(void*)*1, x_153);
x_155 = lean_box(1);
x_156 = 1;
x_157 = 0;
x_158 = l_Lake_OutStream_logEntry(x_155, x_154, x_156, x_157, x_151);
lean_dec(x_154);
x_159 = !lean_is_exclusive(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_158, 0);
lean_dec(x_160);
x_161 = l_Lake_setupFile___boxed__const__1;
lean_ctor_set_tag(x_158, 1);
lean_ctor_set(x_158, 0, x_161);
return x_158;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_158, 1);
lean_inc(x_162);
lean_dec(x_158);
x_163 = l_Lake_setupFile___boxed__const__1;
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_118);
lean_dec(x_107);
lean_dec(x_39);
x_188 = lean_ctor_get(x_117, 1);
lean_inc(x_188);
lean_dec(x_117);
x_189 = l_Lake_setupFile___closed__5;
x_6 = x_189;
x_7 = x_188;
goto block_21;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_107);
lean_dec(x_39);
x_190 = lean_ctor_get(x_113, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_113, 1);
lean_inc(x_191);
lean_dec(x_113);
x_6 = x_190;
x_7 = x_191;
goto block_21;
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_192 = lean_ctor_get(x_40, 0);
lean_inc(x_192);
lean_dec(x_40);
x_193 = lean_ctor_get(x_192, 2);
lean_inc(x_193);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Lake_Module_keyword;
x_196 = l_Lake_Module_depsFacet;
lean_inc(x_192);
x_197 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
lean_ctor_set(x_197, 2, x_192);
lean_ctor_set(x_197, 3, x_196);
x_198 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_198, 0, x_197);
lean_closure_set(x_198, 1, lean_box(0));
lean_inc(x_39);
x_199 = l_Lake_Workspace_runFetchM___rarg(x_39, x_198, x_4, x_27);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_ctor_get(x_200, 0);
lean_inc(x_202);
lean_dec(x_200);
x_203 = lean_io_wait(x_202, x_201);
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; uint8_t x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_box(0);
x_209 = lean_ctor_get(x_192, 0);
lean_inc(x_209);
lean_dec(x_192);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_210, 3);
lean_inc(x_211);
lean_dec(x_210);
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
lean_dec(x_211);
x_213 = lean_ctor_get_uint8(x_212, sizeof(void*)*13);
x_214 = lean_ctor_get(x_209, 2);
lean_inc(x_214);
lean_dec(x_209);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
lean_dec(x_214);
x_216 = lean_ctor_get_uint8(x_215, sizeof(void*)*13);
x_217 = l_Lake_instOrdBuildType;
x_218 = lean_box(x_213);
x_219 = lean_box(x_216);
x_220 = l_Ord_instDecidableRelLe___rarg(x_217, x_218, x_219);
x_221 = lean_ctor_get(x_212, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_212, 4);
lean_inc(x_222);
lean_dec(x_212);
x_223 = l_Array_append___rarg(x_221, x_222);
lean_dec(x_222);
x_224 = lean_ctor_get(x_215, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_215, 4);
lean_inc(x_225);
lean_dec(x_215);
x_226 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_39, x_206);
lean_dec(x_39);
if (x_220 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_250 = l_Lake_BuildType_leanOptions(x_216);
x_251 = l_Array_append___rarg(x_250, x_223);
lean_dec(x_223);
x_252 = l_Array_append___rarg(x_251, x_224);
lean_dec(x_224);
x_253 = l_Array_append___rarg(x_252, x_225);
lean_dec(x_225);
x_254 = lean_array_get_size(x_253);
x_255 = lean_unsigned_to_nat(0u);
x_256 = lean_nat_dec_lt(x_255, x_254);
if (x_256 == 0)
{
lean_dec(x_254);
lean_dec(x_253);
x_227 = x_208;
goto block_249;
}
else
{
uint8_t x_257; 
x_257 = lean_nat_dec_le(x_254, x_254);
if (x_257 == 0)
{
lean_dec(x_254);
lean_dec(x_253);
x_227 = x_208;
goto block_249;
}
else
{
size_t x_258; size_t x_259; lean_object* x_260; 
x_258 = 0;
x_259 = lean_usize_of_nat(x_254);
lean_dec(x_254);
x_260 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_253, x_258, x_259, x_208);
lean_dec(x_253);
x_227 = x_260;
goto block_249;
}
}
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_261 = l_Lake_BuildType_leanOptions(x_213);
x_262 = l_Array_append___rarg(x_261, x_223);
lean_dec(x_223);
x_263 = l_Array_append___rarg(x_262, x_224);
lean_dec(x_224);
x_264 = l_Array_append___rarg(x_263, x_225);
lean_dec(x_225);
x_265 = lean_array_get_size(x_264);
x_266 = lean_unsigned_to_nat(0u);
x_267 = lean_nat_dec_lt(x_266, x_265);
if (x_267 == 0)
{
lean_dec(x_265);
lean_dec(x_264);
x_227 = x_208;
goto block_249;
}
else
{
uint8_t x_268; 
x_268 = lean_nat_dec_le(x_265, x_265);
if (x_268 == 0)
{
lean_dec(x_265);
lean_dec(x_264);
x_227 = x_208;
goto block_249;
}
else
{
size_t x_269; size_t x_270; lean_object* x_271; 
x_269 = 0;
x_270 = lean_usize_of_nat(x_265);
lean_dec(x_265);
x_271 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_264, x_269, x_270, x_208);
lean_dec(x_264);
x_227 = x_271;
goto block_249;
}
}
}
block_249:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
if (lean_is_scalar(x_207)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_207;
}
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
x_229 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_228);
x_230 = l_Lean_Json_compress(x_229);
x_231 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_230, x_205);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_234 = x_231;
} else {
 lean_dec_ref(x_231);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_232);
lean_ctor_set(x_235, 1, x_233);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; uint8_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_236 = lean_ctor_get(x_231, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_231, 1);
lean_inc(x_237);
lean_dec(x_231);
x_238 = lean_io_error_to_string(x_236);
x_239 = 3;
x_240 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set_uint8(x_240, sizeof(void*)*1, x_239);
x_241 = lean_box(1);
x_242 = 1;
x_243 = 0;
x_244 = l_Lake_OutStream_logEntry(x_241, x_240, x_242, x_243, x_237);
lean_dec(x_240);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_246 = x_244;
} else {
 lean_dec_ref(x_244);
 x_246 = lean_box(0);
}
x_247 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_246)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_246;
 lean_ctor_set_tag(x_248, 1);
}
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_245);
return x_248;
}
}
}
else
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_204);
lean_dec(x_192);
lean_dec(x_39);
x_272 = lean_ctor_get(x_203, 1);
lean_inc(x_272);
lean_dec(x_203);
x_273 = l_Lake_setupFile___closed__5;
x_6 = x_273;
x_7 = x_272;
goto block_21;
}
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_192);
lean_dec(x_39);
x_274 = lean_ctor_get(x_199, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_199, 1);
lean_inc(x_275);
lean_dec(x_199);
x_6 = x_274;
x_7 = x_275;
goto block_21;
}
}
}
}
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; 
x_479 = lean_ctor_get(x_22, 0);
x_480 = lean_ctor_get(x_22, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_22);
x_619 = lean_ctor_get(x_1, 6);
lean_inc(x_619);
x_620 = l_Lake_realConfigFile(x_619, x_480);
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_623 = x_620;
} else {
 lean_dec_ref(x_620);
 x_623 = lean_box(0);
}
x_624 = lean_string_utf8_byte_size(x_621);
x_625 = lean_unsigned_to_nat(0u);
x_626 = lean_nat_dec_eq(x_624, x_625);
lean_dec(x_624);
if (x_626 == 0)
{
uint8_t x_627; 
lean_dec(x_623);
x_627 = lean_string_dec_eq(x_621, x_479);
lean_dec(x_621);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = l_Lake_invalidConfigEnvVar;
x_629 = lean_io_getenv(x_628, x_622);
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; uint8_t x_632; uint8_t x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_631 = lean_ctor_get(x_629, 1);
lean_inc(x_631);
lean_dec(x_629);
x_632 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 5);
x_633 = lean_ctor_get_uint8(x_4, sizeof(void*)*1 + 6);
x_634 = lean_box(1);
x_635 = l_Lake_OutStream_get(x_634, x_631);
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
lean_inc(x_636);
x_638 = l_Lake_AnsiMode_isEnabled(x_636, x_633, x_637);
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
x_641 = lean_box(x_632);
x_642 = lean_alloc_closure((void*)(l_Lake_setupFile___lambda__1___boxed), 5, 3);
lean_closure_set(x_642, 0, x_636);
lean_closure_set(x_642, 1, x_641);
lean_closure_set(x_642, 2, x_639);
x_643 = l_Lake_loadWorkspace(x_1, x_642, x_640);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_645);
lean_dec(x_643);
x_646 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_646, 0, x_644);
x_481 = x_646;
x_482 = x_645;
goto block_618;
}
else
{
lean_object* x_647; lean_object* x_648; 
x_647 = lean_ctor_get(x_643, 1);
lean_inc(x_647);
lean_dec(x_643);
x_648 = lean_box(0);
x_481 = x_648;
x_482 = x_647;
goto block_618;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_dec(x_479);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_649 = lean_ctor_get(x_629, 1);
lean_inc(x_649);
lean_dec(x_629);
x_650 = lean_ctor_get(x_630, 0);
lean_inc(x_650);
lean_dec(x_630);
x_651 = l_IO_eprint___at_IO_eprintln___spec__1(x_650, x_649);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; 
x_652 = lean_ctor_get(x_651, 1);
lean_inc(x_652);
lean_dec(x_651);
x_653 = l_Lake_setupFile___closed__6;
x_654 = l_IO_eprintln___at___private_Init_System_IO_0__IO_eprintlnAux___spec__1(x_653, x_652);
if (lean_obj_tag(x_654) == 0)
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_655 = lean_ctor_get(x_654, 1);
lean_inc(x_655);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 x_656 = x_654;
} else {
 lean_dec_ref(x_654);
 x_656 = lean_box(0);
}
x_657 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_656)) {
 x_658 = lean_alloc_ctor(1, 2, 0);
} else {
 x_658 = x_656;
 lean_ctor_set_tag(x_658, 1);
}
lean_ctor_set(x_658, 0, x_657);
lean_ctor_set(x_658, 1, x_655);
return x_658;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; uint8_t x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; uint8_t x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_659 = lean_ctor_get(x_654, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_654, 1);
lean_inc(x_660);
lean_dec(x_654);
x_661 = lean_io_error_to_string(x_659);
x_662 = 3;
x_663 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_663, 0, x_661);
lean_ctor_set_uint8(x_663, sizeof(void*)*1, x_662);
x_664 = lean_box(1);
x_665 = 1;
x_666 = 0;
x_667 = l_Lake_OutStream_logEntry(x_664, x_663, x_665, x_666, x_660);
lean_dec(x_663);
x_668 = lean_ctor_get(x_667, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 lean_ctor_release(x_667, 1);
 x_669 = x_667;
} else {
 lean_dec_ref(x_667);
 x_669 = lean_box(0);
}
x_670 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_669)) {
 x_671 = lean_alloc_ctor(1, 2, 0);
} else {
 x_671 = x_669;
 lean_ctor_set_tag(x_671, 1);
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_668);
return x_671;
}
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; uint8_t x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; uint8_t x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; 
x_672 = lean_ctor_get(x_651, 0);
lean_inc(x_672);
x_673 = lean_ctor_get(x_651, 1);
lean_inc(x_673);
lean_dec(x_651);
x_674 = lean_io_error_to_string(x_672);
x_675 = 3;
x_676 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_676, 0, x_674);
lean_ctor_set_uint8(x_676, sizeof(void*)*1, x_675);
x_677 = lean_box(1);
x_678 = 1;
x_679 = 0;
x_680 = l_Lake_OutStream_logEntry(x_677, x_676, x_678, x_679, x_673);
lean_dec(x_676);
x_681 = lean_ctor_get(x_680, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_682 = x_680;
} else {
 lean_dec_ref(x_680);
 x_682 = lean_box(0);
}
x_683 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_682)) {
 x_684 = lean_alloc_ctor(1, 2, 0);
} else {
 x_684 = x_682;
 lean_ctor_set_tag(x_684, 1);
}
lean_ctor_set(x_684, 0, x_683);
lean_ctor_set(x_684, 1, x_681);
return x_684;
}
}
}
else
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec(x_479);
lean_dec(x_4);
lean_dec(x_3);
x_685 = lean_ctor_get(x_1, 0);
lean_inc(x_685);
lean_dec(x_1);
x_686 = l_Lake_Env_leanPath(x_685);
x_687 = l_Lake_Env_leanSrcPath(x_685);
x_688 = lean_box(0);
x_689 = lean_ctor_get(x_685, 0);
lean_inc(x_689);
lean_dec(x_685);
x_690 = lean_ctor_get(x_689, 4);
lean_inc(x_690);
lean_dec(x_689);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_690);
lean_ctor_set(x_691, 1, x_688);
x_692 = lean_array_mk(x_691);
x_693 = l_Lake_setupFile___closed__3;
x_694 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_694, 0, x_686);
lean_ctor_set(x_694, 1, x_687);
lean_ctor_set(x_694, 2, x_693);
lean_ctor_set(x_694, 3, x_692);
x_695 = lean_box(0);
x_696 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
x_697 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_696);
x_698 = l_Lean_Json_compress(x_697);
x_699 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_698, x_622);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_702 = x_699;
} else {
 lean_dec_ref(x_699);
 x_702 = lean_box(0);
}
if (lean_is_scalar(x_702)) {
 x_703 = lean_alloc_ctor(0, 2, 0);
} else {
 x_703 = x_702;
}
lean_ctor_set(x_703, 0, x_700);
lean_ctor_set(x_703, 1, x_701);
return x_703;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; uint8_t x_707; lean_object* x_708; lean_object* x_709; uint8_t x_710; uint8_t x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_704 = lean_ctor_get(x_699, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_699, 1);
lean_inc(x_705);
lean_dec(x_699);
x_706 = lean_io_error_to_string(x_704);
x_707 = 3;
x_708 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_708, 0, x_706);
lean_ctor_set_uint8(x_708, sizeof(void*)*1, x_707);
x_709 = lean_box(1);
x_710 = 1;
x_711 = 0;
x_712 = l_Lake_OutStream_logEntry(x_709, x_708, x_710, x_711, x_705);
lean_dec(x_708);
x_713 = lean_ctor_get(x_712, 1);
lean_inc(x_713);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_714 = x_712;
} else {
 lean_dec_ref(x_712);
 x_714 = lean_box(0);
}
x_715 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_714)) {
 x_716 = lean_alloc_ctor(1, 2, 0);
} else {
 x_716 = x_714;
 lean_ctor_set_tag(x_716, 1);
}
lean_ctor_set(x_716, 0, x_715);
lean_ctor_set(x_716, 1, x_713);
return x_716;
}
}
}
else
{
lean_object* x_717; lean_object* x_718; 
lean_dec(x_621);
lean_dec(x_479);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_717 = l_Lake_setupFile___boxed__const__2;
if (lean_is_scalar(x_623)) {
 x_718 = lean_alloc_ctor(1, 2, 0);
} else {
 x_718 = x_623;
 lean_ctor_set_tag(x_718, 1);
}
lean_ctor_set(x_718, 0, x_717);
lean_ctor_set(x_718, 1, x_622);
return x_718;
}
block_618:
{
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_483; lean_object* x_484; uint8_t x_485; uint8_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
lean_dec(x_479);
lean_dec(x_4);
lean_dec(x_3);
x_483 = lean_box(1);
x_484 = l_Lake_setupFile___closed__2;
x_485 = 1;
x_486 = 0;
x_487 = l_Lake_OutStream_logEntry(x_483, x_484, x_485, x_486, x_482);
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_489 = x_487;
} else {
 lean_dec_ref(x_487);
 x_489 = lean_box(0);
}
x_490 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_489)) {
 x_491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_491 = x_489;
 lean_ctor_set_tag(x_491, 1);
}
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_488);
return x_491;
}
else
{
lean_object* x_492; lean_object* x_493; 
x_492 = lean_ctor_get(x_481, 0);
lean_inc(x_492);
lean_dec(x_481);
lean_inc(x_479);
x_493 = l_Lake_Workspace_findModuleBySrc_x3f(x_479, x_492);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_494 = l_Lake_setupFile___closed__3;
x_495 = l_List_foldl___at_Lake_setupFile___spec__1(x_492, x_494, x_3);
x_496 = lean_alloc_closure((void*)(l_Lake_buildImportsAndDeps), 8, 2);
lean_closure_set(x_496, 0, x_479);
lean_closure_set(x_496, 1, x_495);
lean_inc(x_492);
x_497 = l_Lake_Workspace_runFetchM___rarg(x_492, x_496, x_4, x_482);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = lean_ctor_get(x_498, 0);
lean_inc(x_500);
lean_dec(x_498);
x_501 = lean_io_wait(x_500, x_499);
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
lean_dec(x_501);
x_504 = lean_ctor_get(x_502, 0);
lean_inc(x_504);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_505 = x_502;
} else {
 lean_dec_ref(x_502);
 x_505 = lean_box(0);
}
x_506 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_492, x_504);
lean_dec(x_492);
x_507 = lean_box(0);
if (lean_is_scalar(x_505)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_505;
}
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
x_509 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_508);
x_510 = l_Lean_Json_compress(x_509);
x_511 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_510, x_503);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_514 = x_511;
} else {
 lean_dec_ref(x_511);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(0, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
return x_515;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; uint8_t x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; uint8_t x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_516 = lean_ctor_get(x_511, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_511, 1);
lean_inc(x_517);
lean_dec(x_511);
x_518 = lean_io_error_to_string(x_516);
x_519 = 3;
x_520 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set_uint8(x_520, sizeof(void*)*1, x_519);
x_521 = lean_box(1);
x_522 = 1;
x_523 = 0;
x_524 = l_Lake_OutStream_logEntry(x_521, x_520, x_522, x_523, x_517);
lean_dec(x_520);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_526 = x_524;
} else {
 lean_dec_ref(x_524);
 x_526 = lean_box(0);
}
x_527 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_526)) {
 x_528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_528 = x_526;
 lean_ctor_set_tag(x_528, 1);
}
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_528, 1, x_525);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; 
lean_dec(x_502);
lean_dec(x_492);
x_529 = lean_ctor_get(x_501, 1);
lean_inc(x_529);
lean_dec(x_501);
x_530 = l_Lake_setupFile___closed__5;
x_6 = x_530;
x_7 = x_529;
goto block_21;
}
}
else
{
lean_object* x_531; lean_object* x_532; 
lean_dec(x_492);
x_531 = lean_ctor_get(x_497, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_497, 1);
lean_inc(x_532);
lean_dec(x_497);
x_6 = x_531;
x_7 = x_532;
goto block_21;
}
}
else
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_479);
lean_dec(x_3);
x_533 = lean_ctor_get(x_493, 0);
lean_inc(x_533);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 x_534 = x_493;
} else {
 lean_dec_ref(x_493);
 x_534 = lean_box(0);
}
x_535 = lean_ctor_get(x_533, 2);
lean_inc(x_535);
if (lean_is_scalar(x_534)) {
 x_536 = lean_alloc_ctor(0, 1, 0);
} else {
 x_536 = x_534;
 lean_ctor_set_tag(x_536, 0);
}
lean_ctor_set(x_536, 0, x_535);
x_537 = l_Lake_Module_keyword;
x_538 = l_Lake_Module_depsFacet;
lean_inc(x_533);
x_539 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_539, 0, x_536);
lean_ctor_set(x_539, 1, x_537);
lean_ctor_set(x_539, 2, x_533);
lean_ctor_set(x_539, 3, x_538);
x_540 = lean_alloc_closure((void*)(l_Lake_BuildInfo_fetch___rarg), 8, 2);
lean_closure_set(x_540, 0, x_539);
lean_closure_set(x_540, 1, lean_box(0));
lean_inc(x_492);
x_541 = l_Lake_Workspace_runFetchM___rarg(x_492, x_540, x_4, x_482);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
lean_dec(x_541);
x_544 = lean_ctor_get(x_542, 0);
lean_inc(x_544);
lean_dec(x_542);
x_545 = lean_io_wait(x_544, x_543);
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; lean_object* x_556; lean_object* x_557; uint8_t x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; 
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
lean_dec(x_545);
x_548 = lean_ctor_get(x_546, 0);
lean_inc(x_548);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 lean_ctor_release(x_546, 1);
 x_549 = x_546;
} else {
 lean_dec_ref(x_546);
 x_549 = lean_box(0);
}
x_550 = lean_box(0);
x_551 = lean_ctor_get(x_533, 0);
lean_inc(x_551);
lean_dec(x_533);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_552, 3);
lean_inc(x_553);
lean_dec(x_552);
x_554 = lean_ctor_get(x_553, 1);
lean_inc(x_554);
lean_dec(x_553);
x_555 = lean_ctor_get_uint8(x_554, sizeof(void*)*13);
x_556 = lean_ctor_get(x_551, 2);
lean_inc(x_556);
lean_dec(x_551);
x_557 = lean_ctor_get(x_556, 0);
lean_inc(x_557);
lean_dec(x_556);
x_558 = lean_ctor_get_uint8(x_557, sizeof(void*)*13);
x_559 = l_Lake_instOrdBuildType;
x_560 = lean_box(x_555);
x_561 = lean_box(x_558);
x_562 = l_Ord_instDecidableRelLe___rarg(x_559, x_560, x_561);
x_563 = lean_ctor_get(x_554, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_554, 4);
lean_inc(x_564);
lean_dec(x_554);
x_565 = l_Array_append___rarg(x_563, x_564);
lean_dec(x_564);
x_566 = lean_ctor_get(x_557, 0);
lean_inc(x_566);
x_567 = lean_ctor_get(x_557, 4);
lean_inc(x_567);
lean_dec(x_557);
x_568 = l___private_Lake_CLI_Serve_0__Lake_mkLeanPaths(x_492, x_548);
lean_dec(x_492);
if (x_562 == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; 
x_592 = l_Lake_BuildType_leanOptions(x_558);
x_593 = l_Array_append___rarg(x_592, x_565);
lean_dec(x_565);
x_594 = l_Array_append___rarg(x_593, x_566);
lean_dec(x_566);
x_595 = l_Array_append___rarg(x_594, x_567);
lean_dec(x_567);
x_596 = lean_array_get_size(x_595);
x_597 = lean_unsigned_to_nat(0u);
x_598 = lean_nat_dec_lt(x_597, x_596);
if (x_598 == 0)
{
lean_dec(x_596);
lean_dec(x_595);
x_569 = x_550;
goto block_591;
}
else
{
uint8_t x_599; 
x_599 = lean_nat_dec_le(x_596, x_596);
if (x_599 == 0)
{
lean_dec(x_596);
lean_dec(x_595);
x_569 = x_550;
goto block_591;
}
else
{
size_t x_600; size_t x_601; lean_object* x_602; 
x_600 = 0;
x_601 = lean_usize_of_nat(x_596);
lean_dec(x_596);
x_602 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_595, x_600, x_601, x_550);
lean_dec(x_595);
x_569 = x_602;
goto block_591;
}
}
}
else
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; uint8_t x_609; 
x_603 = l_Lake_BuildType_leanOptions(x_555);
x_604 = l_Array_append___rarg(x_603, x_565);
lean_dec(x_565);
x_605 = l_Array_append___rarg(x_604, x_566);
lean_dec(x_566);
x_606 = l_Array_append___rarg(x_605, x_567);
lean_dec(x_567);
x_607 = lean_array_get_size(x_606);
x_608 = lean_unsigned_to_nat(0u);
x_609 = lean_nat_dec_lt(x_608, x_607);
if (x_609 == 0)
{
lean_dec(x_607);
lean_dec(x_606);
x_569 = x_550;
goto block_591;
}
else
{
uint8_t x_610; 
x_610 = lean_nat_dec_le(x_607, x_607);
if (x_610 == 0)
{
lean_dec(x_607);
lean_dec(x_606);
x_569 = x_550;
goto block_591;
}
else
{
size_t x_611; size_t x_612; lean_object* x_613; 
x_611 = 0;
x_612 = lean_usize_of_nat(x_607);
lean_dec(x_607);
x_613 = l_Array_foldlMUnsafe_fold___at_Lake_setupFile___spec__2(x_606, x_611, x_612, x_550);
lean_dec(x_606);
x_569 = x_613;
goto block_591;
}
}
}
block_591:
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
if (lean_is_scalar(x_549)) {
 x_570 = lean_alloc_ctor(0, 2, 0);
} else {
 x_570 = x_549;
}
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
x_571 = l___private_Lean_Util_FileSetupInfo_0__Lean_toJsonFileSetupInfo____x40_Lean_Util_FileSetupInfo___hyg_132_(x_570);
x_572 = l_Lean_Json_compress(x_571);
x_573 = l_IO_println___at_Lean_Environment_displayStats___spec__3(x_572, x_547);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_576 = x_573;
} else {
 lean_dec_ref(x_573);
 x_576 = lean_box(0);
}
if (lean_is_scalar(x_576)) {
 x_577 = lean_alloc_ctor(0, 2, 0);
} else {
 x_577 = x_576;
}
lean_ctor_set(x_577, 0, x_574);
lean_ctor_set(x_577, 1, x_575);
return x_577;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; uint8_t x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_578 = lean_ctor_get(x_573, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_573, 1);
lean_inc(x_579);
lean_dec(x_573);
x_580 = lean_io_error_to_string(x_578);
x_581 = 3;
x_582 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set_uint8(x_582, sizeof(void*)*1, x_581);
x_583 = lean_box(1);
x_584 = 1;
x_585 = 0;
x_586 = l_Lake_OutStream_logEntry(x_583, x_582, x_584, x_585, x_579);
lean_dec(x_582);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
if (lean_is_exclusive(x_586)) {
 lean_ctor_release(x_586, 0);
 lean_ctor_release(x_586, 1);
 x_588 = x_586;
} else {
 lean_dec_ref(x_586);
 x_588 = lean_box(0);
}
x_589 = l_Lake_setupFile___boxed__const__1;
if (lean_is_scalar(x_588)) {
 x_590 = lean_alloc_ctor(1, 2, 0);
} else {
 x_590 = x_588;
 lean_ctor_set_tag(x_590, 1);
}
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_587);
return x_590;
}
}
}
else
{
lean_object* x_614; lean_object* x_615; 
lean_dec(x_546);
lean_dec(x_533);
lean_dec(x_492);
x_614 = lean_ctor_get(x_545, 1);
lean_inc(x_614);
lean_dec(x_545);
x_615 = l_Lake_setupFile___closed__5;
x_6 = x_615;
x_7 = x_614;
goto block_21;
}
}
else
{
lean_object* x_616; lean_object* x_617; 
lean_dec(x_533);
lean_dec(x_492);
x_616 = lean_ctor_get(x_541, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_541, 1);
lean_inc(x_617);
lean_dec(x_541);
x_6 = x_616;
x_7 = x_617;
goto block_21;
}
}
}
}
}
block_21:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_io_error_to_string(x_6);
x_9 = 3;
x_10 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_9);
x_11 = lean_box(1);
x_12 = 1;
x_13 = 0;
x_14 = l_Lake_OutStream_logEntry(x_11, x_10, x_12, x_13, x_7);
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_List_foldl___at_Lake_setupFile___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___at_Lake_setupFile___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
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
x_15 = 1;
x_16 = 0;
lean_inc(x_5);
lean_inc(x_9);
x_17 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_9);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_5);
lean_ctor_set_uint8(x_17, sizeof(void*)*5, x_15);
lean_ctor_set_uint8(x_17, sizeof(void*)*5 + 1, x_16);
x_18 = lean_io_process_spawn(x_17, x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_io_process_child_wait(x_14, x_19, x_20);
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
x_24 = l_Lake_setupFile___closed__3;
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
x_33 = lean_ctor_get(x_32, 3);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 4);
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
x_46 = l_Lake_setupFile___closed__3;
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
x_55 = lean_ctor_get(x_54, 3);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_55, 4);
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
x_74 = l_Lake_setupFile___closed__3;
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
x_90 = l_Lake_setupFile___closed__3;
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
x_101 = lean_ctor_get(x_100, 3);
lean_inc(x_101);
lean_dec(x_100);
x_102 = lean_ctor_get(x_101, 4);
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
x_120 = l_Lake_setupFile___closed__3;
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
x_129 = lean_ctor_get(x_128, 3);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_ctor_get(x_129, 4);
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
x_144 = l_Lake_setupFile___closed__3;
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
x_153 = lean_ctor_get(x_152, 3);
lean_inc(x_153);
lean_dec(x_152);
x_154 = lean_ctor_get(x_153, 4);
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
x_173 = l_Lake_setupFile___closed__3;
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
x_184 = lean_ctor_get(x_183, 3);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_ctor_get(x_184, 4);
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
x_206 = l_Lake_setupFile___closed__3;
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
x_216 = lean_ctor_get(x_215, 3);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get(x_216, 4);
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
x_231 = l_Lake_setupFile___closed__3;
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
x_241 = lean_ctor_get(x_240, 3);
lean_inc(x_241);
lean_dec(x_240);
x_242 = lean_ctor_get(x_241, 4);
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
x_261 = l_Lake_setupFile___closed__3;
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
x_272 = lean_ctor_get(x_271, 3);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_ctor_get(x_272, 4);
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
lean_object* initialize_Lake_Load(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_MainM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FileSetupInfo(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_CLI_Serve(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
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
