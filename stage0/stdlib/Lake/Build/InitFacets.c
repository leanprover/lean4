// Lean compiler output
// Module: Lake.Build.InitFacets
// Imports: Lake.Build.Module Lake.Build.Package Lake.Build.Library Lake.Build.Executable Lake.Build.ExternLib Lake.Build.InputFile
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
extern lean_object* l_Lake_LeanLib_initFacetConfigs;
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initFacetConfigs___closed__5;
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs_insert___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_initFacetConfigs;
extern lean_object* l_Lake_Module_initFacetConfigs;
static lean_object* l_Lake_initFacetConfigs___closed__1;
static lean_object* l_Lake_initFacetConfigs___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(lean_object*, lean_object*);
static lean_object* l_Lake_initFacetConfigs___closed__6;
static lean_object* l_Lake_initFacetConfigs___closed__4;
extern lean_object* l_Lake_Package_initFacetConfigs;
static lean_object* l_Lake_initFacetConfigs___closed__0;
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs;
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs_insert___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs_insert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initFacetConfigs___closed__2;
extern lean_object* l_Lake_ExternLib_initFacetConfigs;
extern lean_object* l_Lake_InputFile_initFacetConfigs;
extern lean_object* l_Lake_InputDir_initFacetConfigs;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 3);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_1, x_3);
x_8 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_7, x_4, x_5);
x_1 = x_8;
x_2 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs_insert___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs_insert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_initFacetConfigs_insert(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Module_initFacetConfigs;
x_2 = lean_box(0);
x_3 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Package_initFacetConfigs;
x_2 = l_Lake_initFacetConfigs___closed__0;
x_3 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanLib_initFacetConfigs;
x_2 = l_Lake_initFacetConfigs___closed__1;
x_3 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_LeanExe_initFacetConfigs;
x_2 = l_Lake_initFacetConfigs___closed__2;
x_3 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_ExternLib_initFacetConfigs;
x_2 = l_Lake_initFacetConfigs___closed__3;
x_3 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_InputFile_initFacetConfigs;
x_2 = l_Lake_initFacetConfigs___closed__4;
x_3 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_InputDir_initFacetConfigs;
x_2 = l_Lake_initFacetConfigs___closed__5;
x_3 = l_Lean_RBNode_fold___at___Lake_initFacetConfigs_insert_spec__0(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initFacetConfigs___closed__6;
return x_1;
}
}
lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Library(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Executable(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_ExternLib(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_InputFile(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_InitFacets(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Module(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Package(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Library(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Executable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_ExternLib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_InputFile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_initFacetConfigs___closed__0 = _init_l_Lake_initFacetConfigs___closed__0();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__0);
l_Lake_initFacetConfigs___closed__1 = _init_l_Lake_initFacetConfigs___closed__1();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__1);
l_Lake_initFacetConfigs___closed__2 = _init_l_Lake_initFacetConfigs___closed__2();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__2);
l_Lake_initFacetConfigs___closed__3 = _init_l_Lake_initFacetConfigs___closed__3();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__3);
l_Lake_initFacetConfigs___closed__4 = _init_l_Lake_initFacetConfigs___closed__4();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__4);
l_Lake_initFacetConfigs___closed__5 = _init_l_Lake_initFacetConfigs___closed__5();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__5);
l_Lake_initFacetConfigs___closed__6 = _init_l_Lake_initFacetConfigs___closed__6();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__6);
l_Lake_initFacetConfigs = _init_l_Lake_initFacetConfigs();
lean_mark_persistent(l_Lake_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
