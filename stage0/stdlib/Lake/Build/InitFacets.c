// Lean compiler output
// Module: Lake.Build.InitFacets
// Imports: Lake.Build.Module Lake.Build.Package Lake.Build.Library Lake.Build.Executable Lake.Build.ExternLib
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
static lean_object* l_Lake_initFacetConfigs___closed__12;
static lean_object* l_Lake_initFacetConfigs___closed__5;
static lean_object* l_Lake_initFacetConfigs___closed__10;
static lean_object* l_Lake_initFacetConfigs___closed__9;
static lean_object* l_Lake_initFacetConfigs___closed__8;
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs_insert___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_LeanExe_initFacetConfigs;
extern lean_object* l_Lake_Module_initFacetConfigs;
static lean_object* l_Lake_initFacetConfigs___closed__1;
static lean_object* l_Lake_initFacetConfigs___closed__3;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initFacetConfigs___closed__6;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lake_initFacetConfigs___closed__4;
extern lean_object* l_Lake_Package_initFacetConfigs;
static lean_object* l_Lake_initFacetConfigs___closed__14;
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs;
static lean_object* l_Lake_initFacetConfigs___closed__11;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lake_Workspace_addFacetConfig___spec__1(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initFacetConfigs___closed__7;
static lean_object* l_Lake_initFacetConfigs___closed__15;
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs_insert(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_initFacetConfigs___closed__2;
extern lean_object* l_Lake_ExternLib_initFacetConfigs;
static lean_object* l_Lake_initFacetConfigs___closed__13;
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 3);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(x_1, x_2, x_4);
x_9 = l_Lean_RBNode_insert___at_Lake_Workspace_addFacetConfig___spec__1(x_8, x_5, x_6);
x_2 = x_9;
x_3 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_initFacetConfigs_insert(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(x_1, x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
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
static lean_object* _init_l_Lake_initFacetConfigs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("module", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_initFacetConfigs___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lake_initFacetConfigs___closed__2;
x_3 = l_Lake_Module_initFacetConfigs;
x_4 = l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(x_2, x_1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("package", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_initFacetConfigs___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initFacetConfigs___closed__5;
x_2 = l_Lake_initFacetConfigs___closed__3;
x_3 = l_Lake_Package_initFacetConfigs;
x_4 = l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_lib", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_initFacetConfigs___closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initFacetConfigs___closed__8;
x_2 = l_Lake_initFacetConfigs___closed__6;
x_3 = l_Lake_LeanLib_initFacetConfigs;
x_4 = l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lean_exe", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_initFacetConfigs___closed__10;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initFacetConfigs___closed__11;
x_2 = l_Lake_initFacetConfigs___closed__9;
x_3 = l_Lake_LeanExe_initFacetConfigs;
x_4 = l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("extern_lib", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_initFacetConfigs___closed__13;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_initFacetConfigs___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_initFacetConfigs___closed__14;
x_2 = l_Lake_initFacetConfigs___closed__12;
x_3 = l_Lake_ExternLib_initFacetConfigs;
x_4 = l_Lean_RBNode_fold___at_Lake_initFacetConfigs_insert___spec__1(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_initFacetConfigs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_initFacetConfigs___closed__15;
return x_1;
}
}
lean_object* initialize_Lake_Build_Module(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Package(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Library(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Executable(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_ExternLib(uint8_t builtin, lean_object*);
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
l_Lake_initFacetConfigs___closed__7 = _init_l_Lake_initFacetConfigs___closed__7();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__7);
l_Lake_initFacetConfigs___closed__8 = _init_l_Lake_initFacetConfigs___closed__8();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__8);
l_Lake_initFacetConfigs___closed__9 = _init_l_Lake_initFacetConfigs___closed__9();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__9);
l_Lake_initFacetConfigs___closed__10 = _init_l_Lake_initFacetConfigs___closed__10();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__10);
l_Lake_initFacetConfigs___closed__11 = _init_l_Lake_initFacetConfigs___closed__11();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__11);
l_Lake_initFacetConfigs___closed__12 = _init_l_Lake_initFacetConfigs___closed__12();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__12);
l_Lake_initFacetConfigs___closed__13 = _init_l_Lake_initFacetConfigs___closed__13();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__13);
l_Lake_initFacetConfigs___closed__14 = _init_l_Lake_initFacetConfigs___closed__14();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__14);
l_Lake_initFacetConfigs___closed__15 = _init_l_Lake_initFacetConfigs___closed__15();
lean_mark_persistent(l_Lake_initFacetConfigs___closed__15);
l_Lake_initFacetConfigs = _init_l_Lake_initFacetConfigs();
lean_mark_persistent(l_Lake_initFacetConfigs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
