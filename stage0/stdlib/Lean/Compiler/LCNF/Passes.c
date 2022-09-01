// Lean compiler output
// Module: Lean.Compiler.LCNF.Passes
// Imports: Init Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.CSE Lean.Compiler.LCNF.Simp
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
static lean_object* l_Lean_Compiler_LCNF_simpInstaller___closed__1;
static lean_object* l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__6;
lean_object* l_Lean_Compiler_LCNF_Decl_pullInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_PassInstaller_installAfter___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__4;
static lean_object* l_Lean_Compiler_LCNF_simpInstaller___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_pullInstancesInstaller;
static lean_object* l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cseInstaller;
static lean_object* l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__1;
static lean_object* l_Lean_Compiler_LCNF_simpInstaller___closed__4;
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cseInstaller___closed__4;
lean_object* l_Lean_Compiler_LCNF_Decl_cse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__3;
static lean_object* l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__7;
static lean_object* l_Lean_Compiler_LCNF_simpInstaller___closed__3;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simpInstaller;
static lean_object* l_Lean_Compiler_LCNF_cseInstaller___closed__3;
static lean_object* l_Lean_Compiler_LCNF_cseInstaller___closed__5;
static lean_object* l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__5;
static lean_object* l_Lean_Compiler_LCNF_cseInstaller___closed__1;
static lean_object* l_Lean_Compiler_LCNF_simpInstaller___closed__5;
static lean_object* l_Lean_Compiler_LCNF_cseInstaller___closed__2;
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("init", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("pullInstances", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_pullInstances), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__4;
x_2 = l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__5;
x_3 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__2;
x_2 = l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__6;
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___elambda__1___boxed), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_pullInstancesInstaller() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cseInstaller___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("cse", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cseInstaller___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_cseInstaller___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cseInstaller___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_cse), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cseInstaller___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_cseInstaller___closed__2;
x_2 = l_Lean_Compiler_LCNF_cseInstaller___closed__3;
x_3 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cseInstaller___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__4;
x_2 = l_Lean_Compiler_LCNF_cseInstaller___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___elambda__1___boxed), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cseInstaller() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_cseInstaller___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpInstaller___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpInstaller___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_simpInstaller___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpInstaller___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_simp), 5, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpInstaller___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_simpInstaller___closed__2;
x_2 = l_Lean_Compiler_LCNF_simpInstaller___closed__3;
x_3 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpInstaller___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_cseInstaller___closed__2;
x_2 = l_Lean_Compiler_LCNF_simpInstaller___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_installAfter___elambda__1___boxed), 7, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simpInstaller() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_simpInstaller___closed__5;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Passes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PullLetDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CSE(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__1 = _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__1);
l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__2 = _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__2);
l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__3 = _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__3);
l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__4 = _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__4);
l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__5 = _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__5);
l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__6 = _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__6);
l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__7 = _init_l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstancesInstaller___closed__7);
l_Lean_Compiler_LCNF_pullInstancesInstaller = _init_l_Lean_Compiler_LCNF_pullInstancesInstaller();
lean_mark_persistent(l_Lean_Compiler_LCNF_pullInstancesInstaller);
l_Lean_Compiler_LCNF_cseInstaller___closed__1 = _init_l_Lean_Compiler_LCNF_cseInstaller___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_cseInstaller___closed__1);
l_Lean_Compiler_LCNF_cseInstaller___closed__2 = _init_l_Lean_Compiler_LCNF_cseInstaller___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_cseInstaller___closed__2);
l_Lean_Compiler_LCNF_cseInstaller___closed__3 = _init_l_Lean_Compiler_LCNF_cseInstaller___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_cseInstaller___closed__3);
l_Lean_Compiler_LCNF_cseInstaller___closed__4 = _init_l_Lean_Compiler_LCNF_cseInstaller___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_cseInstaller___closed__4);
l_Lean_Compiler_LCNF_cseInstaller___closed__5 = _init_l_Lean_Compiler_LCNF_cseInstaller___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_cseInstaller___closed__5);
l_Lean_Compiler_LCNF_cseInstaller = _init_l_Lean_Compiler_LCNF_cseInstaller();
lean_mark_persistent(l_Lean_Compiler_LCNF_cseInstaller);
l_Lean_Compiler_LCNF_simpInstaller___closed__1 = _init_l_Lean_Compiler_LCNF_simpInstaller___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_simpInstaller___closed__1);
l_Lean_Compiler_LCNF_simpInstaller___closed__2 = _init_l_Lean_Compiler_LCNF_simpInstaller___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_simpInstaller___closed__2);
l_Lean_Compiler_LCNF_simpInstaller___closed__3 = _init_l_Lean_Compiler_LCNF_simpInstaller___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_simpInstaller___closed__3);
l_Lean_Compiler_LCNF_simpInstaller___closed__4 = _init_l_Lean_Compiler_LCNF_simpInstaller___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_simpInstaller___closed__4);
l_Lean_Compiler_LCNF_simpInstaller___closed__5 = _init_l_Lean_Compiler_LCNF_simpInstaller___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_simpInstaller___closed__5);
l_Lean_Compiler_LCNF_simpInstaller = _init_l_Lean_Compiler_LCNF_simpInstaller();
lean_mark_persistent(l_Lean_Compiler_LCNF_simpInstaller);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
