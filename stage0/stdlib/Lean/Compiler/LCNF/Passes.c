// Lean compiler output
// Module: Lean.Compiler.LCNF.Passes
// Imports: Init Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.CSE Lean.Compiler.LCNF.Simp Lean.Compiler.LCNF.PullFunDecls Lean.Compiler.LCNF.ReduceJpArity Lean.Compiler.LCNF.JoinPoints Lean.Compiler.LCNF.Specialize
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__12;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__8;
extern lean_object* l_Lean_Compiler_LCNF_findJoinPoints;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__6;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__14;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__5;
extern lean_object* l_Lean_Compiler_LCNF_reduceJpArity;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__2;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__1;
extern lean_object* l_Lean_Compiler_LCNF_specialize;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__9;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__4;
extern lean_object* l_Lean_Compiler_LCNF_pullFunDecls;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_builtin;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__3;
lean_object* l_Lean_Compiler_LCNF_PassInstaller_append___elambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_pullInstances;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__13;
lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__7;
extern lean_object* l_Lean_Compiler_LCNF_cse;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__11;
static lean_object* l_Lean_Compiler_LCNF_builtin___closed__10;
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 0;
x_3 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Compiler_LCNF_simp(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__3() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = 1;
x_3 = lean_alloc_ctor(0, 1, 3);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 2, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__3;
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Lean_Compiler_LCNF_simp(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__5;
x_2 = l_Lean_Compiler_LCNF_pullInstances;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__6;
x_2 = l_Lean_Compiler_LCNF_cse;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__7;
x_2 = l_Lean_Compiler_LCNF_builtin___closed__2;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__8;
x_2 = l_Lean_Compiler_LCNF_pullFunDecls;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__9;
x_2 = l_Lean_Compiler_LCNF_findJoinPoints;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__10;
x_2 = l_Lean_Compiler_LCNF_reduceJpArity;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__11;
x_2 = l_Lean_Compiler_LCNF_builtin___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__12;
x_2 = l_Lean_Compiler_LCNF_specialize;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__13;
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_PassInstaller_append___elambda__1___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_builtin() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_builtin___closed__14;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullLetDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CSE(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PullFunDecls(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_JoinPoints(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Specialize(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Compiler_LCNF_PullFunDecls(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_JoinPoints(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Specialize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_builtin___closed__1 = _init_l_Lean_Compiler_LCNF_builtin___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__1);
l_Lean_Compiler_LCNF_builtin___closed__2 = _init_l_Lean_Compiler_LCNF_builtin___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__2);
l_Lean_Compiler_LCNF_builtin___closed__3 = _init_l_Lean_Compiler_LCNF_builtin___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__3);
l_Lean_Compiler_LCNF_builtin___closed__4 = _init_l_Lean_Compiler_LCNF_builtin___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__4);
l_Lean_Compiler_LCNF_builtin___closed__5 = _init_l_Lean_Compiler_LCNF_builtin___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__5);
l_Lean_Compiler_LCNF_builtin___closed__6 = _init_l_Lean_Compiler_LCNF_builtin___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__6);
l_Lean_Compiler_LCNF_builtin___closed__7 = _init_l_Lean_Compiler_LCNF_builtin___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__7);
l_Lean_Compiler_LCNF_builtin___closed__8 = _init_l_Lean_Compiler_LCNF_builtin___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__8);
l_Lean_Compiler_LCNF_builtin___closed__9 = _init_l_Lean_Compiler_LCNF_builtin___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__9);
l_Lean_Compiler_LCNF_builtin___closed__10 = _init_l_Lean_Compiler_LCNF_builtin___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__10);
l_Lean_Compiler_LCNF_builtin___closed__11 = _init_l_Lean_Compiler_LCNF_builtin___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__11);
l_Lean_Compiler_LCNF_builtin___closed__12 = _init_l_Lean_Compiler_LCNF_builtin___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__12);
l_Lean_Compiler_LCNF_builtin___closed__13 = _init_l_Lean_Compiler_LCNF_builtin___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__13);
l_Lean_Compiler_LCNF_builtin___closed__14 = _init_l_Lean_Compiler_LCNF_builtin___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin___closed__14);
l_Lean_Compiler_LCNF_builtin = _init_l_Lean_Compiler_LCNF_builtin();
lean_mark_persistent(l_Lean_Compiler_LCNF_builtin);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
