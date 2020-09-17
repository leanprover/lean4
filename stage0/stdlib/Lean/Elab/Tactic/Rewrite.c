// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrite
// Imports: Init Lean.Elab.Tactic.Basic Lean.Elab.Tactic.ElabTerm
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
lean_object* l_Lean_Elab_Tactic_expandRewriteTactic___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewrite(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandRewriteTactic___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__3;
extern lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1;
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Elab_Tactic_evalRewrite___rarg___closed__2;
lean_object* l_Lean_Elab_Tactic_evalRewrite___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRewrite___rarg___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3;
lean_object* l_Lean_Elab_Tactic_evalRewrite___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRewrite(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRewrite___boxed(lean_object*);
lean_object* l_Lean_Elab_Tactic_expandRewriteTactic(lean_object*, lean_object*, lean_object*);
lean_object* _init_l_Lean_Elab_Tactic_expandRewriteTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP");
return x_1;
}
}
lean_object* l_Lean_Elab_Tactic_expandRewriteTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Elab_Tactic_expandRewriteTactic___closed__1;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
lean_object* l_Lean_Elab_Tactic_expandRewriteTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_expandRewriteTactic(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rewriteSeq");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_expandRewriteTactic___boxed), 3, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_macroAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalRewrite___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_expandRewriteTactic___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalRewrite___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRewrite___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewrite___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_evalRewrite___rarg___closed__2;
x_11 = l_Lean_throwError___at_Lean_Elab_Tactic_evalTactic___main___spec__1___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewrite(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewrite___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewrite___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalRewrite___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewrite___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalRewrite(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rewrite");
return x_1;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewrite___boxed), 1, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewrite(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__3;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Rewrite(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_expandRewriteTactic___closed__1 = _init_l_Lean_Elab_Tactic_expandRewriteTactic___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_expandRewriteTactic___closed__1);
l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1);
l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2);
l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalRewrite___rarg___closed__1 = _init_l_Lean_Elab_Tactic_evalRewrite___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewrite___rarg___closed__1);
l_Lean_Elab_Tactic_evalRewrite___rarg___closed__2 = _init_l_Lean_Elab_Tactic_evalRewrite___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewrite___rarg___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_evalRewrite(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
