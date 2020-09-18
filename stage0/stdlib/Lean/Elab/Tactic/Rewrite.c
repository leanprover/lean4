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
extern lean_object* l_Lean_nullKind;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
lean_object* l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic(lean_object*);
extern lean_object* l_Lean_Parser_declareBuiltinParser___closed__3;
lean_object* l_Lean_Elab_Tactic_evalRewrite___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTactic___main___spec__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2;
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1;
extern lean_object* l_Lean_Elab_macroAttribute;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__1;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__2;
lean_object* l_Lean_Elab_Tactic_evalRewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRewrite___closed__1;
lean_object* l_Lean_Elab_Tactic_evalRewrite___closed__2;
lean_object* l_Lean_Elab_Tactic_expandRewriteTactic(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rewrite");
return x_1;
}
}
lean_object* _init_l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___regBuiltin_Lean_Elab_Term_Quotation_elabTacticQuot___closed__1;
x_2 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_4;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_fget(x_4, x_3);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_fset(x_4, x_3, x_9);
x_11 = x_8;
x_12 = l_Lean_Syntax_getArg(x_1, x_9);
x_13 = l_Lean_Parser_declareBuiltinParser___closed__3;
x_14 = lean_array_push(x_13, x_12);
x_15 = lean_array_push(x_14, x_11);
lean_inc(x_2);
x_16 = lean_array_push(x_15, x_2);
x_17 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__2;
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_3, x_19);
x_21 = x_18;
x_22 = lean_array_fset(x_10, x_3, x_21);
lean_dec(x_3);
x_3 = x_20;
x_4 = x_22;
goto _start;
}
}
}
lean_object* l_Lean_Elab_Tactic_expandRewriteTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Syntax_getArg(x_1, x_4);
x_6 = l_Lean_Syntax_getArg(x_5, x_4);
lean_dec(x_5);
x_7 = l_Lean_Syntax_getArgs(x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_empty___closed__1;
x_11 = l_Array_foldlStepMAux___main___at_Lean_Elab_Term_elabParen___spec__1(x_8, x_7, x_9, x_10);
lean_dec(x_7);
x_12 = l_Lean_Syntax_getArg(x_1, x_8);
x_13 = x_11;
x_14 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1(x_1, x_12, x_9, x_13);
x_15 = x_14;
x_16 = l_Lean_nullKind;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_expandRewriteTactic___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_expandRewriteTactic(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* _init_l_Lean_Elab_Tactic_evalRewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("WIP ");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalRewrite___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRewrite___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Tactic_evalRewrite___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_evalRewrite___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = l_Lean_Elab_Tactic_evalRewrite___closed__3;
x_13 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = 0;
x_15 = l_Lean_Elab_log___at_Lean_Elab_Tactic_evalTactic___main___spec__10(x_13, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalRewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalRewrite(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewrite___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewrite(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1;
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
l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__1 = _init_l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__1();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__1);
l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__2 = _init_l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__2();
lean_mark_persistent(l_Array_umapMAux___main___at_Lean_Elab_Tactic_expandRewriteTactic___spec__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__1);
l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__2);
l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic___closed__3);
res = l___regBuiltin_Lean_Elab_Tactic_expandRewriteTactic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalRewrite___closed__1 = _init_l_Lean_Elab_Tactic_evalRewrite___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewrite___closed__1);
l_Lean_Elab_Tactic_evalRewrite___closed__2 = _init_l_Lean_Elab_Tactic_evalRewrite___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewrite___closed__2);
l_Lean_Elab_Tactic_evalRewrite___closed__3 = _init_l_Lean_Elab_Tactic_evalRewrite___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalRewrite___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewrite___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalRewrite(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
