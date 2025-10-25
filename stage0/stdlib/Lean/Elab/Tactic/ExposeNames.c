// Lean compiler output
// Module: Lean.Elab.Tactic.ExposeNames
// Imports: public import Lean.Meta.Tactic.ExposeNames public import Lean.Elab.Tactic.Basic
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
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___boxed(lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3;
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0;
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4;
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exposeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal___redArg(x_2, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_12 = l_Lean_MVarId_exposeNames(x_11, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Elab_Tactic_replaceMainGoal___redArg(x_15, x_2, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_12, 0);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0___boxed), 9, 0);
x_11 = l_Lean_Elab_Tactic_withMainContext___redArg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalExposeNames___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalExposeNames___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalExposeNames___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalExposeNames(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exposeNames", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4;
x_2 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2;
x_4 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalExposeNames", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7;
x_2 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3;
x_3 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6;
x_4 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0;
x_3 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5;
x_4 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8;
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExposeNames___boxed), 10, 0);
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_ExposeNames(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_ExposeNames(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0 = _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__0);
l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1 = _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1);
l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2 = _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2);
l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3 = _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3);
l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4 = _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4);
l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5 = _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5);
l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6 = _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6);
l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7 = _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7);
l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8 = _init_l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8);
if (builtin) {res = l_Lean_Elab_Tactic_evalExposeNames___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
