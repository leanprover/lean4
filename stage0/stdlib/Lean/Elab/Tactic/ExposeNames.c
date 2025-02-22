// Lean compiler output
// Module: Lean.Elab.Tactic.ExposeNames
// Imports: Lean.Meta.Tactic.ExposeNames Lean.Elab.Tactic.Basic
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
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7;
static lean_object* l_Lean_Elab_Tactic_evalExposeNames___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___boxed(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__9;
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8;
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1(lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1;
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__10;
lean_object* l_Lean_MVarId_exposeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_getMainGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_MVarId_exposeNames(x_11, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Elab_Tactic_replaceMainGoal(x_17, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_13, 0);
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_13);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
return x_10;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
x_25 = lean_ctor_get(x_10, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_10);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_evalExposeNames___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExposeNames___rarg___lambda__1___boxed), 9, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Elab_Tactic_evalExposeNames___rarg___closed__1;
x_11 = l_Lean_Elab_Tactic_withMainContext___rarg(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExposeNames___rarg), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_evalExposeNames___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalExposeNames___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Tactic_evalExposeNames(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exposeNames", 11, 11);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Elab", 4, 4);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("evalExposeNames", 15, 15);
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1;
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_tacticElabAttribute;
return x_1;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalExposeNames___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__9;
x_3 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8;
x_5 = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__10;
x_6 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Tactic_ExposeNames(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_ExposeNames(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_ExposeNames(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_evalExposeNames___rarg___closed__1 = _init_l_Lean_Elab_Tactic_evalExposeNames___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_evalExposeNames___rarg___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__1);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__2);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__4);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__5);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__6);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__7);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__8);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__9 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__9();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__9);
l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__10 = _init_l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__10();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1___closed__10);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalExposeNames__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
