// Lean compiler output
// Module: Init.Lean.Hygiene
// Imports: Init.Control Init.Lean.Syntax
#include "runtime/lean.h"
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
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__3;
lean_object* l_Lean_Unhygienic_run(lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__5;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_run___rarg(lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__4;
lean_object* l_List_head_x21___at_Lean_Unhygienic_MonadQuotation___spec__2___boxed(lean_object*);
lean_object* l_ReaderT_read___at_Lean_Unhygienic_MonadQuotation___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_head_x21___rarg___closed__2;
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation;
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Unhygienic_MonadQuotation___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___at_Lean_Unhygienic_MonadQuotation___spec__2(lean_object*);
lean_object* l_Lean_Unhygienic_MonadQuotation___closed__2;
lean_object* l_Lean_Unhygienic_run___rarg___closed__1;
extern lean_object* l_Nat_Inhabited;
lean_object* l_ReaderT_bind___at_Lean_Unhygienic_MonadQuotation___spec__3(lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
lean_object* l_ReaderT_read___at_Lean_Unhygienic_MonadQuotation___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_List_head_x21___at_Lean_Unhygienic_MonadQuotation___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_Inhabited;
x_3 = l_List_head_x21___rarg___closed__2;
x_4 = lean_panic_fn(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
return x_5;
}
}
}
lean_object* l_ReaderT_bind___at_Lean_Unhygienic_MonadQuotation___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_3);
x_5 = lean_apply_2(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_3(x_2, x_6, x_3, x_7);
return x_8;
}
}
lean_object* l_ReaderT_bind___at_Lean_Unhygienic_MonadQuotation___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_MonadQuotation___spec__3___rarg), 4, 0);
return x_3;
}
}
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_List_head_x21___at_Lean_Unhygienic_MonadQuotation___spec__2(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_3);
x_8 = lean_apply_2(x_2, x_7, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_ReaderT_read___at_Lean_Unhygienic_MonadQuotation___spec__1), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Unhygienic_MonadQuotation___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Unhygienic_MonadQuotation___closed__1;
x_2 = l_Lean_Unhygienic_MonadQuotation___closed__2;
x_3 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Unhygienic_MonadQuotation___spec__3___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Unhygienic_MonadQuotation___lambda__2), 4, 0);
return x_1;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Unhygienic_MonadQuotation___closed__3;
x_2 = l_Lean_Unhygienic_MonadQuotation___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Unhygienic_MonadQuotation() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Unhygienic_MonadQuotation___closed__5;
return x_1;
}
}
lean_object* l_List_head_x21___at_Lean_Unhygienic_MonadQuotation___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_head_x21___at_Lean_Unhygienic_MonadQuotation___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Unhygienic_MonadQuotation___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Unhygienic_MonadQuotation___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* _init_l_Lean_Unhygienic_run___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
lean_object* l_Lean_Unhygienic_run___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Unhygienic_run___rarg___closed__1;
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Unhygienic_run(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Unhygienic_run___rarg), 1, 0);
return x_2;
}
}
lean_object* initialize_Init_Control(lean_object*);
lean_object* initialize_Init_Lean_Syntax(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Hygiene(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Syntax(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Unhygienic_MonadQuotation___closed__1 = _init_l_Lean_Unhygienic_MonadQuotation___closed__1();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__1);
l_Lean_Unhygienic_MonadQuotation___closed__2 = _init_l_Lean_Unhygienic_MonadQuotation___closed__2();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__2);
l_Lean_Unhygienic_MonadQuotation___closed__3 = _init_l_Lean_Unhygienic_MonadQuotation___closed__3();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__3);
l_Lean_Unhygienic_MonadQuotation___closed__4 = _init_l_Lean_Unhygienic_MonadQuotation___closed__4();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__4);
l_Lean_Unhygienic_MonadQuotation___closed__5 = _init_l_Lean_Unhygienic_MonadQuotation___closed__5();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation___closed__5);
l_Lean_Unhygienic_MonadQuotation = _init_l_Lean_Unhygienic_MonadQuotation();
lean_mark_persistent(l_Lean_Unhygienic_MonadQuotation);
l_Lean_Unhygienic_run___rarg___closed__1 = _init_l_Lean_Unhygienic_run___rarg___closed__1();
lean_mark_persistent(l_Lean_Unhygienic_run___rarg___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
