// Lean compiler output
// Module: Std.Do.WP.IO
// Imports: Init.System.IO Std.Do.WP.Monad
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
LEAN_EXPORT lean_object* l_Std_Do_IO_Bare_instWPMonad(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_IO_Bare_instWP___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Do_IO_Bare_instWPMonad___closed__0;
LEAN_EXPORT lean_object* l___private_Std_Do_WP_IO_0__EStateM_bind_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_IO_0__Std_Do_IO_Bare_instWP_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_IO_Bare_instWP(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_IO_0__Std_Do_IO_Bare_instWP_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_WP_IO_0__EStateM_bind_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_IO_Bare_instWP___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_IO_Bare_instWP___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_Std_Do_IO_Bare_instWP(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Do_IO_Bare_instWP___lam__0___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Do_IO_Bare_instWP___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Do_IO_Bare_instWP___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_IO_0__EStateM_bind_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_IO_0__EStateM_bind_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Do_WP_IO_0__EStateM_bind_match__1_splitter___redArg(x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_IO_0__Std_Do_IO_Bare_instWP_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_WP_IO_0__Std_Do_IO_Bare_instWP_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Do_WP_IO_0__Std_Do_IO_Bare_instWP_match__1_splitter___redArg(x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Std_Do_IO_Bare_instWPMonad___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Do_IO_Bare_instWP___lam__0___boxed), 3, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Do_IO_Bare_instWPMonad(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Do_IO_Bare_instWPMonad___closed__0;
return x_2;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Do_WP_Monad(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_WP_IO(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Do_WP_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Do_IO_Bare_instWPMonad___closed__0 = _init_l_Std_Do_IO_Bare_instWPMonad___closed__0();
lean_mark_persistent(l_Std_Do_IO_Bare_instWPMonad___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
