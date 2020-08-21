// Lean compiler output
// Module: Lean.Meta.Exception
// Imports: Init Lean.Environment Lean.MetavarContext Lean.Message Lean.CoreM Lean.Util.PPGoal
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
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Meta_Exception_Inhabited___closed__1;
lean_object* l_Lean_Meta_Exception_Inhabited;
lean_object* l_Lean_Meta_Exception_toMessageData___boxed(lean_object*);
lean_object* l_Lean_Meta_Exception_getRef(lean_object*);
lean_object* l_Lean_Meta_Exception_toMessageData___closed__1;
lean_object* l_Lean_Meta_Exception_toMessageData___closed__2;
lean_object* l_Lean_Meta_Exception_toMessageData___closed__3;
lean_object* l_Lean_Meta_Exception_getRef___boxed(lean_object*);
extern lean_object* l_Lean_Core_Exception_inhabited___closed__1;
lean_object* l_Lean_Meta_Exception_mkCtx(lean_object*, lean_object*);
lean_object* _init_l_Lean_Meta_Exception_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_Exception_inhabited___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Exception_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_Exception_getRef(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
return x_4;
}
}
}
lean_object* l_Lean_Meta_Exception_getRef___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Exception_getRef(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Exception_mkCtx(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("<isDefEqStuck>");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toMessageData___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toMessageData___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Exception_toMessageData___closed__3;
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
return x_4;
}
}
}
lean_object* l_Lean_Meta_Exception_toMessageData___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Exception_toMessageData(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Environment(lean_object*);
lean_object* initialize_Lean_MetavarContext(lean_object*);
lean_object* initialize_Lean_Message(lean_object*);
lean_object* initialize_Lean_CoreM(lean_object*);
lean_object* initialize_Lean_Util_PPGoal(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Exception(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MetavarContext(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_PPGoal(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Exception_Inhabited___closed__1 = _init_l_Lean_Meta_Exception_Inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_Exception_Inhabited___closed__1);
l_Lean_Meta_Exception_Inhabited = _init_l_Lean_Meta_Exception_Inhabited();
lean_mark_persistent(l_Lean_Meta_Exception_Inhabited);
l_Lean_Meta_Exception_toMessageData___closed__1 = _init_l_Lean_Meta_Exception_toMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Exception_toMessageData___closed__1);
l_Lean_Meta_Exception_toMessageData___closed__2 = _init_l_Lean_Meta_Exception_toMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Exception_toMessageData___closed__2);
l_Lean_Meta_Exception_toMessageData___closed__3 = _init_l_Lean_Meta_Exception_toMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_Exception_toMessageData___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
