// Lean compiler output
// Module: Lean.Elab.Exception
// Imports: Init Init.System.IOError Lean.Meta.Message
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
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Elab_Exception_monadIO___rarg(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_Exception_inhabited___closed__1;
lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Exception_hasToString___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Exception_monadIO(lean_object*);
lean_object* l_Lean_Elab_Exception_inhabited;
lean_object* l_Lean_Elab_mkExceptionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Exception_hasToString(lean_object*);
extern lean_object* l_Lean_Message_Inhabited___closed__2;
lean_object* l_Lean_Elab_mkExceptionCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Message_toString(lean_object*);
lean_object* l_Lean_Elab_Exception_monadIO___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
}
lean_object* l_Lean_Elab_Exception_monadIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Exception_monadIO___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Exception_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Message_Inhabited___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Exception_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Exception_inhabited___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Exception_hasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unsupported syntax");
return x_1;
}
}
lean_object* l_Lean_Elab_Exception_hasToString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_Message_toString(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_io_error_to_string(x_4);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Exception_hasToString___closed__1;
return x_6;
}
}
}
}
lean_object* l_Lean_Elab_mkMessageCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_FileMap_toPosition(x_2, x_5);
x_7 = lean_box(0);
x_8 = l_String_splitAux___main___closed__1;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_4);
return x_9;
}
}
lean_object* l_Lean_Elab_mkMessageCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_mkMessageCore(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_mkExceptionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = l_Lean_FileMap_toPosition(x_2, x_4);
x_6 = lean_box(0);
x_7 = 2;
x_8 = l_String_splitAux___main___closed__1;
x_9 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_8);
lean_ctor_set(x_9, 4, x_3);
lean_ctor_set_uint8(x_9, sizeof(void*)*5, x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_mkExceptionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_mkExceptionCore(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Init_System_IOError(lean_object*);
lean_object* initialize_Lean_Meta_Message(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Exception(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IOError(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Exception_inhabited___closed__1 = _init_l_Lean_Elab_Exception_inhabited___closed__1();
lean_mark_persistent(l_Lean_Elab_Exception_inhabited___closed__1);
l_Lean_Elab_Exception_inhabited = _init_l_Lean_Elab_Exception_inhabited();
lean_mark_persistent(l_Lean_Elab_Exception_inhabited);
l_Lean_Elab_Exception_hasToString___closed__1 = _init_l_Lean_Elab_Exception_hasToString___closed__1();
lean_mark_persistent(l_Lean_Elab_Exception_hasToString___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
