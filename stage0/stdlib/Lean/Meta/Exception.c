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
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__11;
extern lean_object* l_Lean_Format_flatten___main___closed__1;
lean_object* l_Lean_Core_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Meta_Exception_Inhabited___closed__1;
lean_object* l_Lean_Meta_Exception_Inhabited;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__10;
lean_object* l_Lean_Meta_Exception_getRef(lean_object*);
lean_object* l_Lean_Meta_EIOEx_monadIO(lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__9;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__8;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__4;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__3;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__7;
lean_object* l_Lean_Meta_Exception_getRef___boxed(lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__5;
extern lean_object* l_Lean_Core_Exception_inhabited___closed__1;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__12;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__6;
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__2;
lean_object* l_Lean_Meta_Exception_mkCtx(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData(lean_object*);
lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__1;
lean_object* l_Lean_Meta_EIOEx_monadIO___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_EIOEx_monadIO___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_12);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
}
lean_object* l_Lean_Meta_EIOEx_monadIO(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_EIOEx_monadIO___rarg), 2, 0);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Core_Exception_inhabited___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
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
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
}
else
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
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
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isLevelDefEqStuck");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__2;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Format_flatten___main___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__3;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" =?= ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("isExprDefEqStuck");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__10;
x_2 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_Exception_toTraceMessageData___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Exception_toTraceMessageData___closed__11;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__4;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_Exception_toTraceMessageData(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l_Lean_Meta_Exception_toTraceMessageData___closed__5;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Meta_Exception_toTraceMessageData___closed__8;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = l_Lean_Meta_Exception_toTraceMessageData___closed__12;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_Exception_toTraceMessageData___closed__8;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_14);
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_Core_Exception_toMessageData(x_24);
return x_25;
}
}
}
}
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = l_Lean_Meta_Exception_toTraceMessageData___closed__5;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Meta_Exception_toTraceMessageData___closed__8;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_17 = l_Lean_Meta_Exception_toTraceMessageData___closed__12;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Lean_Meta_Exception_toTraceMessageData___closed__8;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_14);
x_22 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
default: 
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l_Lean_Core_Exception_toMessageData(x_24);
return x_25;
}
}
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
l_Lean_Meta_Exception_toTraceMessageData___closed__1 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__1();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__1);
l_Lean_Meta_Exception_toTraceMessageData___closed__2 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__2();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__2);
l_Lean_Meta_Exception_toTraceMessageData___closed__3 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__3();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__3);
l_Lean_Meta_Exception_toTraceMessageData___closed__4 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__4();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__4);
l_Lean_Meta_Exception_toTraceMessageData___closed__5 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__5();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__5);
l_Lean_Meta_Exception_toTraceMessageData___closed__6 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__6();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__6);
l_Lean_Meta_Exception_toTraceMessageData___closed__7 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__7();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__7);
l_Lean_Meta_Exception_toTraceMessageData___closed__8 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__8();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__8);
l_Lean_Meta_Exception_toTraceMessageData___closed__9 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__9();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__9);
l_Lean_Meta_Exception_toTraceMessageData___closed__10 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__10();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__10);
l_Lean_Meta_Exception_toTraceMessageData___closed__11 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__11();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__11);
l_Lean_Meta_Exception_toTraceMessageData___closed__12 = _init_l_Lean_Meta_Exception_toTraceMessageData___closed__12();
lean_mark_persistent(l_Lean_Meta_Exception_toTraceMessageData___closed__12);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
