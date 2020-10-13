// Lean compiler output
// Module: Lean.Compiler.IR.UnboxResult
// Imports: Init Lean.Data.Format Lean.Compiler.IR.Basic
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
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr(lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6;
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5;
extern lean_object* l_Lean_TagAttribute_Inhabited___closed__1;
lean_object* l_Lean_getConstInfo___at_Lean_IR_UnboxResult_mkUnboxAttr___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_unboxAttr;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3;
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__5;
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_getConstInfo___at_Lean_IR_UnboxResult_mkUnboxAttr___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_hasUnboxAttr___boxed(lean_object*, lean_object*);
uint8_t l_Lean_IR_UnboxResult_hasUnboxAttr(lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1;
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3;
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2;
lean_object* l_Lean_getConstInfo___at_Lean_IR_UnboxResult_mkUnboxAttr___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_environment_find(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_free_object(x_6);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_16, x_2, x_3, x_4, x_9);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
lean_ctor_set(x_6, 0, x_18);
return x_6;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_6, 0);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_6);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_1);
x_22 = lean_environment_find(x_21, x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_1);
x_24 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_25 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_throwUnknownConstant___rarg___closed__5;
x_27 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_27, x_2, x_3, x_4, x_20);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_20);
return x_30;
}
}
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("constant must be an inductive type");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("recursive inductive datatypes are not supported");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfo___at_Lean_IR_UnboxResult_mkUnboxAttr___spec__1(x_1, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*5);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_6, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_6, 0, x_12);
return x_6;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6;
x_18 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_17, x_2, x_3, x_4, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3;
x_21 = l_Lean_throwError___at_Lean_addAttribute___spec__2___rarg(x_20, x_2, x_3, x_4, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("unbox");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("compiler tries to unbox result values if their types are tagged with `[unbox]`");
return x_1;
}
}
static lean_object* _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___boxed), 5, 0);
return x_1;
}
}
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2;
x_3 = l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3;
x_4 = l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4;
x_5 = l_Lean_registerTagAttribute(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_getConstInfo___at_Lean_IR_UnboxResult_mkUnboxAttr___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfo___at_Lean_IR_UnboxResult_mkUnboxAttr___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
uint8_t l_Lean_IR_UnboxResult_hasUnboxAttr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_IR_UnboxResult_unboxAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_IR_UnboxResult_hasUnboxAttr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_UnboxResult_hasUnboxAttr(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Format(lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_IR_UnboxResult(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__1);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__2);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__3);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__4);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__5);
l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___lambda__1___closed__6);
l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___closed__1);
l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___closed__2);
l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___closed__3);
l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4 = _init_l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4();
lean_mark_persistent(l_Lean_IR_UnboxResult_mkUnboxAttr___closed__4);
res = l_Lean_IR_UnboxResult_mkUnboxAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_IR_UnboxResult_unboxAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_IR_UnboxResult_unboxAttr);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
