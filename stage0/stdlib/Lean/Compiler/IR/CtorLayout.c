// Lean compiler output
// Module: Lean.Compiler.IR.CtorLayout
// Imports: Lean.Environment Lean.Compiler.IR.Format
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
LEAN_EXPORT lean_object* l_Lean_IR_CtorFieldInfo_format(lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__2;
LEAN_EXPORT lean_object* l_Lean_IR_instInhabitedCtorFieldInfo;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__4;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__3;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__11;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__9;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__14;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__12;
lean_object* l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__1;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__10;
lean_object* lean_ir_get_ctor_layout(lean_object*, lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__7;
LEAN_EXPORT lean_object* l_Lean_IR_CtorFieldInfo_instToFormat;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__13;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__8;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__6;
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* l_Lean_IR_CtorFieldInfo_instToFormat___closed__1;
static lean_object* l_Lean_IR_CtorFieldInfo_format___closed__5;
static lean_object* _init_l_Lean_IR_instInhabitedCtorFieldInfo() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("◾", 3, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__1;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("obj@", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("usize@", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__7;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("scalar#", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("@", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_format___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_IR_CtorFieldInfo_format___closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_CtorFieldInfo_format(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_Lean_IR_CtorFieldInfo_format___closed__2;
return x_2;
}
case 1:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_5);
x_6 = l_Lean_IR_CtorFieldInfo_format___closed__4;
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
x_8 = l_Lean_IR_CtorFieldInfo_format___closed__6;
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l___private_Init_Data_Repr_0__Nat_reprFast(x_10);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_IR_CtorFieldInfo_format___closed__4;
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_IR_CtorFieldInfo_format___closed__6;
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = l___private_Init_Data_Repr_0__Nat_reprFast(x_18);
lean_ctor_set_tag(x_1, 3);
lean_ctor_set(x_1, 0, x_19);
x_20 = l_Lean_IR_CtorFieldInfo_format___closed__8;
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
x_22 = l_Lean_IR_CtorFieldInfo_format___closed__6;
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = l___private_Init_Data_Repr_0__Nat_reprFast(x_24);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = l_Lean_IR_CtorFieldInfo_format___closed__8;
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_IR_CtorFieldInfo_format___closed__6;
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
lean_dec(x_1);
x_34 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = l_Lean_IR_CtorFieldInfo_format___closed__10;
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_38 = l_Lean_IR_CtorFieldInfo_format___closed__12;
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l___private_Init_Data_Repr_0__Nat_reprFast(x_32);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_IR_CtorFieldInfo_format___closed__14;
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l___private_Lean_Compiler_IR_Format_0__Lean_IR_formatIRType(x_33);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_IR_CtorFieldInfo_format___closed__6;
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_instToFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_CtorFieldInfo_format), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_IR_CtorFieldInfo_instToFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_CtorFieldInfo_instToFormat___closed__1;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_getCtorLayout___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ir_get_ctor_layout(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Format(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_CtorLayout(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_instInhabitedCtorFieldInfo = _init_l_Lean_IR_instInhabitedCtorFieldInfo();
lean_mark_persistent(l_Lean_IR_instInhabitedCtorFieldInfo);
l_Lean_IR_CtorFieldInfo_format___closed__1 = _init_l_Lean_IR_CtorFieldInfo_format___closed__1();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__1);
l_Lean_IR_CtorFieldInfo_format___closed__2 = _init_l_Lean_IR_CtorFieldInfo_format___closed__2();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__2);
l_Lean_IR_CtorFieldInfo_format___closed__3 = _init_l_Lean_IR_CtorFieldInfo_format___closed__3();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__3);
l_Lean_IR_CtorFieldInfo_format___closed__4 = _init_l_Lean_IR_CtorFieldInfo_format___closed__4();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__4);
l_Lean_IR_CtorFieldInfo_format___closed__5 = _init_l_Lean_IR_CtorFieldInfo_format___closed__5();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__5);
l_Lean_IR_CtorFieldInfo_format___closed__6 = _init_l_Lean_IR_CtorFieldInfo_format___closed__6();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__6);
l_Lean_IR_CtorFieldInfo_format___closed__7 = _init_l_Lean_IR_CtorFieldInfo_format___closed__7();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__7);
l_Lean_IR_CtorFieldInfo_format___closed__8 = _init_l_Lean_IR_CtorFieldInfo_format___closed__8();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__8);
l_Lean_IR_CtorFieldInfo_format___closed__9 = _init_l_Lean_IR_CtorFieldInfo_format___closed__9();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__9);
l_Lean_IR_CtorFieldInfo_format___closed__10 = _init_l_Lean_IR_CtorFieldInfo_format___closed__10();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__10);
l_Lean_IR_CtorFieldInfo_format___closed__11 = _init_l_Lean_IR_CtorFieldInfo_format___closed__11();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__11);
l_Lean_IR_CtorFieldInfo_format___closed__12 = _init_l_Lean_IR_CtorFieldInfo_format___closed__12();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__12);
l_Lean_IR_CtorFieldInfo_format___closed__13 = _init_l_Lean_IR_CtorFieldInfo_format___closed__13();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__13);
l_Lean_IR_CtorFieldInfo_format___closed__14 = _init_l_Lean_IR_CtorFieldInfo_format___closed__14();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_format___closed__14);
l_Lean_IR_CtorFieldInfo_instToFormat___closed__1 = _init_l_Lean_IR_CtorFieldInfo_instToFormat___closed__1();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_instToFormat___closed__1);
l_Lean_IR_CtorFieldInfo_instToFormat = _init_l_Lean_IR_CtorFieldInfo_instToFormat();
lean_mark_persistent(l_Lean_IR_CtorFieldInfo_instToFormat);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
