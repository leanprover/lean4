// Lean compiler output
// Module: Lean.Elab.SetOption
// Imports: Lean.Log Lean.Elab.InfoTree
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
static lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__4;
static lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addCompletionInfo___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
static lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___closed__2;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__2;
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
static lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___closed__1;
lean_object* l_IO_toEIO___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__1;
lean_object* l_Lean_throwError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___rarg(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__7;
static lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_KVMap_insertCore(x_4, x_2, x_3);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption_setOption___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type mismatch at set_option", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption_setOption___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_6);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption_setOption___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_4);
lean_closure_set(x_7, 2, x_6);
lean_closure_set(x_7, 3, x_2);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_DataValue_sameCtor(x_8, x_6);
lean_dec(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Lean_Elab_elabSetOption_setOption___rarg___closed__2;
x_12 = l_Lean_throwError___rarg(x_1, x_3, x_11);
x_13 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_12, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_16, lean_box(0), x_17);
x_19 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_18, x_7);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption_setOption___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_elabSetOption_setOption___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabSetOption_setOption___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_io_error_to_string(x_2);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_MessageData_ofFormat(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected set_option value ", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = l_Lean_Syntax_isNatLit_x3f(x_1);
if (lean_obj_tag(x_9) == 0)
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__5;
x_12 = lean_string_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__6;
x_14 = lean_string_dec_eq(x_10, x_13);
lean_dec(x_10);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_5);
lean_dec(x_4);
lean_inc(x_1);
x_15 = l_Lean_MessageData_ofSyntax(x_1);
x_16 = !lean_is_exclusive(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_1, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_1, 0);
lean_dec(x_18);
x_19 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__2;
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_19);
x_20 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__4;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___rarg(x_2, x_3, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_23 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__2;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_15);
x_25 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___rarg(x_2, x_3, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__7;
x_29 = l_Lean_Elab_elabSetOption_setOption___rarg(x_2, x_4, x_3, x_5, x_6, x_28);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_1);
x_30 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__8;
x_31 = l_Lean_Elab_elabSetOption_setOption___rarg(x_2, x_4, x_3, x_5, x_6, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_5);
lean_dec(x_4);
x_32 = l_Lean_MessageData_ofSyntax(x_1);
x_33 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__2;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__4;
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___rarg(x_2, x_3, x_36);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_9);
if (x_38 == 0)
{
lean_object* x_39; 
lean_ctor_set_tag(x_9, 3);
x_39 = l_Lean_Elab_elabSetOption_setOption___rarg(x_2, x_4, x_3, x_5, x_6, x_9);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
lean_inc(x_40);
lean_dec(x_9);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_Elab_elabSetOption_setOption___rarg(x_2, x_4, x_3, x_5, x_6, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_8);
if (x_43 == 0)
{
lean_object* x_44; 
lean_ctor_set_tag(x_8, 0);
x_44 = l_Lean_Elab_elabSetOption_setOption___rarg(x_2, x_4, x_3, x_5, x_6, x_8);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
lean_inc(x_45);
lean_dec(x_8);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = l_Lean_Elab_elabSetOption_setOption___rarg(x_2, x_4, x_3, x_5, x_6, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc(x_2);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_10);
x_12 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_3);
x_13 = l_Lean_Elab_pushInfoLeaf___rarg(x_3, x_4, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_14, 0, x_5);
lean_closure_set(x_14, 1, x_3);
lean_closure_set(x_14, 2, x_6);
lean_closure_set(x_14, 3, x_7);
lean_closure_set(x_14, 4, x_2);
lean_closure_set(x_14, 5, x_9);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l_Lean_Syntax_getId(x_1);
x_12 = lean_erase_macro_scopes(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___rarg___lambda__1), 2, 1);
lean_closure_set(x_13, 0, x_2);
lean_inc(x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_getOptionDecl), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_alloc_closure((void*)(l_IO_toEIO___rarg), 3, 2);
lean_closure_set(x_15, 0, x_13);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_apply_2(x_3, lean_box(0), x_15);
lean_inc(x_9);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___rarg___lambda__3), 9, 8);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_4);
lean_closure_set(x_17, 3, x_5);
lean_closure_set(x_17, 4, x_6);
lean_closure_set(x_17, 5, x_7);
lean_closure_set(x_17, 6, x_8);
lean_closure_set(x_17, 7, x_9);
x_18 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_16, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = l_Lean_Syntax_getArgs(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Array_toSubarray___rarg(x_10, x_11, x_12);
x_14 = l_Array_ofSubarray___rarg(x_13);
lean_dec(x_13);
lean_inc(x_9);
x_15 = l_Lean_Syntax_setArgs(x_9, x_14);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_Elab_addCompletionInfo___rarg(x_1, x_2, x_16);
lean_inc(x_8);
x_18 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___rarg___lambda__4___boxed), 10, 9);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_9);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_1);
lean_closure_set(x_18, 4, x_2);
lean_closure_set(x_18, 5, x_5);
lean_closure_set(x_18, 6, x_6);
lean_closure_set(x_18, 7, x_7);
lean_closure_set(x_18, 8, x_8);
x_19 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___rarg___lambda__5), 9, 8);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_5);
lean_closure_set(x_11, 2, x_6);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_7);
lean_closure_set(x_11, 5, x_3);
lean_closure_set(x_11, 6, x_2);
lean_closure_set(x_11, 7, x_8);
x_12 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_elabSetOption___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_elabSetOption___rarg___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
lean_object* initialize_Lean_Log(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_InfoTree(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_SetOption(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Log(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_InfoTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_elabSetOption_setOption___rarg___closed__1 = _init_l_Lean_Elab_elabSetOption_setOption___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___rarg___closed__1);
l_Lean_Elab_elabSetOption_setOption___rarg___closed__2 = _init_l_Lean_Elab_elabSetOption_setOption___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___rarg___closed__2);
l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__1 = _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__1);
l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__2 = _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__2);
l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__3 = _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__3);
l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__4 = _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__4);
l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__5 = _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__5);
l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__6 = _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__6);
l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__7 = _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__7);
l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__8 = _init_l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Elab_elabSetOption___rarg___lambda__2___closed__8);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
