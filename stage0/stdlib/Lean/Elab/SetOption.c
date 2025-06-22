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
lean_object* l_IO_toEIO(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addCompletionInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_KVMap_insertCore(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1;
static lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__5;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_isStrLit_x3f(lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2;
lean_object* l_Lean_Syntax_setArgs(lean_object*, lean_object*);
lean_object* l_Lean_Elab_pushInfoLeaf___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_DataValue_sameCtor(lean_object*, lean_object*);
lean_object* l_Lean_getOptionDecl(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4;
static lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_Syntax_isNatLit_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_KVMap_insertCore(x_4, x_1, x_2);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_4(x_1, lean_box(0), lean_box(0), x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type mismatch at set_option", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption_setOption___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption_setOption___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption_setOption___redArg___lam__0), 4, 3);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_9);
x_12 = l_Lean_DataValue_sameCtor(x_10, x_6);
lean_dec(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_inc(x_8);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption_setOption___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_13, 0, x_8);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_11);
x_14 = l_Lean_Elab_elabSetOption_setOption___redArg___closed__1;
x_15 = l_Lean_throwError___redArg(x_1, x_3, x_14);
x_16 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_15, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_8);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption_setOption___redArg___lam__1___boxed), 4, 3);
lean_closure_set(x_17, 0, x_8);
lean_closure_set(x_17, 1, x_2);
lean_closure_set(x_17, 2, x_11);
x_18 = lean_box(0);
x_19 = lean_apply_2(x_9, lean_box(0), x_18);
x_20 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_19, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_elabSetOption_setOption___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_elabSetOption_setOption___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_elabSetOption_setOption___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption_setOption___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_elabSetOption_setOption(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected set_option value ", 28, 28);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Syntax_isStrLit_x3f(x_1);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = l_Lean_Syntax_isNatLit_x3f(x_1);
if (lean_obj_tag(x_16) == 0)
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4;
x_19 = lean_string_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Elab_elabSetOption___redArg___lam__1___closed__5;
x_21 = lean_string_dec_eq(x_17, x_20);
lean_dec(x_17);
if (x_21 == 0)
{
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_22, 0, x_19);
x_23 = l_Lean_Elab_elabSetOption_setOption___redArg(x_2, x_4, x_3, x_5, x_6, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_17);
lean_dec(x_1);
x_24 = lean_alloc_ctor(1, 0, 1);
lean_ctor_set_uint8(x_24, 0, x_19);
x_25 = l_Lean_Elab_elabSetOption_setOption___redArg(x_2, x_4, x_3, x_5, x_6, x_24);
return x_25;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
}
else
{
uint8_t x_26; 
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
lean_object* x_27; 
lean_ctor_set_tag(x_16, 3);
x_27 = l_Lean_Elab_elabSetOption_setOption___redArg(x_2, x_4, x_3, x_5, x_6, x_16);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
lean_inc(x_28);
lean_dec(x_16);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = l_Lean_Elab_elabSetOption_setOption___redArg(x_2, x_4, x_3, x_5, x_6, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
lean_object* x_32; 
lean_ctor_set_tag(x_15, 0);
x_32 = l_Lean_Elab_elabSetOption_setOption___redArg(x_2, x_4, x_3, x_5, x_6, x_15);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Elab_elabSetOption_setOption___redArg(x_2, x_4, x_3, x_5, x_6, x_34);
return x_35;
}
}
block_14:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1;
x_9 = l_Lean_MessageData_ofSyntax(x_1);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3;
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___redArg(x_2, x_3, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__1___boxed), 7, 6);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_10);
x_13 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = l_Lean_Elab_pushInfoLeaf___redArg(x_2, x_7, x_13);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_14, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = l_Lean_Syntax_getId(x_1);
x_12 = lean_erase_macro_scopes(x_11);
lean_inc(x_7);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__2), 9, 8);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_3);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_12);
lean_closure_set(x_13, 5, x_1);
lean_closure_set(x_13, 6, x_6);
lean_closure_set(x_13, 7, x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_getOptionDecl), 2, 1);
lean_closure_set(x_14, 0, x_12);
x_15 = lean_alloc_closure((void*)(l_IO_toEIO), 5, 4);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, lean_box(0));
lean_closure_set(x_15, 2, x_8);
lean_closure_set(x_15, 3, x_14);
x_16 = lean_apply_2(x_9, lean_box(0), x_15);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__3___boxed), 10, 9);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
lean_closure_set(x_11, 5, x_6);
lean_closure_set(x_11, 6, x_7);
lean_closure_set(x_11, 7, x_10);
lean_closure_set(x_11, 8, x_8);
x_12 = l_Lean_Syntax_getArgs(x_9);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_unsigned_to_nat(3u);
x_15 = l_Array_toSubarray___redArg(x_12, x_13, x_14);
x_16 = l_Array_ofSubarray___redArg(x_15);
lean_dec(x_15);
x_17 = l_Lean_Syntax_setArgs(x_9, x_16);
x_18 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Elab_addCompletionInfo___redArg(x_3, x_6, x_18);
x_20 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_19, x_11);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_elabSetOption___redArg___lam__4), 9, 8);
lean_closure_set(x_11, 0, x_6);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_1);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_2);
lean_closure_set(x_11, 5, x_5);
lean_closure_set(x_11, 6, x_9);
lean_closure_set(x_11, 7, x_4);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_elabSetOption___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_elabSetOption___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_elabSetOption___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_elabSetOption___redArg___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
l_Lean_Elab_elabSetOption_setOption___redArg___closed__0 = _init_l_Lean_Elab_elabSetOption_setOption___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___redArg___closed__0);
l_Lean_Elab_elabSetOption_setOption___redArg___closed__1 = _init_l_Lean_Elab_elabSetOption_setOption___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption_setOption___redArg___closed__1);
l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0 = _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0();
lean_mark_persistent(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__0);
l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1 = _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1();
lean_mark_persistent(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__1);
l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2 = _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2();
lean_mark_persistent(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__2);
l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3 = _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3();
lean_mark_persistent(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__3);
l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4 = _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4();
lean_mark_persistent(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__4);
l_Lean_Elab_elabSetOption___redArg___lam__1___closed__5 = _init_l_Lean_Elab_elabSetOption___redArg___lam__1___closed__5();
lean_mark_persistent(l_Lean_Elab_elabSetOption___redArg___lam__1___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
