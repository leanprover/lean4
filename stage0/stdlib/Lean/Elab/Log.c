// Lean compiler output
// Module: Lean.Elab.Log
// Imports: Init Lean.Elab.Util Lean.Elab.Exception
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
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logWarning(lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError(lean_object*);
lean_object* l_Lean_Elab_log___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logError(lean_object*);
lean_object* l_Lean_Core_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfoAt(lean_object*);
lean_object* l_Lean_Elab_log___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_logInfoAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_throwError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log(lean_object*);
lean_object* l_Lean_Elab_mkMessage(lean_object*);
lean_object* l_Lean_Elab_getRefPos___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_getRefPosition(lean_object*);
lean_object* l_Lean_Elab_logInfo___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_getRefPosition___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___rarg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_logWarning___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt(lean_object*);
lean_object* l_Lean_Elab_throwError___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos(lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_log___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfo(lean_object*);
lean_object* l_Lean_Elab_logAt(lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessageAt___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_logError___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_replaceRef(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Core_replaceRef(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_replaceRef___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_replaceRef(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Elab_getRefPos___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_Syntax_getPos(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_apply_2(x_4, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_2(x_4, lean_box(0), x_8);
return x_9;
}
}
}
lean_object* l_Lean_Elab_getRefPos___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_getRefPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPos___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getRefPos___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_getRefPos___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_FileMap_toPosition(x_3, x_2);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPosition___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_getRefPosition___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Elab_getRefPos___rarg(x_1, x_2);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPosition___rarg___lambda__2), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_getRefPosition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPosition___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getRefPosition___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_String_splitAux___main___closed__1;
x_10 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_ctor_set(x_10, 4, x_5);
lean_ctor_set_uint8(x_10, sizeof(void*)*5, x_4);
x_11 = lean_apply_2(x_7, lean_box(0), x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_FileMap_toPosition(x_1, x_2);
x_10 = lean_ctor_get(x_3, 3);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_apply_1(x_10, x_4);
x_12 = lean_box(x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessageAt___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_8);
lean_closure_set(x_13, 2, x_9);
lean_closure_set(x_13, 3, x_12);
x_14 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_box(x_5);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessageAt___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_1);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_4);
lean_closure_set(x_10, 5, x_9);
lean_closure_set(x_10, 6, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_mkMessageAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_box(x_4);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessageAt___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_5);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_1);
lean_closure_set(x_9, 4, x_8);
lean_closure_set(x_9, 5, x_6);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_mkMessageAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessageAt___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_mkMessageAt___rarg___lambda__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_Elab_mkMessageAt___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Elab_mkMessageAt___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Elab_mkMessageAt___rarg___lambda__3(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Elab_mkMessageAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_mkMessageAt___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_6 = l_Lean_Elab_getRefPos___rarg(x_1, x_2);
x_7 = lean_box(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessageAt___rarg___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_mkMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessage___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Lean_Elab_mkMessage___rarg(x_1, x_2, x_3, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_logAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = l_Lean_Elab_mkMessageAt___rarg(x_1, x_7, x_5, x_4, x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___lambda__1), 2, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_logAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_logInfoAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_logInfoAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logInfoAt___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_log___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_log___rarg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_inc(x_1);
x_7 = l_Lean_Elab_getRefPos___rarg(x_1, x_6);
x_8 = lean_box(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_log___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_4);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_log(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_log___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_log___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_log___rarg___lambda__1(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_log___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Elab_log___rarg(x_1, x_2, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_logError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 2;
x_5 = l_Lean_Elab_log___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_logError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logError___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logWarning___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 1;
x_5 = l_Lean_Elab_log___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_logWarning(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logWarning___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logInfo___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = l_Lean_Elab_log___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_logInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logInfo___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_throwError___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_2);
x_6 = lean_apply_2(x_4, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_throwError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_throwError___rarg___lambda__1), 3, 2);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_throwError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_throwError___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Util(lean_object*);
lean_object* initialize_Lean_Elab_Exception(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Log(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
