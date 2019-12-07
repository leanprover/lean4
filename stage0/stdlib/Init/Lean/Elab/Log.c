// Lean compiler output
// Module: Init.Lean.Elab.Log
// Imports: Init.Lean.Elab.Util Init.Lean.Elab.Exception
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
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Elab_logUnknownDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPosition___boxed(lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___boxed(lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl(lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___boxed(lean_object*);
lean_object* l_Lean_Elab_logErrorAt___boxed(lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorUsingCmdPos(lean_object*);
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_logError(lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPosition___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_logErrorAndThrow(lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage(lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorUsingCmdPos___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logElabException___rarg___closed__2;
lean_object* l_Lean_Elab_getPos(lean_object*);
lean_object* l_Lean_Elab_getPos___boxed(lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_logElabException___rarg___closed__3;
lean_object* l_Lean_Elab_getPosition___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logElabException(lean_object*);
lean_object* l_Lean_Elab_logError___boxed(lean_object*);
lean_object* l_Lean_Elab_logErrorUsingCmdPos___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPosition___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPosition(lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l_Lean_Elab_logErrorUsingCmdPos___boxed(lean_object*);
lean_object* l_Lean_Elab_logElabException___boxed(lean_object*);
lean_object* l_Lean_Elab_logErrorAt___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logElabException___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
extern lean_object* l_Lean_addClass___closed__1;
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logElabException___rarg___closed__1;
lean_object* l_Lean_Elab_logErrorAndThrow___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPosition___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAt(lean_object*);
lean_object* l_Lean_Elab_getPosition___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_FileMap_toPosition(x_3, x_4);
x_8 = lean_apply_2(x_6, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_FileMap_toPosition(x_3, x_11);
x_13 = lean_apply_2(x_10, lean_box(0), x_12);
return x_13;
}
}
}
lean_object* l_Lean_Elab_getPosition___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_getPosition___rarg___lambda__1___boxed), 4, 3);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_3);
lean_closure_set(x_7, 2, x_5);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_getPosition___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_getPosition___rarg___lambda__2), 5, 4);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_getPosition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getPosition___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getPosition___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_getPosition___rarg___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* l_Lean_Elab_getPosition___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_getPosition(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_FileMap_toPosition(x_3, x_6);
x_11 = 2;
x_12 = l_String_splitAux___main___closed__1;
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_5);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
x_14 = lean_apply_2(x_8, lean_box(0), x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = l_Lean_FileMap_toPosition(x_3, x_15);
x_17 = 2;
x_18 = l_String_splitAux___main___closed__1;
x_19 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_9);
lean_ctor_set(x_19, 3, x_18);
lean_ctor_set(x_19, 4, x_5);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_17);
x_20 = lean_apply_2(x_8, lean_box(0), x_19);
return x_20;
}
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessage___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_4);
lean_closure_set(x_9, 3, x_7);
lean_closure_set(x_9, 4, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessage___rarg___lambda__2), 7, 6);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_6);
lean_closure_set(x_8, 4, x_4);
lean_closure_set(x_8, 5, x_5);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessage___rarg___lambda__3), 6, 5);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_5);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_mkMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessage___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_mkMessage___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_mkMessage___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_mkMessage(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logErrorAt___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_logErrorAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
lean_inc(x_2);
x_9 = l_Lean_Elab_mkMessage___rarg(x_1, x_2, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAt___rarg___lambda__1), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_logErrorAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAt___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logErrorAt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logErrorAt(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logErrorUsingCmdPos___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logErrorAt___rarg(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_logErrorUsingCmdPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorUsingCmdPos___rarg___lambda__1), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_logErrorUsingCmdPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorUsingCmdPos___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logErrorUsingCmdPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logErrorUsingCmdPos(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_getPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Syntax_getPos(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_apply_2(x_8, lean_box(0), x_6);
return x_9;
}
}
}
lean_object* l_Lean_Elab_getPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_getPos___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_getPos___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_getPos___rarg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_getPos___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_getPos(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_Elab_getPos___rarg(x_1, x_2, x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorUsingCmdPos___rarg___lambda__1), 4, 3);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_logError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logError___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logError___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_logError___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logError(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_logElabException___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("kernel exception");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_logElabException___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logElabException___rarg___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_logElabException___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logElabException___rarg___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logElabException___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_1(x_13, x_12);
return x_14;
}
case 2:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
lean_dec(x_3);
if (lean_obj_tag(x_15) == 11)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_box(0);
lean_inc(x_2);
x_21 = l_Lean_Elab_mkMessage___rarg(x_1, x_2, x_19, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAt___rarg___lambda__1), 2, 1);
lean_closure_set(x_22, 0, x_2);
x_23 = lean_apply_4(x_17, lean_box(0), lean_box(0), x_21, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_15);
x_24 = lean_box(0);
x_4 = x_24;
goto block_11;
}
}
case 3:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = l_Lean_Meta_Exception_toMessageData(x_25);
x_28 = lean_box(0);
lean_inc(x_2);
x_29 = l_Lean_Elab_mkMessage___rarg(x_1, x_2, x_27, x_28);
x_30 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAt___rarg___lambda__1), 2, 1);
lean_closure_set(x_30, 0, x_2);
x_31 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_29, x_30);
return x_31;
}
case 5:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_2);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = lean_apply_2(x_33, lean_box(0), x_34);
return x_35;
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_3, 0);
lean_inc(x_36);
lean_dec(x_3);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_38, 0, x_36);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_box(0);
lean_inc(x_2);
x_41 = l_Lean_Elab_mkMessage___rarg(x_1, x_2, x_39, x_40);
x_42 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAt___rarg___lambda__1), 2, 1);
lean_closure_set(x_42, 0, x_2);
x_43 = lean_apply_4(x_37, lean_box(0), lean_box(0), x_41, x_42);
return x_43;
}
}
block_11:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l_Lean_Elab_logElabException___rarg___closed__3;
lean_inc(x_2);
x_8 = l_Lean_Elab_mkMessage___rarg(x_1, x_2, x_7, x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAt___rarg___lambda__1), 2, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Elab_logElabException(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logElabException___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logElabException___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logElabException(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logErrorAndThrow___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(5);
x_5 = lean_apply_2(x_3, lean_box(0), x_4);
return x_5;
}
}
lean_object* l_Lean_Elab_logErrorAndThrow___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = l_Lean_Elab_logError___rarg(x_1, x_2, x_5, x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAndThrow___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_logErrorAndThrow(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAndThrow___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logErrorAndThrow___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_logErrorAndThrow___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_logErrorAndThrow___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_logErrorAndThrow___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_logErrorAndThrow___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logErrorAndThrow(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logUnknownDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_4);
x_7 = l_Lean_addClass___closed__1;
x_8 = lean_string_append(x_7, x_6);
lean_dec(x_6);
x_9 = l_Char_HasRepr___closed__1;
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Lean_Elab_logError___rarg(x_1, x_2, x_3, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_logUnknownDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logUnknownDecl___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logUnknownDecl___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logUnknownDecl___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_logUnknownDecl___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logUnknownDecl(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Lean_Elab_Util(lean_object*);
lean_object* initialize_Init_Lean_Elab_Exception(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_Log(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Exception(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_logElabException___rarg___closed__1 = _init_l_Lean_Elab_logElabException___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_logElabException___rarg___closed__1);
l_Lean_Elab_logElabException___rarg___closed__2 = _init_l_Lean_Elab_logElabException___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_logElabException___rarg___closed__2);
l_Lean_Elab_logElabException___rarg___closed__3 = _init_l_Lean_Elab_logElabException___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_logElabException___rarg___closed__3);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
