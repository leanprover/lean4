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
lean_object* l_Lean_Elab_logWarning___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_tracingAtPos(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logWarning(lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl(lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___boxed(lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimpleMonadTracerAdapter_getTraces___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_tracingAtPos___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorUsingCmdPos(lean_object*);
lean_object* l_Lean_Meta_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_logError(lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___rarg___closed__1;
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfoAt(lean_object*);
lean_object* l_Lean_Elab_getPosition___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___rarg___closed__2;
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg___lambda__1___closed__1;
lean_object* l_Lean_Elab_mkMessage___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_log___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Elab_logInfoAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow(lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___rarg___closed__4;
lean_object* l_Lean_Elab_logErrorAndThrow___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1(lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log(lean_object*);
lean_object* l_finally___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage(lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_tracingAt___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorUsingCmdPos___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_finally___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*);
lean_object* l_Lean_Elab_getPos(lean_object*);
lean_object* l_Lean_Elab_getPos___boxed(lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Char_HasRepr___closed__1;
lean_object* l_Lean_Elab_log___boxed(lean_object*);
lean_object* l_Lean_Elab_logInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPosition___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPos___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_logWarning___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logElabException(lean_object*);
lean_object* l_Lean_Elab_logError___boxed(lean_object*);
lean_object* l_Lean_Elab_logErrorUsingCmdPos___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getPosition___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_tracingAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logUnknownDecl___rarg___closed__3;
lean_object* l_fix1___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_tracingAt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfoAt___boxed(lean_object*);
lean_object* l_Lean_Elab_getPosition(lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___boxed(lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_tracingAtPos___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logWarning___boxed(lean_object*);
lean_object* l_Lean_Elab_logAt___boxed(lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfo___boxed(lean_object*);
lean_object* l_Lean_Elab_log___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_TraceState_Inhabited___closed__1;
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorUsingCmdPos___boxed(lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___boxed(lean_object*);
lean_object* l_Lean_Elab_logInfo(lean_object*);
lean_object* l_Lean_Elab_logAt(lean_object*);
lean_object* l_Lean_Elab_logElabException___boxed(lean_object*);
lean_object* l_Lean_Elab_logError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_tracingAtPos___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logElabException___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState(lean_object*);
extern lean_object* l_Lean_addClass___closed__1;
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___boxed(lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_tracingAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfo___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_finally___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAndThrow___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_mkMessage___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_getPosition___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt(lean_object*);
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
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_FileMap_toPosition(x_3, x_7);
x_12 = l_String_splitAux___main___closed__1;
x_13 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_6);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_5);
x_14 = lean_apply_2(x_9, lean_box(0), x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = l_Lean_FileMap_toPosition(x_3, x_15);
x_17 = l_String_splitAux___main___closed__1;
x_18 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_10);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set(x_18, 4, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*5, x_5);
x_19 = lean_apply_2(x_9, lean_box(0), x_18);
return x_19;
}
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessage___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_8);
lean_closure_set(x_11, 4, x_10);
lean_closure_set(x_11, 5, x_6);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_box(x_4);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessage___rarg___lambda__2___boxed), 8, 7);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_7);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_5);
lean_closure_set(x_10, 6, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_box(x_4);
lean_inc(x_6);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessage___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_8);
lean_closure_set(x_9, 4, x_3);
lean_closure_set(x_9, 5, x_6);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_mkMessage(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_mkMessage___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Elab_mkMessage___rarg___lambda__1(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_Elab_mkMessage___rarg___lambda__2(x_1, x_2, x_3, x_4, x_9, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Elab_mkMessage___rarg___lambda__3(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Elab_mkMessage___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_mkMessage___rarg(x_1, x_2, x_3, x_6, x_5);
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
lean_object* l_Lean_Elab_logAt___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Elab_logAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
lean_inc(x_2);
x_8 = l_Lean_Elab_mkMessage___rarg(x_1, x_2, x_5, x_4, x_7);
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
lean_object* l_Lean_Elab_logAt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logAt(x_1);
lean_dec(x_1);
return x_2;
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
lean_object* l_Lean_Elab_logInfoAt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logInfoAt(x_1);
lean_dec(x_1);
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
lean_object* l_Lean_Elab_log___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_1);
x_7 = l_Lean_Elab_getPos___rarg(x_1, x_2, x_3);
x_8 = lean_box(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_log___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_log(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_log___rarg___boxed), 5, 0);
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
lean_object* l_Lean_Elab_log___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_6, x_5);
lean_dec(x_3);
return x_7;
}
}
lean_object* l_Lean_Elab_log___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_log(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 2;
x_6 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
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
lean_object* l_Lean_Elab_logWarning___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_logWarning(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logWarning___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logWarning___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logWarning___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_logWarning___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logWarning(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logInfo___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_logInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logInfo___rarg___boxed), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logInfo___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_logInfo___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Lean_Elab_logInfo___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_logInfo(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logErrorUsingCmdPos___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 2;
x_6 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_4, x_5, x_3);
return x_6;
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
lean_object* l_Lean_Elab_logElabException___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_5, x_4);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_KernelException_toMessageData(x_7);
x_9 = l_Lean_Elab_logErrorUsingCmdPos___rarg(x_1, x_2, x_8);
return x_9;
}
case 3:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_Meta_Exception_toMessageData(x_10);
x_12 = l_Lean_Elab_logErrorUsingCmdPos___rarg(x_1, x_2, x_11);
return x_12;
}
case 5:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_14, lean_box(0), x_15);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = l_Lean_Elab_logErrorUsingCmdPos___rarg(x_1, x_2, x_19);
return x_20;
}
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
lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = 2;
x_9 = l_Lean_Elab_log___rarg(x_1, x_2, x_5, x_8, x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAndThrow___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_10, 0, x_4);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
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
lean_object* _init_l_Lean_Elab_logUnknownDecl___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addClass___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_logUnknownDecl___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logUnknownDecl___rarg___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_logUnknownDecl___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Char_HasRepr___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_logUnknownDecl___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logUnknownDecl___rarg___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logUnknownDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_5 = l_Lean_Name_toString___closed__1;
x_6 = l_Lean_Name_toStringWithSep___main(x_5, x_4);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Elab_logUnknownDecl___rarg___closed__2;
x_10 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Lean_Elab_logUnknownDecl___rarg___closed__4;
x_12 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 2;
x_14 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_13, x_12);
return x_14;
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
lean_object* _init_l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_TraceState_Inhabited___closed__1;
x_2 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg___lambda__1___closed__1;
x_7 = lean_apply_1(x_5, x_6);
x_8 = lean_alloc_closure((void*)(l_finally___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_4);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg___lambda__1), 4, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg), 2, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Log_1__resetTraceState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Log_1__resetTraceState(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_array_fget(x_4, x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc(x_14);
lean_dec(x_13);
x_15 = 0;
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_3, x_15, x_12);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_5, x_17);
x_19 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___rarg(x_1, x_2, x_3, x_4, x_18);
lean_dec(x_18);
x_20 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_16, x_19);
return x_20;
}
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_alloc_closure((void*)(l_fix1___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_2);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
}
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___rarg(x_1, x_2, x_3, x_7, x_8);
x_10 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_5);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_SimpleMonadTracerAdapter_getTraces___rarg___lambda__1), 2, 1);
lean_closure_set(x_8, 0, x_1);
lean_inc(x_6);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_8);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__2___boxed), 7, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_3);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
}
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_forMAux___main___at___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_tracingAtPos___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_9 = l___private_Init_Lean_Elab_Log_2__saveNewTraceAsMessagesAt___rarg(x_1, x_2, x_3, x_4, x_8);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_finally___rarg___lambda__2), 4, 3);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_6);
lean_closure_set(x_11, 2, x_9);
lean_inc(x_6);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_7, x_11);
x_13 = lean_alloc_closure((void*)(l_finally___rarg___lambda__4), 4, 3);
lean_closure_set(x_13, 0, x_5);
lean_closure_set(x_13, 1, x_6);
lean_closure_set(x_13, 2, x_9);
x_14 = lean_apply_3(x_10, lean_box(0), x_12, x_13);
return x_14;
}
}
lean_object* l_Lean_Elab_tracingAtPos___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_4);
lean_inc(x_1);
x_8 = l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg(x_1, x_4);
lean_inc(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_tracingAtPos___rarg___lambda__1), 8, 7);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_4);
lean_closure_set(x_9, 3, x_5);
lean_closure_set(x_9, 4, x_2);
lean_closure_set(x_9, 5, x_7);
lean_closure_set(x_9, 6, x_6);
x_10 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_tracingAtPos(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_tracingAtPos___rarg), 6, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_tracingAtPos___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_tracingAtPos(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_tracingAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Syntax_getPos(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_4);
lean_inc(x_1);
x_10 = l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg(x_1, x_4);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_tracingAtPos___rarg___lambda__1), 8, 7);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_3);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_8);
lean_closure_set(x_11, 4, x_2);
lean_closure_set(x_11, 5, x_9);
lean_closure_set(x_11, 6, x_6);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_10, x_11);
return x_12;
}
}
}
lean_object* l_Lean_Elab_tracingAt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_tracingAt___rarg___boxed), 6, 0);
return x_3;
}
}
lean_object* l_Lean_Elab_tracingAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_tracingAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_tracingAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_tracingAt(x_1, x_2);
lean_dec(x_2);
return x_3;
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
l_Lean_Elab_logUnknownDecl___rarg___closed__1 = _init_l_Lean_Elab_logUnknownDecl___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_logUnknownDecl___rarg___closed__1);
l_Lean_Elab_logUnknownDecl___rarg___closed__2 = _init_l_Lean_Elab_logUnknownDecl___rarg___closed__2();
lean_mark_persistent(l_Lean_Elab_logUnknownDecl___rarg___closed__2);
l_Lean_Elab_logUnknownDecl___rarg___closed__3 = _init_l_Lean_Elab_logUnknownDecl___rarg___closed__3();
lean_mark_persistent(l_Lean_Elab_logUnknownDecl___rarg___closed__3);
l_Lean_Elab_logUnknownDecl___rarg___closed__4 = _init_l_Lean_Elab_logUnknownDecl___rarg___closed__4();
lean_mark_persistent(l_Lean_Elab_logUnknownDecl___rarg___closed__4);
l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg___lambda__1___closed__1 = _init_l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg___lambda__1___closed__1();
lean_mark_persistent(l___private_Init_Lean_Elab_Log_1__resetTraceState___rarg___lambda__1___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
