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
lean_object* l_Lean_Elab_logException_match__1(lean_object*);
lean_object* l_Lean_Elab_getRefPos___rarg___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logWarning(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_logDbgTrace___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logError(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedParserDescr___closed__1;
lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__3;
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_508____closed__3;
lean_object* l_Lean_Elab_logInfoAt(lean_object*);
lean_object* l_Lean_Elab_logTrace(lean_object*);
lean_object* l_Lean_Elab_log___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__2;
lean_object* l_Lean_Elab_logDbgTrace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfoAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___rarg___lambda__1___closed__1;
lean_object* l_Lean_Elab_logException(lean_object*);
lean_object* l_Lean_Elab_instMonadLog___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logDbgTrace___rarg___closed__1;
lean_object* l_Lean_Elab_instMonadLog___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_trace___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___rarg___lambda__1(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPosition(lean_object*);
lean_object* l_Lean_Elab_logWarningAt(lean_object*);
lean_object* l_Lean_Elab_logInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_trace___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_logAt___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_instMonadLog(lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPosition___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_log___rarg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_logWarning___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logDbgTrace(lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_trace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_839____closed__1;
lean_object* l_Lean_Elab_getRefPos(lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logAt___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos(lean_object*);
extern lean_object* l_Lean_Elab_abortExceptionId;
lean_object* l_Lean_Elab_log___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_trace(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logException___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logInfo(lean_object*);
lean_object* l_Lean_Elab_logAt(lean_object*);
lean_object* l_Lean_Elab_logWarningAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPos___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_logTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logDbgTrace___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_logErrorAt(lean_object*);
lean_object* l_Lean_Elab_instMonadLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 3);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_instMonadLog___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_apply_2(x_2, lean_box(0), x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_inc(x_2);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_2);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadLog___rarg___lambda__1), 3, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_instMonadLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Elab_instMonadLog___rarg), 2, 0);
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
x_4 = lean_ctor_get(x_2, 0);
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
x_6 = l_Lean_FileMap_toPosition(x_2, x_3);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_getRefPosition___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_5 = l_Lean_Elab_getRefPos___rarg(x_1, x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPosition___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
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
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_getRefPosition___rarg___lambda__2), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
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
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_FileMap_toPosition(x_2, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_instInhabitedParserDescr___closed__1;
x_11 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_4);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_3);
x_12 = lean_apply_1(x_6, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = lean_box(x_4);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_FileMap_toPosition(x_2, x_3);
x_9 = lean_box(0);
x_10 = l_Lean_instInhabitedParserDescr___closed__1;
x_11 = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
lean_ctor_set(x_11, 4, x_5);
lean_ctor_set_uint8(x_11, sizeof(void*)*5, x_4);
x_12 = lean_apply_1(x_7, x_11);
return x_12;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_box(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___lambda__4___boxed), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_8);
lean_closure_set(x_9, 4, x_6);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_box(x_5);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___lambda__5___boxed), 6, 5);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_replaceRef(x_1, x_7);
x_9 = l_Lean_Syntax_getPos(x_8);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_box(x_5);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___lambda__3___boxed), 6, 5);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_6);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 0);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(x_5);
lean_inc(x_6);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___lambda__6___boxed), 7, 6);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_4);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_6);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_14, x_17);
return x_18;
}
}
}
lean_object* l_Lean_Elab_logAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_box(x_6);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___lambda__7___boxed), 7, 6);
lean_closure_set(x_10, 0, x_4);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_5);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_7);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_logAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logAt___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_logAt___rarg___lambda__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Elab_logAt___rarg___lambda__2(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Elab_logAt___rarg___lambda__3(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Elab_logAt___rarg___lambda__4(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_Elab_logAt___rarg___lambda__5(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Elab_logAt___rarg___lambda__6(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Elab_logAt___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_Elab_logAt___rarg___lambda__7(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_7);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Elab_logAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_logErrorAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 2;
x_7 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_logErrorAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logErrorAt___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logWarningAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
x_7 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_logWarningAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logWarningAt___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logInfoAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_logInfoAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logInfoAt___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_log___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_3, x_6, x_4, x_5);
return x_7;
}
}
lean_object* l_Lean_Elab_log___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_box(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_log___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_8);
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
lean_object* l_Lean_Elab_log___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_5);
lean_dec(x_5);
x_8 = l_Lean_Elab_log___rarg___lambda__1(x_1, x_2, x_3, x_4, x_7, x_6);
return x_8;
}
}
lean_object* l_Lean_Elab_log___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_logError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 2;
x_6 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_logError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logError___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logWarning___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 1;
x_6 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_logWarning(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logWarning___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logInfo___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = 0;
x_6 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Elab_logInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logInfo___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logException_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Elab_logException_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logException_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_logException___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("internal exception: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_logException___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logException___rarg___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_logException___rarg___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_logException___rarg___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_logException___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_Lean_Elab_logException___rarg___lambda__1___closed__3;
x_7 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 2;
x_9 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_logException___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = 2;
x_9 = l_Lean_Elab_logAt___rarg(x_1, x_2, x_3, x_6, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
lean_dec(x_5);
x_11 = l_Lean_Elab_abortExceptionId;
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_InternalExceptionId_getName___boxed), 2, 1);
lean_closure_set(x_14, 0, x_10);
x_15 = lean_apply_2(x_4, lean_box(0), x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_logException___rarg___lambda__1), 4, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_3);
x_17 = lean_apply_4(x_13, lean_box(0), lean_box(0), x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_apply_2(x_19, lean_box(0), x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Elab_logException(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logException___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; 
x_6 = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = 0;
x_8 = l_Lean_Elab_log___rarg(x_1, x_2, x_3, x_6, x_7);
return x_8;
}
}
lean_object* l_Lean_Elab_logTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logTrace___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_trace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_1);
x_7 = l_Lean_checkTraceOption(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_box(0);
x_13 = lean_apply_1(x_3, x_12);
x_14 = l_Lean_Elab_logTrace___rarg(x_2, x_4, x_5, x_1, x_13);
return x_14;
}
}
}
lean_object* l_Lean_Elab_trace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_trace___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_8, 0, x_5);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_6);
lean_closure_set(x_8, 3, x_2);
lean_closure_set(x_8, 4, x_3);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_trace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_trace___rarg), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_trace___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_trace___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Lean_Elab_logDbgTrace___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_1);
x_7 = l_Lean_checkTraceOption(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_apply_2(x_9, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_Lean_Elab_logTrace___rarg(x_2, x_3, x_4, x_1, x_5);
return x_12;
}
}
}
static lean_object* _init_l_Lean_Elab_logDbgTrace___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_initFn____x40_Lean_Elab_Util___hyg_839____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_508____closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Elab_logDbgTrace___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = l_Lean_Elab_logDbgTrace___rarg___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_logDbgTrace___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
lean_closure_set(x_8, 4, x_5);
x_9 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_8);
return x_9;
}
}
lean_object* l_Lean_Elab_logDbgTrace(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_logDbgTrace___rarg), 5, 0);
return x_2;
}
}
lean_object* l_Lean_Elab_logDbgTrace___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_logDbgTrace___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Elab_Util(lean_object*);
lean_object* initialize_Lean_Elab_Exception(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Log(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l_Lean_Elab_logException___rarg___lambda__1___closed__1 = _init_l_Lean_Elab_logException___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_logException___rarg___lambda__1___closed__1);
l_Lean_Elab_logException___rarg___lambda__1___closed__2 = _init_l_Lean_Elab_logException___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_logException___rarg___lambda__1___closed__2);
l_Lean_Elab_logException___rarg___lambda__1___closed__3 = _init_l_Lean_Elab_logException___rarg___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_logException___rarg___lambda__1___closed__3);
l_Lean_Elab_logDbgTrace___rarg___closed__1 = _init_l_Lean_Elab_logDbgTrace___rarg___closed__1();
lean_mark_persistent(l_Lean_Elab_logDbgTrace___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
