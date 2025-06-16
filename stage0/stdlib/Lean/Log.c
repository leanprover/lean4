// Lean compiler output
// Module: Lean.Log
// Imports: Lean.Util.Sorry Lean.Widget.Types Lean.Message Lean.DocString.Links
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
LEAN_EXPORT lean_object* l_Lean_logNamedError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lambda__1___boxed(lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
static lean_object* l_Lean_errorDescriptionWidget___closed__1;
LEAN_EXPORT lean_object* l_Lean_log(lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5;
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_logAt___rarg___lambda__14___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___rarg(lean_object*, lean_object*);
uint8_t l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_manualRoot;
LEAN_EXPORT lean_object* l_Lean_log___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204____closed__1;
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6;
LEAN_EXPORT lean_object* l_Lean_logWarning___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt(lean_object*);
lean_object* l_Lean_MessageData_composePreservingKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___closed__3___boxed__const__1;
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204____closed__4;
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204____closed__2;
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204____closed__6;
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition(lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1;
extern lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l_Lean_logInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_errorNameOfKind_x3f(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__14(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_warningAsError;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logUnknownDecl___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_getRefPos(lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lambda__1(lean_object*);
static lean_object* l_Lean_logUnknownDecl___rarg___closed__3;
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__10;
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget;
static uint64_t l_Lean_errorDescriptionWidget___closed__2;
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_logUnknownDecl___rarg___closed__4;
extern lean_object* l_Lean_errorExplanationManualDomain;
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3;
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4;
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204____closed__7;
LEAN_EXPORT lean_object* l_Lean_logNamedError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__8;
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarning___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2;
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_errorDescriptionWidget___closed__3;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204____closed__5;
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarning(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3;
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt(lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__9;
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_logUnknownDecl___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure___at_Lean_Server_instRpcEncodableStateMRpcObjectStore___spec__1___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___rarg___lambda__1___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7;
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 4);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_6 = lean_apply_2(x_1, lean_box(0), x_5);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_inc(x_1);
x_8 = lean_apply_2(x_1, lean_box(0), x_7);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, lean_box(0), x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_instMonadLogOfMonadLift___rarg___lambda__1), 3, 2);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_6);
lean_ctor_set(x_12, 2, x_8);
lean_ctor_set(x_12, 3, x_10);
lean_ctor_set(x_12, 4, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadLogOfMonadLift___rarg), 2, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___rarg___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = 0;
x_6 = l_Lean_Syntax_getPos_x3f(x_2, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_apply_2(x_4, lean_box(0), x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_2(x_4, lean_box(0), x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_getRefPos___rarg___lambda__1___boxed), 2, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getRefPos___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getRefPos___rarg___lambda__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_5 = l_Lean_getRefPos___rarg(x_1, x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_getRefPosition___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_4);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_getRefPosition___rarg___lambda__2), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
lean_closure_set(x_5, 2, x_3);
x_6 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_getRefPosition___rarg), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getRefPosition___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warningAsError", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("treat warnings as errors", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3;
x_3 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__6;
x_2 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__5;
x_4 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__7;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_5____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nimport { createElement } from 'react';\nexport default function ({ code, explanationUrl }) {\n  const sansText = { fontFamily: 'var(--vscode-font-family)' }\n\n  const codeSpan = createElement('span', {}, [\n    createElement('span', { style: sansText }, 'Error code: '), code])\n  const brSpan = createElement('span', {}, '\\n')\n  const linkSpan = createElement('span', { style: sansText },\n    createElement('a', { href: explanationUrl }, 'View explanation'))\n\n  const all = createElement('div', { style: { marginTop: '1em' } }, [codeSpan, brSpan, linkSpan])\n  return all\n}", 569, 569);
return x_1;
}
}
static uint64_t _init_l_Lean_errorDescriptionWidget___closed__2() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_errorDescriptionWidget___closed__1;
x_2 = lean_string_hash(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___closed__3___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_errorDescriptionWidget___closed__2;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___closed__1;
x_2 = l_Lean_errorDescriptionWidget___closed__3___boxed__const__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_errorDescriptionWidget___closed__3;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("find/\?domain=", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1;
x_2 = l_Lean_errorExplanationManualDomain;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("&name=", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2;
x_2 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_manualRoot;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("errorDescriptionWidget", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__6;
x_2 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("explanationUrl", 14, 14);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_MessageData_kind(x_1);
x_3 = l_Lean_errorNameOfKind_x3f(x_2);
lean_dec(x_2);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = 1;
x_7 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5;
x_8 = l_Lean_Name_toString(x_5, x_6, x_7);
x_9 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4;
x_10 = lean_string_append(x_9, x_8);
x_11 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3;
x_12 = lean_string_append(x_10, x_11);
x_13 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = l_Lean_errorDescriptionWidget;
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_8);
x_17 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__9;
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__10;
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Json_mkObj(x_24);
x_26 = lean_alloc_closure((void*)(l_StateT_pure___at_Lean_Server_instRpcEncodableStateMRpcObjectStore___spec__1___rarg), 2, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__8;
x_28 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = lean_unbox_uint64(x_16);
lean_dec(x_16);
lean_ctor_set_uint64(x_28, sizeof(void*)*2, x_29);
x_30 = l_Lean_MessageData_nil;
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_composePreservingKind(x_1, x_31);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint64_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_33 = lean_ctor_get(x_3, 0);
lean_inc(x_33);
lean_dec(x_3);
x_34 = 1;
x_35 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5;
x_36 = l_Lean_Name_toString(x_33, x_34, x_35);
x_37 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4;
x_38 = lean_string_append(x_37, x_36);
x_39 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3;
x_40 = lean_string_append(x_38, x_39);
x_41 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6;
x_42 = lean_string_append(x_41, x_40);
lean_dec(x_40);
x_43 = l_Lean_errorDescriptionWidget;
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_36);
x_46 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__9;
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_42);
x_49 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__10;
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_47);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Json_mkObj(x_53);
x_55 = lean_alloc_closure((void*)(l_StateT_pure___at_Lean_Server_instRpcEncodableStateMRpcObjectStore___spec__1___rarg), 2, 1);
lean_closure_set(x_55, 0, x_54);
x_56 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__8;
x_57 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_unbox_uint64(x_44);
lean_dec(x_44);
lean_ctor_set_uint64(x_57, sizeof(void*)*2, x_58);
x_59 = l_Lean_MessageData_nil;
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_MessageData_composePreservingKind(x_1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_FileMap_toPosition(x_2, x_8);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 0;
x_12 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3;
x_13 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_5);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 1, x_3);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 2, x_4);
x_14 = lean_apply_1(x_7, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_box(x_3);
x_9 = lean_box(x_4);
x_10 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_8);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_box(x_4);
x_10 = lean_box(x_5);
lean_inc(x_6);
x_11 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__2___boxed), 6, 5);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_7);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_10);
lean_closure_set(x_11, 4, x_6);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
x_10 = l_Lean_FileMap_toPosition(x_2, x_9);
x_11 = l_Lean_FileMap_toPosition(x_2, x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 0;
x_14 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3;
x_15 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_6);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_4);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 2, x_5);
x_16 = lean_apply_1(x_8, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_box(x_4);
x_10 = lean_box(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__4___boxed), 7, 6);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_10);
lean_closure_set(x_11, 5, x_7);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_apply_1(x_1, x_2);
x_10 = lean_box(x_5);
x_11 = lean_box(x_6);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__5___boxed), 7, 6);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_10);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_7);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_FileMap_toPosition(x_2, x_3);
lean_inc(x_9);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = 0;
x_12 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3;
x_13 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_10);
lean_ctor_set(x_13, 3, x_12);
lean_ctor_set(x_13, 4, x_6);
lean_ctor_set_uint8(x_13, sizeof(void*)*5, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 1, x_4);
lean_ctor_set_uint8(x_13, sizeof(void*)*5 + 2, x_5);
x_14 = lean_apply_1(x_8, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_box(x_4);
x_10 = lean_box(x_5);
x_11 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__7___boxed), 7, 6);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_10);
lean_closure_set(x_11, 5, x_7);
x_12 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_apply_1(x_1, x_2);
x_10 = lean_box(x_5);
x_11 = lean_box(x_6);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__8___boxed), 7, 6);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_10);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_7);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_2);
x_10 = l_Lean_FileMap_toPosition(x_2, x_3);
x_11 = l_Lean_FileMap_toPosition(x_2, x_4);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = 0;
x_14 = l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3;
x_15 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_14);
lean_ctor_set(x_15, 4, x_7);
lean_ctor_set_uint8(x_15, sizeof(void*)*5, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 1, x_5);
lean_ctor_set_uint8(x_15, sizeof(void*)*5 + 2, x_6);
x_16 = lean_apply_1(x_9, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_box(x_5);
x_11 = lean_box(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__10___boxed), 8, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_10);
lean_closure_set(x_12, 5, x_11);
lean_closure_set(x_12, 6, x_8);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_apply_1(x_1, x_2);
x_11 = lean_box(x_6);
x_12 = lean_box(x_7);
lean_inc(x_8);
x_13 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__11___boxed), 8, 7);
lean_closure_set(x_13, 0, x_3);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_4);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_11);
lean_closure_set(x_13, 5, x_12);
lean_closure_set(x_13, 6, x_8);
x_14 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_10, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l_Lean_replaceRef(x_1, x_8);
x_10 = 0;
x_11 = l_Lean_Syntax_getPos_x3f(x_9, x_10);
x_12 = l_Lean_Syntax_getTailPos_x3f(x_9, x_10);
lean_dec(x_9);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_box(x_5);
x_15 = lean_box(x_6);
lean_inc(x_7);
x_16 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_16, 0, x_3);
lean_closure_set(x_16, 1, x_4);
lean_closure_set(x_16, 2, x_2);
lean_closure_set(x_16, 3, x_14);
lean_closure_set(x_16, 4, x_15);
lean_closure_set(x_16, 5, x_7);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_13, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_box(x_5);
x_21 = lean_box(x_6);
lean_inc(x_7);
x_22 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__6___boxed), 8, 7);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_4);
lean_closure_set(x_22, 2, x_2);
lean_closure_set(x_22, 3, x_19);
lean_closure_set(x_22, 4, x_20);
lean_closure_set(x_22, 5, x_21);
lean_closure_set(x_22, 6, x_7);
x_23 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_18, x_22);
return x_23;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_11, 0);
lean_inc(x_25);
lean_dec(x_11);
x_26 = lean_box(x_5);
x_27 = lean_box(x_6);
lean_inc(x_7);
x_28 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__9___boxed), 8, 7);
lean_closure_set(x_28, 0, x_3);
lean_closure_set(x_28, 1, x_4);
lean_closure_set(x_28, 2, x_2);
lean_closure_set(x_28, 3, x_25);
lean_closure_set(x_28, 4, x_26);
lean_closure_set(x_28, 5, x_27);
lean_closure_set(x_28, 6, x_7);
x_29 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_24, x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_30 = lean_ctor_get(x_2, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec(x_11);
x_32 = lean_ctor_get(x_12, 0);
lean_inc(x_32);
lean_dec(x_12);
x_33 = lean_box(x_5);
x_34 = lean_box(x_6);
lean_inc(x_7);
x_35 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__12___boxed), 9, 8);
lean_closure_set(x_35, 0, x_3);
lean_closure_set(x_35, 1, x_4);
lean_closure_set(x_35, 2, x_2);
lean_closure_set(x_35, 3, x_31);
lean_closure_set(x_35, 4, x_32);
lean_closure_set(x_35, 5, x_33);
lean_closure_set(x_35, 6, x_34);
lean_closure_set(x_35, 7, x_7);
x_36 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_30, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_logAt___rarg___lambda__14___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__14(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; 
x_9 = 1;
x_10 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_box(x_1);
x_13 = lean_box(x_6);
lean_inc(x_7);
x_14 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__13___boxed), 8, 7);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_5);
lean_closure_set(x_14, 4, x_12);
lean_closure_set(x_14, 5, x_13);
lean_closure_set(x_14, 6, x_7);
x_15 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_11, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = l_Lean_logAt___rarg___lambda__14___closed__1;
x_18 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_8, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_box(x_1);
x_20 = lean_box(x_6);
lean_inc(x_7);
x_21 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__13___boxed), 8, 7);
lean_closure_set(x_21, 0, x_3);
lean_closure_set(x_21, 1, x_2);
lean_closure_set(x_21, 2, x_4);
lean_closure_set(x_21, 3, x_5);
lean_closure_set(x_21, 4, x_19);
lean_closure_set(x_21, 5, x_20);
lean_closure_set(x_21, 6, x_7);
x_22 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_21);
return x_22;
}
else
{
uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = 2;
x_24 = lean_box(x_23);
x_25 = lean_box(x_6);
lean_inc(x_7);
x_26 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__13___boxed), 8, 7);
lean_closure_set(x_26, 0, x_3);
lean_closure_set(x_26, 1, x_2);
lean_closure_set(x_26, 2, x_4);
lean_closure_set(x_26, 3, x_5);
lean_closure_set(x_26, 4, x_24);
lean_closure_set(x_26, 5, x_25);
lean_closure_set(x_26, 6, x_7);
x_27 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; uint8_t x_16; uint8_t x_17; 
x_16 = 2;
x_17 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_7, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_box(0);
x_9 = x_18;
goto block_15;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_6);
x_19 = l_Lean_MessageData_hasSyntheticSorry(x_6);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_box(0);
x_9 = x_21;
goto block_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_apply_2(x_23, lean_box(0), x_24);
return x_25;
}
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(x_7);
x_12 = lean_box(x_8);
lean_inc(x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__14___boxed), 8, 7);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_2);
lean_closure_set(x_13, 2, x_5);
lean_closure_set(x_13, 3, x_3);
lean_closure_set(x_13, 4, x_6);
lean_closure_set(x_13, 5, x_12);
lean_closure_set(x_13, 6, x_10);
x_14 = lean_apply_4(x_10, lean_box(0), lean_box(0), x_4, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___boxed), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_logAt___rarg___lambda__1(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_logAt___rarg___lambda__2(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_logAt___rarg___lambda__3(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_logAt___rarg___lambda__4(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_logAt___rarg___lambda__5(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_logAt___rarg___lambda__6(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_logAt___rarg___lambda__7(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = l_Lean_logAt___rarg___lambda__8(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_logAt___rarg___lambda__9(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_logAt___rarg___lambda__10(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_logAt___rarg___lambda__11(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = lean_unbox(x_7);
lean_dec(x_7);
x_12 = l_Lean_logAt___rarg___lambda__12(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_5);
lean_dec(x_5);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_logAt___rarg___lambda__13(x_1, x_2, x_3, x_4, x_9, x_10, x_7, x_8);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_logAt___rarg___lambda__14(x_9, x_2, x_3, x_4, x_5, x_10, x_7, x_8);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = 2;
x_8 = 0;
x_9 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logErrorAt___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = l_Lean_MessageData_tagWithErrorName(x_7, x_6);
x_9 = 2;
x_10 = 0;
x_11 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logNamedErrorAt___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = 1;
x_8 = 0;
x_9 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logWarningAt___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_8 = l_Lean_MessageData_tagWithErrorName(x_7, x_6);
x_9 = 1;
x_10 = 0;
x_11 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logNamedWarningAt___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = 0;
x_8 = 0;
x_9 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logInfoAt___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_log___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_log___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_box(x_6);
x_11 = lean_box(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_log___rarg___lambda__1___boxed), 8, 7);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_10);
lean_closure_set(x_12, 6, x_11);
x_13 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_log(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_log___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_log___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Lean_log___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_log___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = 2;
x_7 = 0;
x_8 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logError___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = l_Lean_MessageData_tagWithErrorName(x_6, x_5);
x_8 = 2;
x_9 = 0;
x_10 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logNamedError___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = 1;
x_7 = 0;
x_8 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logWarning___rarg), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = l_Lean_MessageData_tagWithErrorName(x_6, x_5);
x_8 = 1;
x_9 = 0;
x_10 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logNamedWarning___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_6 = 0;
x_7 = 0;
x_8 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logInfo___rarg), 5, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown declaration '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_logUnknownDecl___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_logUnknownDecl___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_6 = l_Lean_MessageData_ofName(x_5);
x_7 = l_Lean_logUnknownDecl___rarg___closed__2;
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = l_Lean_logUnknownDecl___rarg___closed__4;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = 2;
x_12 = 0;
x_13 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logUnknownDecl___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Lean_Util_Sorry(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Links(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Log(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Sorry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Widget_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Links(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Log___hyg_204____closed__1 = _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_204____closed__1);
l_Lean_initFn____x40_Lean_Log___hyg_204____closed__2 = _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_204____closed__2);
l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3 = _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_204____closed__3);
l_Lean_initFn____x40_Lean_Log___hyg_204____closed__4 = _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_204____closed__4);
l_Lean_initFn____x40_Lean_Log___hyg_204____closed__5 = _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_204____closed__5);
l_Lean_initFn____x40_Lean_Log___hyg_204____closed__6 = _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_204____closed__6);
l_Lean_initFn____x40_Lean_Log___hyg_204____closed__7 = _init_l_Lean_initFn____x40_Lean_Log___hyg_204____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_204____closed__7);
if (builtin) {res = l_Lean_initFn____x40_Lean_Log___hyg_204_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_warningAsError = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_warningAsError);
lean_dec_ref(res);
}l_Lean_errorDescriptionWidget___closed__1 = _init_l_Lean_errorDescriptionWidget___closed__1();
lean_mark_persistent(l_Lean_errorDescriptionWidget___closed__1);
l_Lean_errorDescriptionWidget___closed__2 = _init_l_Lean_errorDescriptionWidget___closed__2();
l_Lean_errorDescriptionWidget___closed__3___boxed__const__1 = _init_l_Lean_errorDescriptionWidget___closed__3___boxed__const__1();
lean_mark_persistent(l_Lean_errorDescriptionWidget___closed__3___boxed__const__1);
l_Lean_errorDescriptionWidget___closed__3 = _init_l_Lean_errorDescriptionWidget___closed__3();
lean_mark_persistent(l_Lean_errorDescriptionWidget___closed__3);
l_Lean_errorDescriptionWidget = _init_l_Lean_errorDescriptionWidget();
lean_mark_persistent(l_Lean_errorDescriptionWidget);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__6);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__7);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__8 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__8();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__8);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__9 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__9();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__9);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__10 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__10();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__10);
l_Lean_logAt___rarg___lambda__14___closed__1 = _init_l_Lean_logAt___rarg___lambda__14___closed__1();
lean_mark_persistent(l_Lean_logAt___rarg___lambda__14___closed__1);
l_Lean_logUnknownDecl___rarg___closed__1 = _init_l_Lean_logUnknownDecl___rarg___closed__1();
lean_mark_persistent(l_Lean_logUnknownDecl___rarg___closed__1);
l_Lean_logUnknownDecl___rarg___closed__2 = _init_l_Lean_logUnknownDecl___rarg___closed__2();
lean_mark_persistent(l_Lean_logUnknownDecl___rarg___closed__2);
l_Lean_logUnknownDecl___rarg___closed__3 = _init_l_Lean_logUnknownDecl___rarg___closed__3();
lean_mark_persistent(l_Lean_logUnknownDecl___rarg___closed__3);
l_Lean_logUnknownDecl___rarg___closed__4 = _init_l_Lean_logUnknownDecl___rarg___closed__4();
lean_mark_persistent(l_Lean_logUnknownDecl___rarg___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
