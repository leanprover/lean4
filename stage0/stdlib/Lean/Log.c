// Lean compiler output
// Module: Lean.Log
// Imports: Lean.Util.Sorry Lean.Widget.Types Lean.Message Lean.DocString.Links Lean.ErrorExplanation
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
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0___boxed(lean_object*);
lean_object* l_Lean_Option_get___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_kind(lean_object*);
static uint64_t l_Lean_errorDescriptionWidget___closed__1;
LEAN_EXPORT lean_object* l_Lean_logError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5;
LEAN_EXPORT lean_object* l_Lean_log___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Json_mkObj(lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
extern lean_object* l_Lean_manualRoot;
static lean_object* l_Lean_initFn___closed__3____x40_Lean_Log___hyg_204_;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logUnknownDecl___redArg___closed__3;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_initFn___closed__4____x40_Lean_Log___hyg_204_;
uint64_t lean_string_hash(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__6____x40_Lean_Log___hyg_204_;
static lean_object* l_Lean_logUnknownDecl___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_composePreservingKind(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Log___hyg_204_;
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarning___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1;
extern lean_object* l_Lean_MessageData_nil;
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l_Lean_initFn___closed__5____x40_Lean_Log___hyg_204_;
static lean_object* l_Lean_logAt___redArg___lam__4___closed__0;
lean_object* l_Lean_errorNameOfKind_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_warningAsError;
LEAN_EXPORT lean_object* l_Lean_getRefPos(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_errorDescriptionWidget___closed__0;
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget;
static lean_object* l_Lean_errorDescriptionWidget___closed__2;
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__2____x40_Lean_Log___hyg_204_;
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3;
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4;
LEAN_EXPORT lean_object* l_Lean_logNamedError(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logUnknownDecl___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logUnknownDecl___redArg___closed__0;
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0;
static lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2;
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_errorDescriptionWidget___closed__2___boxed__const__1;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Log___hyg_204_;
LEAN_EXPORT lean_object* l_Lean_logNamedError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logNamedWarning(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_ctor_get(x_2, 4);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_instMonadLogOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_1);
lean_inc(x_1);
x_10 = lean_apply_2(x_1, lean_box(0), x_4);
lean_inc(x_1);
x_11 = lean_apply_2(x_1, lean_box(0), x_5);
lean_inc(x_1);
x_12 = lean_apply_2(x_1, lean_box(0), x_6);
x_13 = lean_apply_2(x_1, lean_box(0), x_7);
lean_ctor_set(x_2, 4, x_9);
lean_ctor_set(x_2, 3, x_13);
lean_ctor_set(x_2, 2, x_12);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_10);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
x_18 = lean_ctor_get(x_2, 4);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_1);
x_19 = lean_alloc_closure((void*)(l_Lean_instMonadLogOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_1);
lean_inc(x_1);
x_20 = lean_apply_2(x_1, lean_box(0), x_14);
lean_inc(x_1);
x_21 = lean_apply_2(x_1, lean_box(0), x_15);
lean_inc(x_1);
x_22 = lean_apply_2(x_1, lean_box(0), x_16);
x_23 = lean_apply_2(x_1, lean_box(0), x_17);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_24, 4, x_19);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instMonadLogOfMonadLift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instMonadLogOfMonadLift___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Syntax_getPos_x3f(x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_getRefPos___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getRefPos___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPos___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getRefPos___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_FileMap_toPosition(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lean_getRefPosition___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_6, 0, x_5);
lean_closure_set(x_6, 1, x_1);
x_7 = l_Lean_getRefPos___redArg(x_2, x_3);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_getRefPosition___redArg___lam__1), 5, 4);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_2);
lean_closure_set(x_7, 3, x_4);
x_8 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getRefPosition___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getRefPosition___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getRefPosition___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Log___hyg_204_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("warningAsError", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Log___hyg_204_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Log___hyg_204_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_initFn___closed__2____x40_Lean_Log___hyg_204_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__3____x40_Lean_Log___hyg_204_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("treat warnings as errors", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__4____x40_Lean_Log___hyg_204_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_initFn___closed__3____x40_Lean_Log___hyg_204_;
x_2 = l_Lean_initFn___closed__2____x40_Lean_Log___hyg_204_;
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn___closed__5____x40_Lean_Log___hyg_204_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__6____x40_Lean_Log___hyg_204_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn___closed__0____x40_Lean_Log___hyg_204_;
x_2 = l_Lean_initFn___closed__5____x40_Lean_Log___hyg_204_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Log___hyg_204_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn___closed__1____x40_Lean_Log___hyg_204_;
x_3 = l_Lean_initFn___closed__4____x40_Lean_Log___hyg_204_;
x_4 = l_Lean_initFn___closed__6____x40_Lean_Log___hyg_204_;
x_5 = l_Lean_Option_register___at___Lean_initFn____x40_Lean_Util_Profile___hyg_5__spec__0(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nimport { createElement } from 'react';\nexport default function ({ code, explanationUrl }) {\n  const sansText = { fontFamily: 'var(--vscode-font-family)' }\n\n  const codeSpan = createElement('span', {}, [\n    createElement('span', { style: sansText }, 'Error code: '), code])\n  const brSpan = createElement('span', {}, '\\n')\n  const linkSpan = createElement('span', { style: sansText },\n    createElement('a', { href: explanationUrl }, 'View explanation'))\n\n  const all = createElement('div', { style: { marginTop: '1em' } }, [codeSpan, brSpan, linkSpan])\n  return all\n}", 569, 569);
return x_1;
}
}
static uint64_t _init_l_Lean_errorDescriptionWidget___closed__1() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_errorDescriptionWidget___closed__0;
x_2 = lean_string_hash(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___closed__2___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lean_errorDescriptionWidget___closed__1;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_errorDescriptionWidget___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_errorDescriptionWidget___closed__0;
x_2 = l_Lean_errorDescriptionWidget___closed__2___boxed__const__1;
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
x_1 = l_Lean_errorDescriptionWidget___closed__2;
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_manualRoot;
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("find/\?domain=Manual.errorExplanation&name=", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("errorDescriptionWidget", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__2;
x_2 = l_Lean_initFn___closed__5____x40_Lean_Log___hyg_204_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("code", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5() {
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_errorDescriptionWidget;
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_8 = lean_ctor_get(x_6, 1);
x_9 = lean_ctor_get(x_6, 0);
lean_dec(x_9);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0___boxed), 1, 0);
x_11 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0;
x_12 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1;
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l_Lean_Name_toString(x_5, x_14, x_10);
x_16 = lean_string_append(x_12, x_15);
x_17 = lean_string_append(x_11, x_16);
lean_dec(x_16);
x_18 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3;
x_19 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4;
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_15);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 0, x_19);
x_20 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5;
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_Json_mkObj(x_25);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__1), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_unbox_uint64(x_8);
lean_dec(x_8);
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
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0___boxed), 1, 0);
x_35 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0;
x_36 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1;
x_37 = lean_box(1);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Name_toString(x_5, x_38, x_34);
x_40 = lean_string_append(x_36, x_39);
x_41 = lean_string_append(x_35, x_40);
lean_dec(x_40);
x_42 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3;
x_43 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4;
lean_ctor_set_tag(x_3, 3);
lean_ctor_set(x_3, 0, x_39);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
x_45 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5;
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_41);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Json_mkObj(x_50);
x_52 = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__1), 2, 1);
lean_closure_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_53, 0, x_42);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_unbox_uint64(x_33);
lean_dec(x_33);
lean_ctor_set_uint64(x_53, sizeof(void*)*2, x_54);
x_55 = l_Lean_MessageData_nil;
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_MessageData_composePreservingKind(x_1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint64_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_58 = lean_ctor_get(x_3, 0);
lean_inc(x_58);
lean_dec(x_3);
x_59 = l_Lean_errorDescriptionWidget;
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0___boxed), 1, 0);
x_63 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0;
x_64 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__1;
x_65 = lean_box(1);
x_66 = lean_unbox(x_65);
x_67 = l_Lean_Name_toString(x_58, x_66, x_62);
x_68 = lean_string_append(x_64, x_67);
x_69 = lean_string_append(x_63, x_68);
lean_dec(x_68);
x_70 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__3;
x_71 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__4;
x_72 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_72, 0, x_67);
if (lean_is_scalar(x_61)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_61;
}
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__5;
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_69);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Json_mkObj(x_79);
x_81 = lean_alloc_closure((void*)(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__1), 2, 1);
lean_closure_set(x_81, 0, x_80);
x_82 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_82, 0, x_70);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_unbox_uint64(x_60);
lean_dec(x_60);
lean_ctor_set_uint64(x_82, sizeof(void*)*2, x_83);
x_84 = l_Lean_MessageData_nil;
x_85 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_MessageData_composePreservingKind(x_1, x_85);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc(x_1);
x_10 = l_Lean_FileMap_toPosition(x_1, x_2);
x_11 = l_Lean_FileMap_toPosition(x_1, x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_initFn___closed__2____x40_Lean_Log___hyg_204_;
x_14 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_7);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 2, x_6);
x_15 = lean_apply_1(x_8, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_box(x_4);
x_12 = lean_box(x_5);
x_13 = lean_box(x_6);
x_14 = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__0___boxed), 9, 8);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_11);
lean_closure_set(x_14, 4, x_12);
lean_closure_set(x_14, 5, x_13);
lean_closure_set(x_14, 6, x_10);
lean_closure_set(x_14, 7, x_7);
x_15 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_box(x_3);
x_13 = lean_box(x_4);
x_14 = lean_box(x_5);
lean_inc(x_7);
x_15 = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__1___boxed), 10, 9);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_2);
lean_closure_set(x_15, 3, x_12);
lean_closure_set(x_15, 4, x_13);
lean_closure_set(x_15, 5, x_14);
lean_closure_set(x_15, 6, x_6);
lean_closure_set(x_15, 7, x_7);
lean_closure_set(x_15, 8, x_8);
x_16 = lean_apply_1(x_9, x_10);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_25; 
x_20 = l_Lean_replaceRef(x_1, x_11);
x_25 = l_Lean_Syntax_getPos_x3f(x_20, x_2);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(0u);
x_21 = x_26;
goto block_24;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_21 = x_27;
goto block_24;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_box(x_2);
x_15 = lean_box(x_3);
x_16 = lean_box(x_4);
lean_inc(x_6);
x_17 = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__2___boxed), 11, 10);
lean_closure_set(x_17, 0, x_12);
lean_closure_set(x_17, 1, x_13);
lean_closure_set(x_17, 2, x_14);
lean_closure_set(x_17, 3, x_15);
lean_closure_set(x_17, 4, x_16);
lean_closure_set(x_17, 5, x_5);
lean_closure_set(x_17, 6, x_6);
lean_closure_set(x_17, 7, x_7);
lean_closure_set(x_17, 8, x_8);
lean_closure_set(x_17, 9, x_9);
x_18 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_17);
return x_18;
}
block_24:
{
lean_object* x_22; 
x_22 = l_Lean_Syntax_getTailPos_x3f(x_20, x_2);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_inc(x_21);
x_12 = x_21;
x_13 = x_21;
goto block_19;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_12 = x_21;
x_13 = x_23;
goto block_19;
}
}
}
}
static lean_object* _init_l_Lean_logAt___redArg___lam__4___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_warningAsError;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_22; lean_object* x_24; uint8_t x_25; uint8_t x_26; 
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_8, x_25);
if (x_26 == 0)
{
x_22 = x_26;
goto block_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = l_Lean_KVMap_instValueBool;
x_28 = l_Lean_logAt___redArg___lam__4___closed__0;
x_29 = l_Lean_Option_get___redArg(x_27, x_10, x_28);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
x_22 = x_30;
goto block_23;
}
block_21:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_box(x_3);
x_17 = lean_box(x_11);
x_18 = lean_box(x_4);
lean_inc(x_5);
x_19 = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__3___boxed), 11, 10);
lean_closure_set(x_19, 0, x_2);
lean_closure_set(x_19, 1, x_16);
lean_closure_set(x_19, 2, x_17);
lean_closure_set(x_19, 3, x_18);
lean_closure_set(x_19, 4, x_15);
lean_closure_set(x_19, 5, x_5);
lean_closure_set(x_19, 6, x_14);
lean_closure_set(x_19, 7, x_6);
lean_closure_set(x_19, 8, x_7);
lean_closure_set(x_19, 9, x_12);
x_20 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_13, x_19);
return x_20;
}
block_23:
{
if (x_22 == 0)
{
x_11 = x_8;
goto block_21;
}
else
{
x_11 = x_9;
goto block_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_22; uint8_t x_23; 
x_9 = lean_box(2);
x_22 = lean_unbox(x_9);
x_23 = l_Lean_beqMessageSeverity____x40_Lean_Message___hyg_185_(x_7, x_22);
if (x_23 == 0)
{
x_10 = x_23;
goto block_21;
}
else
{
uint8_t x_24; 
lean_inc(x_6);
x_24 = l_Lean_MessageData_hasSyntheticSorry(x_6);
x_10 = x_24;
goto block_21;
}
block_21:
{
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(x_10);
x_13 = lean_box(x_8);
x_14 = lean_box(x_7);
lean_inc(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_logAt___redArg___lam__4___boxed), 10, 9);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_5);
lean_closure_set(x_15, 2, x_12);
lean_closure_set(x_15, 3, x_13);
lean_closure_set(x_15, 4, x_11);
lean_closure_set(x_15, 5, x_3);
lean_closure_set(x_15, 6, x_6);
lean_closure_set(x_15, 7, x_14);
lean_closure_set(x_15, 8, x_9);
x_16 = lean_apply_4(x_11, lean_box(0), lean_box(0), x_4, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = lean_apply_2(x_18, lean_box(0), x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, uint8_t x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_logAt___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_logAt___redArg___lam__0(x_1, x_2, x_3, x_10, x_11, x_12, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_logAt___redArg___lam__1(x_1, x_2, x_3, x_11, x_12, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_logAt___redArg___lam__2(x_1, x_2, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Lean_logAt___redArg___lam__3(x_1, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_8);
lean_dec(x_8);
x_14 = lean_unbox(x_9);
lean_dec(x_9);
x_15 = l_Lean_logAt___redArg___lam__4(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_13, x_14, x_10);
lean_dec(x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = l_Lean_logAt___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = lean_unbox(x_9);
lean_dec(x_9);
x_12 = l_Lean_logAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_box(2);
x_8 = lean_box(0);
x_9 = lean_unbox(x_7);
x_10 = lean_unbox(x_8);
x_11 = l_Lean_logAt___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logErrorAt___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_8 = l_Lean_MessageData_tagWithErrorName(x_7, x_6);
x_9 = lean_box(2);
x_10 = lean_box(0);
x_11 = lean_unbox(x_9);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_logAt___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedErrorAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logNamedErrorAt___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_box(1);
x_8 = lean_box(0);
x_9 = lean_unbox(x_7);
x_10 = lean_unbox(x_8);
x_11 = l_Lean_logAt___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logWarningAt___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_8 = l_Lean_MessageData_tagWithErrorName(x_7, x_6);
x_9 = lean_box(1);
x_10 = lean_box(0);
x_11 = lean_unbox(x_9);
x_12 = lean_unbox(x_10);
x_13 = l_Lean_logAt___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarningAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logNamedWarningAt___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_unbox(x_7);
x_10 = lean_unbox(x_8);
x_11 = l_Lean_logAt___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logInfoAt___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_logAt___redArg(x_1, x_2, x_3, x_4, x_8, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
x_10 = lean_box(x_6);
x_11 = lean_box(x_7);
x_12 = lean_alloc_closure((void*)(l_Lean_log___redArg___lam__0___boxed), 8, 7);
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
LEAN_EXPORT lean_object* l_Lean_log(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, uint8_t x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_log___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = lean_unbox(x_7);
lean_dec(x_7);
x_11 = l_Lean_log___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_9, x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_log___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = l_Lean_log___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_log___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_7);
lean_dec(x_7);
x_10 = lean_unbox(x_8);
lean_dec(x_8);
x_11 = l_Lean_log(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_box(2);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_log___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logError___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_7 = l_Lean_MessageData_tagWithErrorName(x_6, x_5);
x_8 = lean_box(2);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_log___redArg(x_1, x_2, x_3, x_4, x_7, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedError(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logNamedError___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_log___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logWarning___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_7 = l_Lean_MessageData_tagWithErrorName(x_6, x_5);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_8);
x_11 = lean_unbox(x_9);
x_12 = l_Lean_log___redArg(x_1, x_2, x_3, x_4, x_7, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logNamedWarning(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logNamedWarning___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_log___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logInfo___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unknown declaration '", 21, 21);
return x_1;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_logUnknownDecl___redArg___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_logUnknownDecl___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_logUnknownDecl___redArg___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = l_Lean_logUnknownDecl___redArg___closed__1;
x_7 = l_Lean_MessageData_ofName(x_5);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_logUnknownDecl___redArg___closed__3;
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_logError___redArg(x_1, x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logUnknownDecl___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Lean_Util_Sorry(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Widget_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString_Links(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ErrorExplanation(uint8_t builtin, lean_object*);
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
res = initialize_Lean_ErrorExplanation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn___closed__0____x40_Lean_Log___hyg_204_ = _init_l_Lean_initFn___closed__0____x40_Lean_Log___hyg_204_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Log___hyg_204_);
l_Lean_initFn___closed__1____x40_Lean_Log___hyg_204_ = _init_l_Lean_initFn___closed__1____x40_Lean_Log___hyg_204_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Log___hyg_204_);
l_Lean_initFn___closed__2____x40_Lean_Log___hyg_204_ = _init_l_Lean_initFn___closed__2____x40_Lean_Log___hyg_204_();
lean_mark_persistent(l_Lean_initFn___closed__2____x40_Lean_Log___hyg_204_);
l_Lean_initFn___closed__3____x40_Lean_Log___hyg_204_ = _init_l_Lean_initFn___closed__3____x40_Lean_Log___hyg_204_();
lean_mark_persistent(l_Lean_initFn___closed__3____x40_Lean_Log___hyg_204_);
l_Lean_initFn___closed__4____x40_Lean_Log___hyg_204_ = _init_l_Lean_initFn___closed__4____x40_Lean_Log___hyg_204_();
lean_mark_persistent(l_Lean_initFn___closed__4____x40_Lean_Log___hyg_204_);
l_Lean_initFn___closed__5____x40_Lean_Log___hyg_204_ = _init_l_Lean_initFn___closed__5____x40_Lean_Log___hyg_204_();
lean_mark_persistent(l_Lean_initFn___closed__5____x40_Lean_Log___hyg_204_);
l_Lean_initFn___closed__6____x40_Lean_Log___hyg_204_ = _init_l_Lean_initFn___closed__6____x40_Lean_Log___hyg_204_();
lean_mark_persistent(l_Lean_initFn___closed__6____x40_Lean_Log___hyg_204_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Log___hyg_204_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_warningAsError = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_warningAsError);
lean_dec_ref(res);
}l_Lean_errorDescriptionWidget___closed__0 = _init_l_Lean_errorDescriptionWidget___closed__0();
lean_mark_persistent(l_Lean_errorDescriptionWidget___closed__0);
l_Lean_errorDescriptionWidget___closed__1 = _init_l_Lean_errorDescriptionWidget___closed__1();
l_Lean_errorDescriptionWidget___closed__2___boxed__const__1 = _init_l_Lean_errorDescriptionWidget___closed__2___boxed__const__1();
lean_mark_persistent(l_Lean_errorDescriptionWidget___closed__2___boxed__const__1);
l_Lean_errorDescriptionWidget___closed__2 = _init_l_Lean_errorDescriptionWidget___closed__2();
lean_mark_persistent(l_Lean_errorDescriptionWidget___closed__2);
l_Lean_errorDescriptionWidget = _init_l_Lean_errorDescriptionWidget();
lean_mark_persistent(l_Lean_errorDescriptionWidget);
l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0 = _init_l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0();
lean_mark_persistent(l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed___closed__0);
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
l_Lean_logAt___redArg___lam__4___closed__0 = _init_l_Lean_logAt___redArg___lam__4___closed__0();
lean_mark_persistent(l_Lean_logAt___redArg___lam__4___closed__0);
l_Lean_logUnknownDecl___redArg___closed__0 = _init_l_Lean_logUnknownDecl___redArg___closed__0();
lean_mark_persistent(l_Lean_logUnknownDecl___redArg___closed__0);
l_Lean_logUnknownDecl___redArg___closed__1 = _init_l_Lean_logUnknownDecl___redArg___closed__1();
lean_mark_persistent(l_Lean_logUnknownDecl___redArg___closed__1);
l_Lean_logUnknownDecl___redArg___closed__2 = _init_l_Lean_logUnknownDecl___redArg___closed__2();
lean_mark_persistent(l_Lean_logUnknownDecl___redArg___closed__2);
l_Lean_logUnknownDecl___redArg___closed__3 = _init_l_Lean_logUnknownDecl___redArg___closed__3();
lean_mark_persistent(l_Lean_logUnknownDecl___redArg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
