// Lean compiler output
// Module: Lean.Log
// Imports: Init Lean.Util.Sorry Lean.Message
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
LEAN_EXPORT lean_object* l_Lean_log(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3;
static lean_object* l_Lean_logAt___rarg___lambda__14___closed__1;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___rarg(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_hasSyntheticSorry(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_193____closed__1;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___rarg___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_193____closed__2;
LEAN_EXPORT lean_object* l_Lean_instMonadLog(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLog___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLog___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_193____closed__6;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__14(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_warningAsError;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_logUnknownDecl___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_getRefPos(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_logUnknownDecl___rarg___closed__3;
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_193____closed__5;
LEAN_EXPORT lean_object* l_Lean_logUnknownDecl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__4(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_logUnknownDecl___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Log___hyg_193_(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_193____closed__7;
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfo(lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_Log___hyg_193____closed__4;
LEAN_EXPORT lean_object* l_Lean_logInfoAt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_logError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
static lean_object* l_Lean_logUnknownDecl___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_getRefPosition___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__13(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getRefPos___rarg___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instMonadLog___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_instMonadLog___rarg(lean_object* x_1, lean_object* x_2) {
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
x_11 = lean_alloc_closure((void*)(l_Lean_instMonadLog___rarg___lambda__1), 3, 2);
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
LEAN_EXPORT lean_object* l_Lean_instMonadLog(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_instMonadLog___rarg), 2, 0);
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
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("warningAsError", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("treat warnings as errors", 24);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3;
x_3 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__4;
x_4 = lean_box(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__6;
x_2 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__1;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Log___hyg_193_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__2;
x_3 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__5;
x_4 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__7;
x_5 = l_Lean_Option_register___at_Lean_initFn____x40_Lean_Util_Profile___hyg_6____spec__1(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_FileMap_toPosition(x_2, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3;
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_4);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_3);
x_13 = lean_apply_1(x_6, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_box(x_3);
x_8 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__1___boxed), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_5);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = lean_box(x_4);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__2___boxed), 5, 4);
lean_closure_set(x_9, 0, x_3);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
lean_closure_set(x_9, 3, x_5);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Lean_FileMap_toPosition(x_2, x_8);
x_10 = l_Lean_FileMap_toPosition(x_2, x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = 0;
x_13 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_5);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_4);
x_15 = lean_apply_1(x_7, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_box(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__4___boxed), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_8);
lean_closure_set(x_9, 4, x_6);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_box(x_5);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__5___boxed), 6, 5);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_FileMap_toPosition(x_2, x_3);
lean_inc(x_8);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = 0;
x_11 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3;
x_12 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_9);
lean_ctor_set(x_12, 3, x_11);
lean_ctor_set(x_12, 4, x_5);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_10);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_4);
x_13 = lean_apply_1(x_7, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = lean_box(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__7___boxed), 6, 5);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_3);
lean_closure_set(x_9, 3, x_8);
lean_closure_set(x_9, 4, x_6);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_apply_1(x_1, x_2);
x_9 = lean_box(x_5);
lean_inc(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__8___boxed), 6, 5);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_4);
lean_closure_set(x_10, 3, x_9);
lean_closure_set(x_10, 4, x_6);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_FileMap_toPosition(x_2, x_3);
x_10 = l_Lean_FileMap_toPosition(x_2, x_4);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = 0;
x_13 = l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3;
x_14 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_11);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_6);
lean_ctor_set_uint8(x_14, sizeof(void*)*5, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*5 + 1, x_5);
x_15 = lean_apply_1(x_8, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_box(x_5);
x_10 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__10___boxed), 7, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_9);
lean_closure_set(x_10, 5, x_7);
x_11 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_apply_1(x_1, x_2);
x_10 = lean_box(x_6);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__11___boxed), 7, 6);
lean_closure_set(x_11, 0, x_3);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_4);
lean_closure_set(x_11, 3, x_5);
lean_closure_set(x_11, 4, x_10);
lean_closure_set(x_11, 5, x_7);
x_12 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_replaceRef(x_1, x_7);
x_9 = 0;
x_10 = l_Lean_Syntax_getPos_x3f(x_8, x_9);
x_11 = l_Lean_Syntax_getTailPos_x3f(x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_box(x_5);
lean_inc(x_6);
x_14 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__3___boxed), 6, 5);
lean_closure_set(x_14, 0, x_3);
lean_closure_set(x_14, 1, x_4);
lean_closure_set(x_14, 2, x_2);
lean_closure_set(x_14, 3, x_13);
lean_closure_set(x_14, 4, x_6);
x_15 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_12, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(x_5);
lean_inc(x_6);
x_19 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__6___boxed), 7, 6);
lean_closure_set(x_19, 0, x_3);
lean_closure_set(x_19, 1, x_4);
lean_closure_set(x_19, 2, x_2);
lean_closure_set(x_19, 3, x_17);
lean_closure_set(x_19, 4, x_18);
lean_closure_set(x_19, 5, x_6);
x_20 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_16, x_19);
return x_20;
}
}
else
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_box(x_5);
lean_inc(x_6);
x_24 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__9___boxed), 7, 6);
lean_closure_set(x_24, 0, x_3);
lean_closure_set(x_24, 1, x_4);
lean_closure_set(x_24, 2, x_2);
lean_closure_set(x_24, 3, x_22);
lean_closure_set(x_24, 4, x_23);
lean_closure_set(x_24, 5, x_6);
x_25 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_21, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_ctor_get(x_11, 0);
lean_inc(x_28);
lean_dec(x_11);
x_29 = lean_box(x_5);
lean_inc(x_6);
x_30 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__12___boxed), 8, 7);
lean_closure_set(x_30, 0, x_3);
lean_closure_set(x_30, 1, x_4);
lean_closure_set(x_30, 2, x_2);
lean_closure_set(x_30, 3, x_27);
lean_closure_set(x_30, 4, x_28);
lean_closure_set(x_30, 5, x_29);
lean_closure_set(x_30, 6, x_6);
x_31 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_26, x_30);
return x_31;
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
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__14(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; 
x_8 = 1;
x_9 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_box(x_1);
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__13___boxed), 7, 6);
lean_closure_set(x_12, 0, x_3);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_11);
lean_closure_set(x_12, 5, x_6);
x_13 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_10, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = l_Lean_logAt___rarg___lambda__14___closed__1;
x_16 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_7, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(x_1);
lean_inc(x_6);
x_18 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__13___boxed), 7, 6);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_4);
lean_closure_set(x_18, 3, x_5);
lean_closure_set(x_18, 4, x_17);
lean_closure_set(x_18, 5, x_6);
x_19 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_14, x_18);
return x_19;
}
else
{
uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = 2;
x_21 = lean_box(x_20);
lean_inc(x_6);
x_22 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__13___boxed), 7, 6);
lean_closure_set(x_22, 0, x_3);
lean_closure_set(x_22, 1, x_2);
lean_closure_set(x_22, 2, x_4);
lean_closure_set(x_22, 3, x_5);
lean_closure_set(x_22, 4, x_21);
lean_closure_set(x_22, 5, x_6);
x_23 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_14, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; uint8_t x_15; 
x_14 = 2;
x_15 = l___private_Lean_Message_0__Lean_beqMessageSeverity____x40_Lean_Message___hyg_103_(x_7, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_box(0);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_6);
x_17 = l_Lean_MessageData_hasSyntheticSorry(x_6);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_box(0);
x_8 = x_19;
goto block_13;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = lean_apply_2(x_21, lean_box(0), x_22);
return x_23;
}
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_box(x_7);
lean_inc(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___lambda__14___boxed), 7, 6);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_5);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_6);
lean_closure_set(x_11, 5, x_9);
x_12 = lean_apply_4(x_9, lean_box(0), lean_box(0), x_4, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_logAt___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_logAt___rarg___lambda__1(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_logAt___rarg___lambda__2(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_logAt___rarg___lambda__3(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_logAt___rarg___lambda__4(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_logAt___rarg___lambda__5(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_logAt___rarg___lambda__6(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_logAt___rarg___lambda__7(x_1, x_2, x_3, x_7, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_4);
lean_dec(x_4);
x_8 = l_Lean_logAt___rarg___lambda__8(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_logAt___rarg___lambda__9(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_logAt___rarg___lambda__10(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_logAt___rarg___lambda__11(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_6);
lean_dec(x_6);
x_10 = l_Lean_logAt___rarg___lambda__12(x_1, x_2, x_3, x_4, x_5, x_9, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_5);
lean_dec(x_5);
x_9 = l_Lean_logAt___rarg___lambda__13(x_1, x_2, x_3, x_4, x_8, x_6, x_7);
lean_dec(x_7);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___lambda__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_Lean_logAt___rarg___lambda__14(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 2;
x_8 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_logWarningAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
x_8 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_logInfoAt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 0;
x_8 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
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
LEAN_EXPORT lean_object* l_Lean_log___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_logAt___rarg(x_1, x_2, x_3, x_4, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_log___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_box(x_6);
x_10 = lean_alloc_closure((void*)(l_Lean_log___rarg___lambda__1___boxed), 7, 6);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_5);
lean_closure_set(x_10, 5, x_9);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_log(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_log___rarg___boxed), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_log___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_6);
lean_dec(x_6);
x_9 = l_Lean_log___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_log___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_6);
lean_dec(x_6);
x_8 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 2;
x_7 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
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
LEAN_EXPORT lean_object* l_Lean_logWarning___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_logAt___rarg___lambda__14___closed__1;
x_8 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_6, x_7);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; 
x_9 = 1;
x_10 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; 
x_11 = 2;
x_12 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_5, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_inc(x_4);
x_7 = lean_alloc_closure((void*)(l_Lean_logWarning___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
lean_closure_set(x_7, 4, x_5);
x_8 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_4, x_7);
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
LEAN_EXPORT lean_object* l_Lean_logWarning___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_logWarning___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfo___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
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
x_1 = lean_mk_string_from_bytes("unknown declaration '", 21);
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
x_1 = lean_mk_string_from_bytes("'", 1);
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
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
x_12 = l_Lean_log___rarg(x_1, x_2, x_3, x_4, x_10, x_11);
return x_12;
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Sorry(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Log(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Sorry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_initFn____x40_Lean_Log___hyg_193____closed__1 = _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_193____closed__1);
l_Lean_initFn____x40_Lean_Log___hyg_193____closed__2 = _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_193____closed__2);
l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3 = _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_193____closed__3);
l_Lean_initFn____x40_Lean_Log___hyg_193____closed__4 = _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__4();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_193____closed__4);
l_Lean_initFn____x40_Lean_Log___hyg_193____closed__5 = _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__5();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_193____closed__5);
l_Lean_initFn____x40_Lean_Log___hyg_193____closed__6 = _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__6();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_193____closed__6);
l_Lean_initFn____x40_Lean_Log___hyg_193____closed__7 = _init_l_Lean_initFn____x40_Lean_Log___hyg_193____closed__7();
lean_mark_persistent(l_Lean_initFn____x40_Lean_Log___hyg_193____closed__7);
if (builtin) {res = l_Lean_initFn____x40_Lean_Log___hyg_193_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_warningAsError = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_warningAsError);
lean_dec_ref(res);
}l_Lean_logAt___rarg___lambda__14___closed__1 = _init_l_Lean_logAt___rarg___lambda__14___closed__1();
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
