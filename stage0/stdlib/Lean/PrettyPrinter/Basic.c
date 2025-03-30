// Lean compiler output
// Module: Lean.PrettyPrinter.Basic
// Imports: Lean.KeyedDeclsAttribute
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
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__10;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__2;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__4;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_runForNodeKind(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__1;
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__9;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__8;
static lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__1;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__6;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1(lean_object*);
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_backtrackExceptionId;
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4_(lean_object*);
static lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__11;
lean_object* l_Lean_KeyedDeclsAttribute_getValues___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("backtrackFormatter", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__2;
x_3 = l_Lean_registerInternalExceptionId(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 5);
x_6 = l_Lean_addMessageContextPartial___at_Lean_Core_instAddMessageContextCoreM___spec__1(x_1, x_2, x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_6);
lean_inc(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__4___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Lean_stringToMessageData(x_5);
x_7 = l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__4___rarg(x_6, x_2, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3___rarg___boxed), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_eval_const(x_8, x_9, x_1);
lean_dec(x_8);
x_11 = l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3___rarg(x_10, x_2, x_3, x_7);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ParserDescr", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__1;
x_2 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("TrailingParserDescr", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__1;
x_2 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__4;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no declaration of attribute [", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("] found for '", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_runForNodeKind___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_1, x_11, x_2);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_free_object(x_7);
lean_inc(x_2);
x_13 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_2, x_4, x_5, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_ConstantInfo_type(x_14);
lean_dec(x_14);
x_17 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__3;
x_18 = l_Lean_Expr_isConstOf(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__5;
x_20 = l_Lean_Expr_isConstOf(x_16, x_19);
lean_dec(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_3);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_MessageData_ofName(x_22);
x_24 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__7;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__9;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MessageData_ofName(x_2);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__11;
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1___rarg(x_31, x_4, x_5, x_15);
lean_dec(x_5);
lean_dec(x_4);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_1);
x_33 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_2, x_4, x_5, x_15);
lean_dec(x_2);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_apply_4(x_3, x_34, x_4, x_5, x_35);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; 
lean_dec(x_16);
lean_dec(x_1);
x_41 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_2, x_4, x_5, x_15);
lean_dec(x_2);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_apply_4(x_3, x_42, x_4, x_5, x_43);
return x_44;
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_13);
if (x_49 == 0)
{
return x_13;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_13, 0);
x_51 = lean_ctor_get(x_13, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_13);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_12, 0);
lean_inc(x_53);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_53);
return x_7;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_7, 0);
x_55 = lean_ctor_get(x_7, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_7);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_1, x_56, x_2);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
lean_inc(x_2);
x_58 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_2, x_4, x_5, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_ConstantInfo_type(x_59);
lean_dec(x_59);
x_62 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__3;
x_63 = l_Lean_Expr_isConstOf(x_61, x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__5;
x_65 = l_Lean_Expr_isConstOf(x_61, x_64);
lean_dec(x_61);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_3);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_MessageData_ofName(x_67);
x_69 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__7;
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
x_71 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__9;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_MessageData_ofName(x_2);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__11;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1___rarg(x_76, x_4, x_5, x_60);
lean_dec(x_5);
lean_dec(x_4);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec(x_1);
x_78 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_2, x_4, x_5, x_60);
lean_dec(x_2);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_apply_4(x_3, x_79, x_4, x_5, x_80);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_78, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_84 = x_78;
} else {
 lean_dec_ref(x_78);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
}
}
else
{
lean_object* x_86; 
lean_dec(x_61);
lean_dec(x_1);
x_86 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_2, x_4, x_5, x_60);
lean_dec(x_2);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_apply_4(x_3, x_87, x_4, x_5, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = lean_ctor_get(x_86, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_86, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_92 = x_86;
} else {
 lean_dec_ref(x_86);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_94 = lean_ctor_get(x_58, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_58, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_96 = x_58;
} else {
 lean_dec_ref(x_58);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_57, 0);
lean_inc(x_98);
lean_dec(x_57);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_55);
return x_99;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PrettyPrinter_runForNodeKind(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_runForNodeKind___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__4___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_KeyedDeclsAttribute(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_KeyedDeclsAttribute(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__1 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__1);
l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__2 = _init_l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4____closed__2);
if (builtin) {res = l_Lean_PrettyPrinter_initFn____x40_Lean_PrettyPrinter_Basic___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_PrettyPrinter_backtrackExceptionId = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_PrettyPrinter_backtrackExceptionId);
lean_dec_ref(res);
}l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__1 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__1();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__1);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__2 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__2();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__2);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__3 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__3();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__3);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__4 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__4();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__4);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__5 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__5();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__5);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__6 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__6();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__6);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__7 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__7();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__7);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__8 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__8();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__8);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__9 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__9();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__9);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__10 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__10();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__10);
l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__11 = _init_l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__11();
lean_mark_persistent(l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__11);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
