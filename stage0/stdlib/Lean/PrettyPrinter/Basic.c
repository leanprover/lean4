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
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerInternalExceptionId(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_evalConst___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_3, 2);
x_11 = l_Lean_Environment_evalConst___rarg(x_9, x_10, x_1, x_2);
x_12 = l_Lean_ofExcept___at_Lean_PrettyPrinter_runForNodeKind___spec__3___rarg(x_11, x_3, x_4, x_8);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg___boxed), 5, 0);
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
uint8_t x_33; lean_object* x_34; 
lean_dec(x_1);
x_33 = 1;
x_34 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_2, x_33, x_4, x_5, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_apply_4(x_3, x_35, x_4, x_5, x_36);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = !lean_is_exclusive(x_34);
if (x_38 == 0)
{
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_34, 0);
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_34);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; lean_object* x_43; 
lean_dec(x_16);
lean_dec(x_1);
x_42 = 1;
x_43 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_2, x_42, x_4, x_5, x_15);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_apply_4(x_3, x_44, x_4, x_5, x_45);
return x_46;
}
else
{
uint8_t x_47; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_13);
if (x_51 == 0)
{
return x_13;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_13, 0);
x_53 = lean_ctor_get(x_13, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_13);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_ctor_get(x_12, 0);
lean_inc(x_55);
lean_dec(x_12);
lean_ctor_set(x_7, 0, x_55);
return x_7;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_7, 0);
x_57 = lean_ctor_get(x_7, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_7);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_KeyedDeclsAttribute_getValues___rarg(x_1, x_58, x_2);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_inc(x_2);
x_60 = l_Lean_getConstInfo___at___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___spec__1(x_2, x_4, x_5, x_57);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_ConstantInfo_type(x_61);
lean_dec(x_61);
x_64 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__3;
x_65 = l_Lean_Expr_isConstOf(x_63, x_64);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__5;
x_67 = l_Lean_Expr_isConstOf(x_63, x_66);
lean_dec(x_63);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_3);
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_MessageData_ofName(x_69);
x_71 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__7;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
x_73 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__9;
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_MessageData_ofName(x_2);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_PrettyPrinter_runForNodeKind___rarg___closed__11;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwError___at_Lean_PrettyPrinter_runForNodeKind___spec__1___rarg(x_78, x_4, x_5, x_62);
lean_dec(x_5);
lean_dec(x_4);
return x_79;
}
else
{
uint8_t x_80; lean_object* x_81; 
lean_dec(x_1);
x_80 = 1;
x_81 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_2, x_80, x_4, x_5, x_62);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_apply_4(x_3, x_82, x_4, x_5, x_83);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = lean_ctor_get(x_81, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_81, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_87 = x_81;
} else {
 lean_dec_ref(x_81);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
uint8_t x_89; lean_object* x_90; 
lean_dec(x_63);
lean_dec(x_1);
x_89 = 1;
x_90 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_2, x_89, x_4, x_5, x_62);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_apply_4(x_3, x_91, x_4, x_5, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
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
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_60, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_60, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_100 = x_60;
} else {
 lean_dec_ref(x_60);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = lean_ctor_get(x_59, 0);
lean_inc(x_102);
lean_dec(x_59);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_57);
return x_103;
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
LEAN_EXPORT lean_object* l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_evalConst___at_Lean_PrettyPrinter_runForNodeKind___spec__2___rarg(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
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
