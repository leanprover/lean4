// Lean compiler output
// Module: Lean.DeclarationRange
// Imports: Lean.Data.DeclarationRange Lean.MonadEnv
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
lean_object* l_Lean_MapDeclarationExtension_insert___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__1;
LEAN_EXPORT lean_object* l_Lean_declRangeExt;
static lean_object* l_Lean_addDeclarationRanges___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__2;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_DeclarationRange___hyg_4_(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_MapDeclarationExtension_contains___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges(lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addBuiltinDeclarationRanges___closed__1;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__3;
uint8_t lean_is_aux_recursor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_builtinDeclRanges;
lean_object* l_Lean_Name_getPrefix(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45_(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__3___closed__1;
lean_object* l_Lean_mkMapDeclarationExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f(lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRanges;
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_noConfusionExt;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_isRec___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_DeclarationRange___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(0);
x_3 = lean_st_mk_ref(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("declRangeExt", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__1;
x_2 = l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__3;
x_3 = l_Lean_mkMapDeclarationExtension___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_addBuiltinDeclarationRanges___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_builtinDeclRanges;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_4 = l_Lean_addBuiltinDeclarationRanges___closed__1;
x_5 = lean_st_ref_take(x_4, x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_6, x_1, x_2);
x_9 = lean_st_ref_set(x_4, x_8, x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
static lean_object* _init_l_Lean_addDeclarationRanges___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_declRangeExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_addDeclarationRanges___rarg___lambda__1___closed__1;
x_5 = l_Lean_MapDeclarationExtension_insert___rarg(x_4, x_3, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = l_Lean_instInhabitedDeclarationRanges;
x_7 = l_Lean_addDeclarationRanges___rarg___lambda__1___closed__1;
lean_inc(x_1);
x_8 = l_Lean_MapDeclarationExtension_contains___rarg(x_6, x_7, x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_addDeclarationRanges___rarg___lambda__1), 3, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_3);
x_11 = lean_apply_1(x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lean_addDeclarationRanges___rarg___lambda__2), 5, 4);
lean_closure_set(x_7, 0, x_3);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_1);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_addDeclarationRanges___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_instInhabitedDeclarationRanges;
x_7 = l_Lean_addDeclarationRanges___rarg___lambda__1___closed__1;
x_8 = l_Lean_MapDeclarationExtension_find_x3f___rarg(x_6, x_7, x_3, x_2);
x_9 = lean_apply_2(x_5, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_findDeclarationRangesCore_x3f___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_3);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRangesCore_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_findDeclarationRangesCore_x3f___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_RBNode_find___at_Lean_NameMap_find_x3f___spec__1___rarg(x_3, x_2);
x_7 = lean_apply_2(x_5, lean_box(0), x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_findDeclarationRanges_x3f___rarg___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addBuiltinDeclarationRanges___closed__1;
x_2 = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(x_2, 0, lean_box(0));
lean_closure_set(x_2, 1, lean_box(0));
lean_closure_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lean_findDeclarationRanges_x3f___rarg___lambda__2___closed__1;
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___rarg___lambda__1___boxed), 3, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_3);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_apply_2(x_11, lean_box(0), x_5);
return x_12;
}
}
}
static lean_object* _init_l_Lean_findDeclarationRanges_x3f___rarg___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_noConfusionExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___rarg___lambda__2), 5, 4);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_4);
lean_inc(x_3);
lean_inc(x_5);
x_9 = lean_is_aux_recursor(x_5, x_3);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_findDeclarationRanges_x3f___rarg___lambda__3___closed__1;
lean_inc(x_3);
x_11 = l_Lean_TagDeclarationExtension_isTagged(x_10, x_5, x_3);
if (x_11 == 0)
{
if (x_7 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_findDeclarationRangesCore_x3f___rarg(x_2, x_6, x_3);
x_13 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_12, x_8);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_Name_getPrefix(x_3);
lean_dec(x_3);
x_15 = l_Lean_findDeclarationRangesCore_x3f___rarg(x_2, x_6, x_14);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_8);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = l_Lean_Name_getPrefix(x_3);
lean_dec(x_3);
x_18 = l_Lean_findDeclarationRangesCore_x3f___rarg(x_2, x_6, x_17);
x_19 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_18, x_8);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_5);
x_20 = l_Lean_Name_getPrefix(x_3);
lean_dec(x_3);
x_21 = l_Lean_findDeclarationRangesCore_x3f___rarg(x_2, x_6, x_20);
x_22 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_21, x_8);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_isRec___rarg(x_1, x_2, x_3);
lean_inc(x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___rarg___lambda__3___boxed), 7, 6);
lean_closure_set(x_8, 0, x_4);
lean_closure_set(x_8, 1, x_1);
lean_closure_set(x_8, 2, x_3);
lean_closure_set(x_8, 3, x_5);
lean_closure_set(x_8, 4, x_6);
lean_closure_set(x_8, 5, x_2);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_inc(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___rarg___lambda__4), 6, 5);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_closure_set(x_7, 2, x_4);
lean_closure_set(x_7, 3, x_3);
lean_closure_set(x_7, 4, x_5);
x_8 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_findDeclarationRanges_x3f___rarg), 4, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_findDeclarationRanges_x3f___rarg___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_findDeclarationRanges_x3f___rarg___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_7);
lean_dec(x_7);
x_9 = l_Lean_findDeclarationRanges_x3f___rarg___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
return x_9;
}
}
lean_object* initialize_Lean_Data_DeclarationRange(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DeclarationRange(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_DeclarationRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_MonadEnv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_DeclarationRange___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_builtinDeclRanges = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_builtinDeclRanges);
lean_dec_ref(res);
}l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__1 = _init_l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__1();
lean_mark_persistent(l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__1);
l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__2 = _init_l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__2();
lean_mark_persistent(l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__2);
l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__3 = _init_l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__3();
lean_mark_persistent(l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45____closed__3);
if (builtin) {res = l_Lean_initFn____x40_Lean_DeclarationRange___hyg_45_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_declRangeExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_declRangeExt);
lean_dec_ref(res);
}l_Lean_addBuiltinDeclarationRanges___closed__1 = _init_l_Lean_addBuiltinDeclarationRanges___closed__1();
lean_mark_persistent(l_Lean_addBuiltinDeclarationRanges___closed__1);
l_Lean_addDeclarationRanges___rarg___lambda__1___closed__1 = _init_l_Lean_addDeclarationRanges___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_addDeclarationRanges___rarg___lambda__1___closed__1);
l_Lean_findDeclarationRanges_x3f___rarg___lambda__2___closed__1 = _init_l_Lean_findDeclarationRanges_x3f___rarg___lambda__2___closed__1();
lean_mark_persistent(l_Lean_findDeclarationRanges_x3f___rarg___lambda__2___closed__1);
l_Lean_findDeclarationRanges_x3f___rarg___lambda__3___closed__1 = _init_l_Lean_findDeclarationRanges_x3f___rarg___lambda__3___closed__1();
lean_mark_persistent(l_Lean_findDeclarationRanges_x3f___rarg___lambda__3___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
