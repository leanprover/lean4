// Lean compiler output
// Module: Lake.Build.Store
// Imports: Lake.Build.Data Lake.Util.StoreInsts
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
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray(lean_object*);
static lean_object* l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__2;
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectSharedExternLibs___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_empty;
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__3;
lean_object* l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__1;
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___rarg___closed__1;
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectSharedExternLibs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_BuildStore_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1___rarg(x_1, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_name_eq(x_11, x_1);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_7);
x_2 = x_8;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_10, x_7);
x_2 = x_8;
x_3 = x_14;
goto _start;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_2 = x_8;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_BuildStore_collectModuleFacetArray___rarg___closed__1;
x_5 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1___rarg(x_2, x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_BuildStore_collectModuleFacetArray___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetArray___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BuildStore_collectModuleFacetArray___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1___rarg(x_1, x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_12);
lean_dec(x_6);
x_13 = lean_name_eq(x_12, x_1);
lean_dec(x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_7);
x_2 = x_8;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_RBNode_insert___at_Lean_NameMap_insert___spec__1___rarg(x_10, x_11, x_7);
x_2 = x_8;
x_3 = x_15;
goto _start;
}
}
else
{
lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_2 = x_8;
x_3 = x_17;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_box(0);
x_5 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1___rarg(x_2, x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_BuildStore_collectModuleFacetMap___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectModuleFacetMap___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BuildStore_collectModuleFacetMap___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1___rarg(x_1, x_5, x_3);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_name_eq(x_11, x_1);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_7);
x_2 = x_8;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_10, x_7);
x_2 = x_8;
x_3 = x_14;
goto _start;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_2 = x_8;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_BuildStore_collectModuleFacetArray___rarg___closed__1;
x_5 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1___rarg(x_2, x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_BuildStore_collectPackageFacetArray___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectPackageFacetArray___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BuildStore_collectPackageFacetArray___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 3);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1___rarg(x_1, x_5, x_3);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 2);
lean_inc(x_11);
lean_dec(x_6);
x_12 = lean_name_eq(x_11, x_1);
lean_dec(x_11);
if (x_12 == 0)
{
lean_dec(x_7);
x_2 = x_8;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_push(x_10, x_7);
x_2 = x_8;
x_3 = x_14;
goto _start;
}
}
else
{
lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_2 = x_8;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lake_BuildStore_collectModuleFacetArray___rarg___closed__1;
x_5 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1___rarg(x_2, x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_BuildStore_collectTargetFacetArray___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_forIn_visit___at_Lake_BuildStore_collectTargetFacetArray___spec__1___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BuildStore_collectTargetFacetArray___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("externLib", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shared", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__1;
x_2 = l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectSharedExternLibs___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__3;
x_4 = l_Lake_BuildStore_collectTargetFacetArray___rarg(x_1, x_3, lean_box(0));
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectSharedExternLibs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_BuildStore_collectSharedExternLibs___rarg), 2, 0);
return x_2;
}
}
lean_object* initialize_Lake_Build_Data(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Store(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Data(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_StoreInsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_BuildStore_empty = _init_l_Lake_BuildStore_empty();
lean_mark_persistent(l_Lake_BuildStore_empty);
l_Lake_BuildStore_collectModuleFacetArray___rarg___closed__1 = _init_l_Lake_BuildStore_collectModuleFacetArray___rarg___closed__1();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___rarg___closed__1);
l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__1 = _init_l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__1();
lean_mark_persistent(l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__1);
l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__2 = _init_l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__2();
lean_mark_persistent(l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__2);
l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__3 = _init_l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__3();
lean_mark_persistent(l_Lake_BuildStore_collectSharedExternLibs___rarg___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
