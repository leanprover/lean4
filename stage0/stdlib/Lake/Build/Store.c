// Lean compiler output
// Module: Lake.Build.Store
// Imports: Lake.Build.Data Lake.Build.Job.Basic Lake.Util.StoreInsts
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
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectSharedExternLibs___redArg(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2;
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_empty;
static lean_object* l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2;
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___redArg(lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectSharedExternLibs(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0;
lean_object* l_Lean_RBNode_forIn_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_BuildStore_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_9 == 0)
{
lean_dec(x_3);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_10; 
x_10 = lean_array_push(x_4, x_3);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
}
else
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_push(x_4, x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1;
x_2 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5;
x_2 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4;
x_3 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3;
x_4 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2;
x_5 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6;
x_2 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9;
x_5 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10;
x_6 = l_Lean_RBNode_forIn_visit___redArg(x_4, x_3, x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildStore_collectModuleFacetArray___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildStore_collectModuleFacetArray___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_3);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_4, x_8, x_3);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_RBNode_insert___at___Lean_NameMap_insert_spec__0___redArg(x_4, x_11, x_3);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
else
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9;
x_5 = lean_box(0);
x_6 = l_Lean_RBNode_forIn_visit___redArg(x_4, x_3, x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildStore_collectModuleFacetMap___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildStore_collectModuleFacetMap___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_9 == 0)
{
lean_dec(x_3);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_10; 
x_10 = lean_array_push(x_4, x_3);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
}
else
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = lean_name_eq(x_6, x_1);
lean_dec(x_6);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_push(x_4, x_3);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_4);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_4);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9;
x_5 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10;
x_6 = l_Lean_RBNode_forIn_visit___redArg(x_4, x_3, x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildStore_collectPackageFacetArray___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildStore_collectPackageFacetArray___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_name_eq(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_push(x_4, x_3);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_4);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9;
x_5 = l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10;
x_6 = l_Lean_RBNode_forIn_visit___redArg(x_4, x_3, x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildStore_collectTargetFacetArray___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_BuildStore_collectTargetFacetArray___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("externLib", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shared", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1;
x_2 = l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectSharedExternLibs___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2;
x_3 = l_Lake_BuildStore_collectTargetFacetArray___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildStore_collectSharedExternLibs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_BuildStore_collectSharedExternLibs___redArg(x_2);
return x_4;
}
}
lean_object* initialize_Lake_Build_Data(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Build_Job_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_StoreInsts(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Store(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Data(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Build_Job_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_StoreInsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_BuildStore_empty = _init_l_Lake_BuildStore_empty();
lean_mark_persistent(l_Lake_BuildStore_empty);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__0);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__1);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__2);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__3);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__4);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__5);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__6);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__7);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__8);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__9);
l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10 = _init_l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10();
lean_mark_persistent(l_Lake_BuildStore_collectModuleFacetArray___redArg___closed__10);
l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0 = _init_l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0();
lean_mark_persistent(l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__0);
l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1 = _init_l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1();
lean_mark_persistent(l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__1);
l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2 = _init_l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2();
lean_mark_persistent(l_Lake_BuildStore_collectSharedExternLibs___redArg___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
