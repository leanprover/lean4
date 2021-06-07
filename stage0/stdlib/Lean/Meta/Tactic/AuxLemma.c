// Lean compiler output
// Module: Lean.Meta.Tactic.AuxLemma
// Imports: Init Lean.Meta.Basic
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
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_mkAuxLemma___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxLemma___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma_match__2(lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(lean_object*, lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AuxLemmas_lemmas___default___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_mkAuxLemma___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44_(lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxLemma___closed__2;
static lean_object* l_Lean_Meta_instInhabitedAuxLemmas___closed__1;
lean_object* l_Lean_Meta_mkAuxLemma___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_UInt64_toUSize(uint64_t);
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__1;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_mkAuxLemma___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AuxLemmas_lemmas___default___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_AuxLemmas_lemmas___default___closed__2;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_AuxLemmas_idx___default;
lean_object* l_Lean_Meta_mkAuxLemma_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_KernelException_toMessageData(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkAuxLemma___closed__1;
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_mkAuxLemma___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedAuxLemmas;
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_mkAuxLemma___spec__8(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mul(size_t, size_t);
static lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7___closed__1;
lean_object* l_Lean_Meta_auxLemmasExt;
lean_object* l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1(lean_object*);
lean_object* lean_environment_main_module(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static size_t l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__2;
lean_object* l_Lean_Meta_AuxLemmas_lemmas___default;
uint8_t l_USize_decLe(size_t, size_t);
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxLemma___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_mkAuxLemma___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_mkAuxLemma___spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_auxLemmasExt___closed__2;
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_mkAuxLemma___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__2;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
uint8_t l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2(lean_object*, size_t, lean_object*);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_auxLemmasExt___closed__1;
lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxLemma_match__1(lean_object*);
lean_object* lean_add_decl(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_AuxLemmas_idx___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(1u);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AuxLemmas_lemmas___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_AuxLemmas_lemmas___default___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_AuxLemmas_lemmas___default___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_AuxLemmas_lemmas___default___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_AuxLemmas_lemmas___default___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_AuxLemmas_lemmas___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_AuxLemmas_lemmas___default___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_AuxLemmas_lemmas___default___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedAuxLemmas() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedAuxLemmas___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l_Lean_Meta_AuxLemmas_lemmas___default___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__1;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__2;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_auxLemmasExt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_EnvExtensionInterfaceUnsafe_instInhabitedExt___lambda__1), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_auxLemmasExt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_auxLemmasExt___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAuxLemma_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_mkAuxLemma_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkAuxLemma_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_mkAuxLemma_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_mkAuxLemma___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
x_10 = lean_expr_eqv(x_5, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_4, x_11);
lean_dec(x_4);
x_3 = lean_box(0);
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = x_1 << x_2 % (sizeof(size_t) * 8);
return x_3;
}
}
static size_t _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__1;
x_3 = x_2 - x_1;
return x_3;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__2;
x_7 = x_2 & x_6;
x_8 = lean_usize_to_nat(x_7);
x_9 = lean_box(2);
x_10 = lean_array_get(x_9, x_4, x_8);
lean_dec(x_8);
lean_dec(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_expr_eqv(x_3, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
}
case 1:
{
lean_object* x_16; size_t x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = x_2 >> x_5 % (sizeof(size_t) * 8);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_mkAuxLemma___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_mkAuxLemma___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Expr_hash(x_2);
x_5 = (size_t)x_4;
x_6 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2(x_3, x_5, x_2);
return x_6;
}
}
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxLemma___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = l_Lean_KernelException_toMessageData(x_1, x_7);
x_9 = l_Lean_throwError___at_Lean_Meta_setInlineAttribute___spec__1(x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_9;
}
}
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_add_decl(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_throwKernelException___at_Lean_Meta_mkAuxLemma___spec__5(x_12, x_2, x_3, x_4, x_5, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_setEnv___at_Lean_Meta_setInlineAttribute___spec__2(x_14, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_4);
return x_15;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_mkAuxLemma___spec__8(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_5);
return x_6;
}
else
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_fget(x_2, x_5);
x_10 = lean_array_fget(x_3, x_5);
x_11 = l_Lean_Expr_hash(x_9);
x_12 = (size_t)x_11;
x_13 = 1;
x_14 = x_1 - x_13;
x_15 = 5;
x_16 = x_15 * x_14;
x_17 = x_12 >> x_16 % (sizeof(size_t) * 8);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
lean_object* l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_mkAuxLemma___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_array_get_size(x_5);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 0);
lean_dec(x_11);
x_12 = lean_array_push(x_5, x_3);
x_13 = lean_array_push(x_6, x_4);
lean_ctor_set(x_1, 1, x_13);
lean_ctor_set(x_1, 0, x_12);
return x_1;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_array_push(x_5, x_3);
x_15 = lean_array_push(x_6, x_4);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_fget(x_5, x_2);
x_18 = lean_expr_eqv(x_3, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
goto _start;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_1);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_1, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_1, 0);
lean_dec(x_24);
x_25 = lean_array_fset(x_5, x_2, x_3);
x_26 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
lean_ctor_set(x_1, 1, x_26);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_array_fset(x_5, x_2, x_3);
x_28 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
static lean_object* _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = 1;
x_9 = 5;
x_10 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__2;
x_11 = x_2 & x_10;
x_12 = lean_usize_to_nat(x_11);
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_1;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_7, x_12);
x_16 = lean_box(2);
x_17 = lean_array_fset(x_7, x_12, x_16);
switch (lean_obj_tag(x_15)) {
case 0:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_15, 0);
x_20 = lean_ctor_get(x_15, 1);
x_21 = lean_expr_eqv(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_array_fset(x_17, x_12, x_23);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_24);
return x_1;
}
else
{
lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_19);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 0, x_4);
x_25 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_25);
return x_1;
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_expr_eqv(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_array_fset(x_17, x_12, x_30);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_31);
return x_1;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_4);
lean_ctor_set(x_32, 1, x_5);
x_33 = lean_array_fset(x_17, x_12, x_32);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_33);
return x_1;
}
}
}
case 1:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = x_2 >> x_9 % (sizeof(size_t) * 8);
x_37 = x_3 + x_8;
x_38 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7(x_35, x_36, x_37, x_4, x_5);
lean_ctor_set(x_15, 0, x_38);
x_39 = lean_array_fset(x_17, x_12, x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_39);
return x_1;
}
else
{
lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_15, 0);
lean_inc(x_40);
lean_dec(x_15);
x_41 = x_2 >> x_9 % (sizeof(size_t) * 8);
x_42 = x_3 + x_8;
x_43 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7(x_40, x_41, x_42, x_4, x_5);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_array_fset(x_17, x_12, x_44);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_45);
return x_1;
}
}
default: 
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_5);
x_47 = lean_array_fset(x_17, x_12, x_46);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_47);
return x_1;
}
}
}
}
else
{
lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_48 = lean_ctor_get(x_1, 0);
lean_inc(x_48);
lean_dec(x_1);
x_49 = 1;
x_50 = 5;
x_51 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__2;
x_52 = x_2 & x_51;
x_53 = lean_usize_to_nat(x_52);
x_54 = lean_array_get_size(x_48);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_array_fget(x_48, x_53);
x_58 = lean_box(2);
x_59 = lean_array_fset(x_48, x_53, x_58);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_62 = x_57;
} else {
 lean_dec_ref(x_57);
 x_62 = lean_box(0);
}
x_63 = lean_expr_eqv(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Std_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_array_fset(x_59, x_53, x_65);
lean_dec(x_53);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_61);
lean_dec(x_60);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_5);
x_69 = lean_array_fset(x_59, x_53, x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
case 1:
{
lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_57, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_72 = x_57;
} else {
 lean_dec_ref(x_57);
 x_72 = lean_box(0);
}
x_73 = x_2 >> x_50 % (sizeof(size_t) * 8);
x_74 = x_3 + x_49;
x_75 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7(x_71, x_73, x_74, x_4, x_5);
if (lean_is_scalar(x_72)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_72;
}
lean_ctor_set(x_76, 0, x_75);
x_77 = lean_array_fset(x_59, x_53, x_76);
lean_dec(x_53);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
default: 
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_4);
lean_ctor_set(x_79, 1, x_5);
x_80 = lean_array_fset(x_59, x_53, x_79);
lean_dec(x_53);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_1);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; size_t x_85; uint8_t x_86; 
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_mkAuxLemma___spec__9(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = x_85 <= x_3;
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_dec_lt(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_84, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7___closed__1;
x_93 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_mkAuxLemma___spec__8(x_3, x_90, x_91, lean_box(0), x_83, x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_93;
}
else
{
return x_84;
}
}
else
{
return x_84;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_1, 0);
x_95 = lean_ctor_get(x_1, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_1);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Std_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Meta_mkAuxLemma___spec__9(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = x_99 <= x_3;
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Std_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_101, x_102);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_98, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 1);
lean_inc(x_105);
lean_dec(x_98);
x_106 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7___closed__1;
x_107 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_mkAuxLemma___spec__8(x_3, x_104, x_105, lean_box(0), x_97, x_106);
lean_dec(x_105);
lean_dec(x_104);
return x_107;
}
else
{
return x_98;
}
}
else
{
return x_98;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_insert___at_Lean_Meta_mkAuxLemma___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_hash(x_2);
x_8 = (size_t)x_7;
x_9 = 1;
x_10 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7(x_5, x_8, x_9, x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_6, x_11);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_12);
lean_ctor_set(x_1, 0, x_10);
return x_1;
}
else
{
lean_object* x_13; lean_object* x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_1);
x_15 = l_Lean_Expr_hash(x_2);
x_16 = (size_t)x_15;
x_17 = 1;
x_18 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7(x_13, x_16, x_17, x_2, x_3);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_14, x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
lean_object* l_Lean_Meta_mkAuxLemma___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_6, x_8);
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_2);
x_11 = l_Std_PersistentHashMap_insert___at_Lean_Meta_mkAuxLemma___spec__6(x_7, x_3, x_10);
lean_ctor_set(x_4, 1, x_11);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_4);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
x_17 = l_Std_PersistentHashMap_insert___at_Lean_Meta_mkAuxLemma___spec__6(x_13, x_3, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_auxLemma");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkAuxLemma___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkAuxLemma___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAuxLemma(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_auxLemmasExt;
x_15 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_14, x_13);
x_16 = lean_environment_main_module(x_13);
x_17 = l_Lean_Meta_mkAuxLemma___closed__2;
x_18 = l_Lean_Name_append(x_16, x_17);
lean_dec(x_16);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
x_20 = lean_name_mk_numeral(x_18, x_19);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_20);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec(x_15);
x_25 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_mkAuxLemma___spec__1(x_24, x_2);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_free_object(x_9);
x_26 = l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(x_23, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_23);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_take(x_7, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = !lean_is_exclusive(x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_20);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lambda__1), 4, 3);
lean_closure_set(x_33, 0, x_20);
lean_closure_set(x_33, 1, x_1);
lean_closure_set(x_33, 2, x_2);
x_34 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_14, x_32, x_33);
lean_ctor_set(x_29, 0, x_34);
x_35 = lean_st_ref_set(x_7, x_29, x_30);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_20);
return x_35;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_20);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_ctor_get(x_29, 0);
x_41 = lean_ctor_get(x_29, 1);
x_42 = lean_ctor_get(x_29, 2);
x_43 = lean_ctor_get(x_29, 3);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_29);
lean_inc(x_20);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lambda__1), 4, 3);
lean_closure_set(x_44, 0, x_20);
lean_closure_set(x_44, 1, x_1);
lean_closure_set(x_44, 2, x_2);
x_45 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_14, x_40, x_44);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
lean_ctor_set(x_46, 2, x_42);
lean_ctor_set(x_46, 3, x_43);
x_47 = lean_st_ref_set(x_7, x_46, x_30);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_20);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_26);
if (x_51 == 0)
{
return x_26;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_26, 0);
x_53 = lean_ctor_get(x_26, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_26);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_25, 0);
lean_inc(x_55);
lean_dec(x_25);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(x_1, x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_dec(x_56);
lean_free_object(x_9);
x_59 = l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(x_23, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_23);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_st_ref_take(x_7, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = !lean_is_exclusive(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_20);
x_66 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lambda__1), 4, 3);
lean_closure_set(x_66, 0, x_20);
lean_closure_set(x_66, 1, x_1);
lean_closure_set(x_66, 2, x_2);
x_67 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_14, x_65, x_66);
lean_ctor_set(x_62, 0, x_67);
x_68 = lean_st_ref_set(x_7, x_62, x_63);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_20);
return x_68;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_20);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_62, 0);
x_74 = lean_ctor_get(x_62, 1);
x_75 = lean_ctor_get(x_62, 2);
x_76 = lean_ctor_get(x_62, 3);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_62);
lean_inc(x_20);
x_77 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lambda__1), 4, 3);
lean_closure_set(x_77, 0, x_20);
lean_closure_set(x_77, 1, x_1);
lean_closure_set(x_77, 2, x_2);
x_78 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_14, x_73, x_77);
x_79 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set(x_79, 3, x_76);
x_80 = lean_st_ref_set(x_7, x_79, x_63);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_20);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_59);
if (x_84 == 0)
{
return x_59;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_59, 0);
x_86 = lean_ctor_get(x_59, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_59);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_9, 0, x_56);
return x_9;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_88 = lean_ctor_get(x_9, 0);
x_89 = lean_ctor_get(x_9, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_9);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Meta_auxLemmasExt;
x_92 = l_Lean_EnvExtensionInterfaceUnsafe_getState___rarg(x_91, x_90);
x_93 = lean_environment_main_module(x_90);
x_94 = l_Lean_Meta_mkAuxLemma___closed__2;
x_95 = l_Lean_Name_append(x_93, x_94);
lean_dec(x_93);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
x_97 = lean_name_mk_numeral(x_95, x_96);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_97);
x_98 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_1);
lean_ctor_set(x_98, 2, x_2);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_3);
x_100 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
lean_dec(x_92);
x_102 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_mkAuxLemma___spec__1(x_101, x_2);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(x_100, x_4, x_5, x_6, x_7, x_89);
lean_dec(x_100);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_st_ref_take(x_7, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 3);
lean_inc(x_111);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_112 = x_106;
} else {
 lean_dec_ref(x_106);
 x_112 = lean_box(0);
}
lean_inc(x_97);
x_113 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lambda__1), 4, 3);
lean_closure_set(x_113, 0, x_97);
lean_closure_set(x_113, 1, x_1);
lean_closure_set(x_113, 2, x_2);
x_114 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_91, x_108, x_113);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 4, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_109);
lean_ctor_set(x_115, 2, x_110);
lean_ctor_set(x_115, 3, x_111);
x_116 = lean_st_ref_set(x_7, x_115, x_107);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_97);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_97);
lean_dec(x_2);
lean_dec(x_1);
x_120 = lean_ctor_get(x_103, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_103, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_122 = x_103;
} else {
 lean_dec_ref(x_103);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_124 = lean_ctor_get(x_102, 0);
lean_inc(x_124);
lean_dec(x_102);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_List_beq___at_Lean_OpenDecl_instToStringOpenDecl___spec__1(x_1, x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; 
lean_dec(x_125);
x_128 = l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(x_100, x_4, x_5, x_6, x_7, x_89);
lean_dec(x_100);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_st_ref_take(x_7, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 2);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 3);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
lean_inc(x_97);
x_138 = lean_alloc_closure((void*)(l_Lean_Meta_mkAuxLemma___lambda__1), 4, 3);
lean_closure_set(x_138, 0, x_97);
lean_closure_set(x_138, 1, x_1);
lean_closure_set(x_138, 2, x_2);
x_139 = l_Lean_EnvExtensionInterfaceUnsafe_imp___elambda__2___rarg(x_91, x_133, x_138);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(0, 4, 0);
} else {
 x_140 = x_137;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_134);
lean_ctor_set(x_140, 2, x_135);
lean_ctor_set(x_140, 3, x_136);
x_141 = lean_st_ref_set(x_7, x_140, x_132);
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_97);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_97);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_ctor_get(x_128, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_128, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_147 = x_128;
} else {
 lean_dec_ref(x_128);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; 
lean_dec(x_100);
lean_dec(x_97);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_125);
lean_ctor_set(x_149, 1, x_89);
return x_149;
}
}
}
}
}
lean_object* l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_mkAuxLemma___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_PersistentHashMap_findAtAux___at_Lean_Meta_mkAuxLemma___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_mkAuxLemma___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_PersistentHashMap_find_x3f___at_Lean_Meta_mkAuxLemma___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_throwKernelException___at_Lean_Meta_mkAuxLemma___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwKernelException___at_Lean_Meta_mkAuxLemma___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addDecl___at_Lean_Meta_mkAuxLemma___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_mkAuxLemma___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Std_PersistentHashMap_insertAux_traverse___at_Lean_Meta_mkAuxLemma___spec__8(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
lean_object* l_Lean_Meta_mkAuxLemma___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_mkAuxLemma(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Basic(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_AuxLemmas_idx___default = _init_l_Lean_Meta_AuxLemmas_idx___default();
lean_mark_persistent(l_Lean_Meta_AuxLemmas_idx___default);
l_Lean_Meta_AuxLemmas_lemmas___default___closed__1 = _init_l_Lean_Meta_AuxLemmas_lemmas___default___closed__1();
lean_mark_persistent(l_Lean_Meta_AuxLemmas_lemmas___default___closed__1);
l_Lean_Meta_AuxLemmas_lemmas___default___closed__2 = _init_l_Lean_Meta_AuxLemmas_lemmas___default___closed__2();
lean_mark_persistent(l_Lean_Meta_AuxLemmas_lemmas___default___closed__2);
l_Lean_Meta_AuxLemmas_lemmas___default___closed__3 = _init_l_Lean_Meta_AuxLemmas_lemmas___default___closed__3();
lean_mark_persistent(l_Lean_Meta_AuxLemmas_lemmas___default___closed__3);
l_Lean_Meta_AuxLemmas_lemmas___default = _init_l_Lean_Meta_AuxLemmas_lemmas___default();
lean_mark_persistent(l_Lean_Meta_AuxLemmas_lemmas___default);
l_Lean_Meta_instInhabitedAuxLemmas___closed__1 = _init_l_Lean_Meta_instInhabitedAuxLemmas___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedAuxLemmas___closed__1);
l_Lean_Meta_instInhabitedAuxLemmas = _init_l_Lean_Meta_instInhabitedAuxLemmas();
lean_mark_persistent(l_Lean_Meta_instInhabitedAuxLemmas);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44____closed__2);
l_Lean_Meta_auxLemmasExt___closed__1 = _init_l_Lean_Meta_auxLemmasExt___closed__1();
lean_mark_persistent(l_Lean_Meta_auxLemmasExt___closed__1);
l_Lean_Meta_auxLemmasExt___closed__2 = _init_l_Lean_Meta_auxLemmasExt___closed__2();
lean_mark_persistent(l_Lean_Meta_auxLemmasExt___closed__2);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_AuxLemma___hyg_44_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_auxLemmasExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_auxLemmasExt);
lean_dec_ref(res);
l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__1 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__1();
l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__2 = _init_l_Std_PersistentHashMap_findAux___at_Lean_Meta_mkAuxLemma___spec__2___closed__2();
l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7___closed__1 = _init_l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7___closed__1();
lean_mark_persistent(l_Std_PersistentHashMap_insertAux___at_Lean_Meta_mkAuxLemma___spec__7___closed__1);
l_Lean_Meta_mkAuxLemma___closed__1 = _init_l_Lean_Meta_mkAuxLemma___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAuxLemma___closed__1);
l_Lean_Meta_mkAuxLemma___closed__2 = _init_l_Lean_Meta_mkAuxLemma___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAuxLemma___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
