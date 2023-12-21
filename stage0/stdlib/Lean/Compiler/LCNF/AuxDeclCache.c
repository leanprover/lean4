// Lean compiler output
// Module: Lean.Compiler.LCNF.AuxDeclCache
// Imports: Init Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.DeclHash Lean.Compiler.LCNF.Internalize
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
uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqDecl____x40_Lean_Compiler_LCNF_Basic___hyg_5489_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__6(size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__3;
lean_object* l_Lean_EnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instHashableDecl;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabitedPersistentHashMap___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_EStateM_pure___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___closed__4;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___lambda__1(lean_object*, lean_object*, lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__2;
extern lean_object* l_Lean_Compiler_LCNF_instBEqDecl;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__1;
uint64_t l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266_(lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_auxDeclCacheExt;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normalizeFVarIds(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___closed__3;
static lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___closed__1;
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(lean_object*);
static size_t l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__1;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__3;
x_2 = lean_alloc_closure((void*)(l_EStateM_pure___rarg), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__4;
x_3 = l_Lean_EnvExtensionInterfaceUnsafe_registerExt___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_fget(x_1, x_4);
lean_inc(x_5);
x_10 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqDecl____x40_Lean_Compiler_LCNF_Basic___hyg_5489_(x_5, x_9);
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
lean_dec(x_5);
x_14 = lean_array_fget(x_2, x_4);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__1() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = 5;
x_3 = lean_usize_shift_left(x_1, x_2);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__2() {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__1;
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; size_t x_5; size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = 5;
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__2;
x_7 = lean_usize_land(x_2, x_6);
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
x_13 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqDecl____x40_Lean_Compiler_LCNF_Basic___hyg_5489_(x_3, x_11);
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
x_17 = lean_usize_shift_right(x_2, x_5);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
default: 
{
lean_object* x_19; 
lean_dec(x_3);
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
x_23 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__3(x_20, x_21, lean_box(0), x_22, x_3);
lean_dec(x_21);
lean_dec(x_20);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
lean_inc(x_2);
x_4 = l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266_(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2(x_3, x_5, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__6(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_inc(x_9);
x_11 = l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266_(x_9);
x_12 = lean_uint64_to_usize(x_11);
x_13 = 1;
x_14 = lean_usize_sub(x_1, x_13);
x_15 = 5;
x_16 = lean_usize_mul(x_15, x_14);
x_17 = lean_usize_shift_right(x_12, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_5, x_18);
lean_dec(x_5);
x_20 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5(x_6, x_17, x_1, x_9, x_10);
x_4 = lean_box(0);
x_5 = x_19;
x_6 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_inc(x_3);
x_18 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqDecl____x40_Lean_Compiler_LCNF_Basic___hyg_5489_(x_3, x_17);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
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
x_10 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__2;
x_11 = lean_usize_land(x_2, x_10);
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
x_16 = lean_box(0);
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
lean_inc(x_19);
lean_inc(x_4);
x_21 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqDecl____x40_Lean_Compiler_LCNF_Basic___hyg_5489_(x_4, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_free_object(x_15);
x_22 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_19, x_20, x_4, x_5);
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
lean_inc(x_26);
lean_inc(x_4);
x_28 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqDecl____x40_Lean_Compiler_LCNF_Basic___hyg_5489_(x_4, x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_26, x_27, x_4, x_5);
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
x_36 = lean_usize_shift_right(x_2, x_9);
x_37 = lean_usize_add(x_3, x_8);
x_38 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5(x_35, x_36, x_37, x_4, x_5);
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
x_41 = lean_usize_shift_right(x_2, x_9);
x_42 = lean_usize_add(x_3, x_8);
x_43 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5(x_40, x_41, x_42, x_4, x_5);
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
x_51 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__2;
x_52 = lean_usize_land(x_2, x_51);
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
x_58 = lean_box(0);
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
lean_inc(x_60);
lean_inc(x_4);
x_63 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqDecl____x40_Lean_Compiler_LCNF_Basic___hyg_5489_(x_4, x_60);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_62);
x_64 = l_Lean_PersistentHashMap_mkCollisionNode___rarg(x_60, x_61, x_4, x_5);
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
x_73 = lean_usize_shift_right(x_2, x_50);
x_74 = lean_usize_add(x_3, x_49);
x_75 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5(x_71, x_73, x_74, x_4, x_5);
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
x_84 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__7(x_1, x_83, x_4, x_5);
x_85 = 7;
x_86 = lean_usize_dec_le(x_85, x_3);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_84);
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
x_92 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5___closed__1;
x_93 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__6(x_3, x_90, x_91, lean_box(0), x_83, x_92);
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
x_98 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__7(x_96, x_97, x_4, x_5);
x_99 = 7;
x_100 = lean_usize_dec_le(x_99, x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = l_Lean_PersistentHashMap_getCollisionNodeSize___rarg(x_98);
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
x_106 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5___closed__1;
x_107 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__6(x_3, x_104, x_105, lean_box(0), x_97, x_106);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
x_7 = l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266_(x_2);
x_8 = lean_uint64_to_usize(x_7);
x_9 = 1;
x_10 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5(x_5, x_8, x_9, x_2, x_3);
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
lean_inc(x_2);
x_15 = l___private_Lean_Compiler_LCNF_DeclHash_0__Lean_Compiler_LCNF_hashDecl____x40_Lean_Compiler_LCNF_DeclHash___hyg_266_(x_2);
x_16 = lean_uint64_to_usize(x_15);
x_17 = 1;
x_18 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5(x_13, x_16, x_17, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_insert___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__4(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cacheAuxDecl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_instBEqDecl;
x_2 = l_Lean_Compiler_LCNF_instHashableDecl;
x_3 = l_Lean_PersistentHashMap_instInhabitedPersistentHashMap___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cacheAuxDecl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_auxDeclCacheExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cacheAuxDecl___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_cacheAuxDecl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__3;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_box(0);
lean_ctor_set(x_1, 0, x_9);
lean_inc(x_5);
x_10 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_1, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__1;
x_19 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__2;
x_20 = l_Lean_EnvExtension_getState___rarg(x_18, x_19, x_17);
lean_dec(x_17);
lean_inc(x_11);
x_21 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__1(x_20, x_11);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_free_object(x_13);
x_22 = lean_st_ref_take(x_5, x_16);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_23, 0);
x_27 = lean_ctor_get(x_23, 4);
lean_dec(x_27);
x_28 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_cacheAuxDecl___lambda__1), 3, 2);
lean_closure_set(x_28, 0, x_11);
lean_closure_set(x_28, 1, x_8);
x_29 = l_Lean_EnvExtension_modifyState___rarg(x_19, x_26, x_28);
x_30 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__4;
lean_ctor_set(x_23, 4, x_30);
lean_ctor_set(x_23, 0, x_29);
x_31 = lean_st_ref_set(x_5, x_23, x_24);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_23, 0);
x_39 = lean_ctor_get(x_23, 1);
x_40 = lean_ctor_get(x_23, 2);
x_41 = lean_ctor_get(x_23, 3);
x_42 = lean_ctor_get(x_23, 5);
x_43 = lean_ctor_get(x_23, 6);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_23);
x_44 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_cacheAuxDecl___lambda__1), 3, 2);
lean_closure_set(x_44, 0, x_11);
lean_closure_set(x_44, 1, x_8);
x_45 = l_Lean_EnvExtension_modifyState___rarg(x_19, x_38, x_44);
x_46 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__4;
x_47 = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_40);
lean_ctor_set(x_47, 3, x_41);
lean_ctor_set(x_47, 4, x_46);
lean_ctor_set(x_47, 5, x_42);
lean_ctor_set(x_47, 6, x_43);
x_48 = lean_st_ref_set(x_5, x_47, x_24);
lean_dec(x_5);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_50 = x_48;
} else {
 lean_dec_ref(x_48);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
if (lean_is_scalar(x_50)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_50;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
x_53 = lean_ctor_get(x_21, 0);
lean_inc(x_53);
lean_dec(x_21);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_13, 0, x_54);
return x_13;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__1;
x_59 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__2;
x_60 = l_Lean_EnvExtension_getState___rarg(x_58, x_59, x_57);
lean_dec(x_57);
lean_inc(x_11);
x_61 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__1(x_60, x_11);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_62 = lean_st_ref_take(x_5, x_56);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_63, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_63, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_63, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 5);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 6);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 lean_ctor_release(x_63, 2);
 lean_ctor_release(x_63, 3);
 lean_ctor_release(x_63, 4);
 lean_ctor_release(x_63, 5);
 lean_ctor_release(x_63, 6);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
x_72 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_cacheAuxDecl___lambda__1), 3, 2);
lean_closure_set(x_72, 0, x_11);
lean_closure_set(x_72, 1, x_8);
x_73 = l_Lean_EnvExtension_modifyState___rarg(x_59, x_65, x_72);
x_74 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__4;
if (lean_is_scalar(x_71)) {
 x_75 = lean_alloc_ctor(0, 7, 0);
} else {
 x_75 = x_71;
}
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_67);
lean_ctor_set(x_75, 3, x_68);
lean_ctor_set(x_75, 4, x_74);
lean_ctor_set(x_75, 5, x_69);
lean_ctor_set(x_75, 6, x_70);
x_76 = lean_st_ref_set(x_5, x_75, x_64);
lean_dec(x_5);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
x_79 = lean_box(0);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
x_81 = lean_ctor_get(x_61, 0);
lean_inc(x_81);
lean_dec(x_61);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_56);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_8);
lean_dec(x_5);
x_84 = !lean_is_exclusive(x_10);
if (x_84 == 0)
{
return x_10;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_10, 0);
x_86 = lean_ctor_get(x_10, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_10);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_1, 0);
x_89 = lean_ctor_get(x_1, 1);
x_90 = lean_ctor_get(x_1, 2);
x_91 = lean_ctor_get(x_1, 3);
x_92 = lean_ctor_get(x_1, 4);
x_93 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_94 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_95 = lean_ctor_get(x_1, 5);
lean_inc(x_95);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_1);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_89);
lean_ctor_set(x_97, 2, x_90);
lean_ctor_set(x_97, 3, x_91);
lean_ctor_set(x_97, 4, x_92);
lean_ctor_set(x_97, 5, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*6, x_93);
lean_ctor_set_uint8(x_97, sizeof(void*)*6 + 1, x_94);
lean_inc(x_5);
x_98 = l_Lean_Compiler_LCNF_normalizeFVarIds(x_97, x_4, x_5, x_6);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_st_ref_get(x_5, x_100);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_105 = lean_ctor_get(x_102, 0);
lean_inc(x_105);
lean_dec(x_102);
x_106 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__1;
x_107 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__2;
x_108 = l_Lean_EnvExtension_getState___rarg(x_106, x_107, x_105);
lean_dec(x_105);
lean_inc(x_99);
x_109 = l_Lean_PersistentHashMap_find_x3f___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__1(x_108, x_99);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_104);
x_110 = lean_st_ref_take(x_5, x_103);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_111, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_111, 3);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 5);
lean_inc(x_117);
x_118 = lean_ctor_get(x_111, 6);
lean_inc(x_118);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 lean_ctor_release(x_111, 2);
 lean_ctor_release(x_111, 3);
 lean_ctor_release(x_111, 4);
 lean_ctor_release(x_111, 5);
 lean_ctor_release(x_111, 6);
 x_119 = x_111;
} else {
 lean_dec_ref(x_111);
 x_119 = lean_box(0);
}
x_120 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_cacheAuxDecl___lambda__1), 3, 2);
lean_closure_set(x_120, 0, x_99);
lean_closure_set(x_120, 1, x_88);
x_121 = l_Lean_EnvExtension_modifyState___rarg(x_107, x_113, x_120);
x_122 = l_Lean_Compiler_LCNF_cacheAuxDecl___closed__4;
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(0, 7, 0);
} else {
 x_123 = x_119;
}
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_114);
lean_ctor_set(x_123, 2, x_115);
lean_ctor_set(x_123, 3, x_116);
lean_ctor_set(x_123, 4, x_122);
lean_ctor_set(x_123, 5, x_117);
lean_ctor_set(x_123, 6, x_118);
x_124 = lean_st_ref_set(x_5, x_123, x_112);
lean_dec(x_5);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
x_127 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_99);
lean_dec(x_88);
lean_dec(x_5);
x_129 = lean_ctor_get(x_109, 0);
lean_inc(x_129);
lean_dec(x_109);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_104)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_104;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_103);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_88);
lean_dec(x_5);
x_132 = lean_ctor_get(x_98, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_98, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_134 = x_98;
} else {
 lean_dec_ref(x_98);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_findAtAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; lean_object* x_8; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_insertAux_traverse___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__6(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_cacheAuxDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_cacheAuxDecl(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_DeclHash(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_AuxDeclCache(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_DeclHash(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9____closed__4);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_AuxDeclCache___hyg_9_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_auxDeclCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_auxDeclCacheExt);
lean_dec_ref(res);
}l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__1 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__1();
l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__2 = _init_l_Lean_PersistentHashMap_findAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__2___closed__2();
l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5___closed__1 = _init_l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5___closed__1();
lean_mark_persistent(l_Lean_PersistentHashMap_insertAux___at_Lean_Compiler_LCNF_cacheAuxDecl___spec__5___closed__1);
l_Lean_Compiler_LCNF_cacheAuxDecl___closed__1 = _init_l_Lean_Compiler_LCNF_cacheAuxDecl___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_cacheAuxDecl___closed__1);
l_Lean_Compiler_LCNF_cacheAuxDecl___closed__2 = _init_l_Lean_Compiler_LCNF_cacheAuxDecl___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_cacheAuxDecl___closed__2);
l_Lean_Compiler_LCNF_cacheAuxDecl___closed__3 = _init_l_Lean_Compiler_LCNF_cacheAuxDecl___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_cacheAuxDecl___closed__3);
l_Lean_Compiler_LCNF_cacheAuxDecl___closed__4 = _init_l_Lean_Compiler_LCNF_cacheAuxDecl___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_cacheAuxDecl___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
