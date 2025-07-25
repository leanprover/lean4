// Lean compiler output
// Module: Lean.Compiler.ClosedTermCache
// Imports: Lean.Environment
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_(lean_object*, lean_object*);
static lean_object* l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__2;
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedClosedTermCache;
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isClosedTermName(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedClosedTermCache___closed__2;
static lean_object* l_Lean_initFn___closed__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
static lean_object* l_Lean_initFn___lam__0___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
static lean_object* l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__3;
static lean_object* l_Lean_initFn___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_instInhabitedClosedTermCache___closed__0;
LEAN_EXPORT lean_object* l_Lean_closedTermCacheExt;
static lean_object* l_Lean_cacheClosedTermName___closed__0;
static lean_object* l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__0;
static lean_object* l_Lean_instInhabitedClosedTermCache___closed__3;
lean_object* l_List_takeTR_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_instInhabitedClosedTermCache___closed__1;
LEAN_EXPORT lean_object* l_Lean_isClosedTermName___boxed(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70_(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__1;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ClosedTermCache___hyg_70____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__0(lean_object*);
static lean_object* _init_l_Lean_instInhabitedClosedTermCache___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instInhabitedClosedTermCache___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_instInhabitedClosedTermCache___closed__2;
x_3 = l_Lean_instInhabitedClosedTermCache___closed__1;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_instInhabitedClosedTermCache___closed__3;
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Data.PersistentHashMap", 27, 27);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.PersistentHashMap.find!", 28, 28);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key is not in the map", 21, 21);
return x_1;
}
}
static lean_object* _init_l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__2;
x_2 = lean_unsigned_to_nat(14u);
x_3 = lean_unsigned_to_nat(174u);
x_4 = l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__1;
x_5 = l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_27; lean_object* x_28; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_27 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_27);
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_28 = l_Lean_PersistentHashMap_find_x3f___redArg(x_1, x_2, x_27, x_6);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__3;
x_30 = l_panic___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__0(x_29);
x_9 = x_30;
goto block_26;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
lean_dec_ref(x_28);
x_9 = x_31;
goto block_26;
}
block_26:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_ctor_get(x_4, 2);
lean_inc(x_9);
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = l_Lean_PersistentHashMap_insert___redArg(x_1, x_2, x_11, x_6, x_9);
x_15 = l_Lean_NameSet_insert(x_12, x_9);
if (lean_is_scalar(x_8)) {
 x_16 = lean_alloc_ctor(1, 2, 0);
} else {
 x_16 = x_8;
}
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_4, 2, x_16);
lean_ctor_set(x_4, 1, x_15);
lean_ctor_set(x_4, 0, x_14);
x_5 = x_7;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_ctor_get(x_4, 2);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_21 = l_Lean_PersistentHashMap_insert___redArg(x_1, x_2, x_18, x_6, x_9);
x_22 = l_Lean_NameSet_insert(x_19, x_9);
if (lean_is_scalar(x_8)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_8;
}
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_4 = x_24;
x_5 = x_7;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_initFn___lam__0___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 2);
x_9 = l_List_lengthTR___redArg(x_7);
x_10 = l_List_lengthTR___redArg(x_8);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_10);
lean_dec(x_9);
x_12 = l_Lean_initFn___lam__0___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
lean_inc(x_7);
x_13 = l_List_takeTR_go___redArg(x_7, x_7, x_11, x_12);
lean_dec(x_7);
x_14 = l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1(x_1, x_2, x_4, x_6, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_initFn___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_initFn___closed__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Expr_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_2 = l_Lean_initFn___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
x_3 = l_Lean_initFn___closed__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
x_4 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_Compiler_ClosedTermCache___hyg_70____boxed), 6, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = l_Lean_instInhabitedClosedTermCache___closed__3;
x_6 = lean_alloc_closure((void*)(l_Lean_initFn___lam__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
x_8 = 0;
x_9 = l_Lean_registerEnvExtension___redArg(x_6, x_7, x_8, x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_Compiler_ClosedTermCache___hyg_70____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_initFn___lam__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_4);
x_9 = l_Lean_PersistentHashMap_insert___redArg(x_1, x_2, x_7, x_3, x_4);
x_10 = l_Lean_NameSet_insert(x_8, x_4);
lean_ctor_set(x_5, 1, x_10);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
lean_inc(x_4);
x_14 = l_Lean_PersistentHashMap_insert___redArg(x_1, x_2, x_11, x_3, x_4);
x_15 = l_Lean_NameSet_insert(x_12, x_4);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_13);
return x_16;
}
}
}
static lean_object* _init_l_Lean_cacheClosedTermName___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_closedTermCacheExt;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = l_Lean_cacheClosedTermName___closed__0;
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_6 = l_Lean_initFn___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
x_7 = l_Lean_initFn___closed__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
x_8 = lean_alloc_closure((void*)(l_Lean_cacheClosedTermName___lam__0), 5, 4);
lean_closure_set(x_8, 0, x_6);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_3);
x_9 = l_Lean_EnvExtension_modifyState___redArg(x_4, x_1, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Lean_cacheClosedTermName___closed__0;
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_5 = l_Lean_instInhabitedClosedTermCache;
x_6 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe(lean_box(0), x_5, x_3, x_1, x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_initFn___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
x_9 = l_Lean_initFn___closed__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_;
x_10 = l_Lean_PersistentHashMap_find_x3f___redArg(x_8, x_9, x_7, x_2);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_isClosedTermName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = l_Lean_cacheClosedTermName___closed__0;
x_4 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_5 = l_Lean_instInhabitedClosedTermCache;
x_6 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe(lean_box(0), x_5, x_3, x_1, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_NameSet_contains(x_7, x_2);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isClosedTermName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_isClosedTermName(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedClosedTermCache___closed__0 = _init_l_Lean_instInhabitedClosedTermCache___closed__0();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache___closed__0);
l_Lean_instInhabitedClosedTermCache___closed__1 = _init_l_Lean_instInhabitedClosedTermCache___closed__1();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache___closed__1);
l_Lean_instInhabitedClosedTermCache___closed__2 = _init_l_Lean_instInhabitedClosedTermCache___closed__2();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache___closed__2);
l_Lean_instInhabitedClosedTermCache___closed__3 = _init_l_Lean_instInhabitedClosedTermCache___closed__3();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache___closed__3);
l_Lean_instInhabitedClosedTermCache = _init_l_Lean_instInhabitedClosedTermCache();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache);
l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__0 = _init_l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__0();
lean_mark_persistent(l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__0);
l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__1 = _init_l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__1);
l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__2 = _init_l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__2();
lean_mark_persistent(l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__2);
l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__3 = _init_l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__3();
lean_mark_persistent(l_List_foldl___at___Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70__spec__1___closed__3);
l_Lean_initFn___lam__0___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_ = _init_l_Lean_initFn___lam__0___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_();
lean_mark_persistent(l_Lean_initFn___lam__0___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_);
l_Lean_initFn___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_ = _init_l_Lean_initFn___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_();
lean_mark_persistent(l_Lean_initFn___closed__0____x40_Lean_Compiler_ClosedTermCache___hyg_70_);
l_Lean_initFn___closed__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_ = _init_l_Lean_initFn___closed__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_();
lean_mark_persistent(l_Lean_initFn___closed__1____x40_Lean_Compiler_ClosedTermCache___hyg_70_);
if (builtin) {res = l_Lean_initFn____x40_Lean_Compiler_ClosedTermCache___hyg_70_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_closedTermCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_closedTermCacheExt);
lean_dec_ref(res);
}l_Lean_cacheClosedTermName___closed__0 = _init_l_Lean_cacheClosedTermName___closed__0();
lean_mark_persistent(l_Lean_cacheClosedTermName___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
