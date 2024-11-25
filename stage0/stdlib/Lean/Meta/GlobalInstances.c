// Lean compiler output
// Module: Lean.Meta.GlobalInstances
// Imports: Lean.Meta.Basic Lean.ScopedEnvExtension
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
uint8_t l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_addGlobalInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addGlobalInstance___closed__1;
LEAN_EXPORT uint8_t lean_is_instance(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__1;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__3;
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isGlobalInstance___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__4;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3_(lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__6;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_globalInstanceExtension;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_addGlobalInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__8;
static lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__1;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__5;
lean_object* l_Lean_PersistentHashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
static lean_object* l_Lean_Meta_isGlobalInstance___closed__1;
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("globalInstanceExtension", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__1;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__2;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__4;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__7;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__6;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__8;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__9;
x_3 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__6;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__6;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_6, 6);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_st_ref_take(x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 4);
lean_dec(x_15);
x_16 = l_Lean_ScopedEnvExtension_addCore___rarg(x_14, x_1, x_2, x_3, x_9);
x_17 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__1;
lean_ctor_set(x_11, 4, x_17);
lean_ctor_set(x_11, 0, x_16);
x_18 = lean_st_ref_set(x_7, x_11, x_12);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_take(x_5, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
x_25 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__2;
lean_ctor_set(x_21, 1, x_25);
x_26 = lean_st_ref_set(x_5, x_21, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_21, 0);
x_34 = lean_ctor_get(x_21, 2);
x_35 = lean_ctor_get(x_21, 3);
x_36 = lean_ctor_get(x_21, 4);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_21);
x_37 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__2;
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_33);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_38, 4, x_36);
x_39 = lean_st_ref_set(x_5, x_38, x_22);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(0);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
x_46 = lean_ctor_get(x_11, 2);
x_47 = lean_ctor_get(x_11, 3);
x_48 = lean_ctor_get(x_11, 5);
x_49 = lean_ctor_get(x_11, 6);
x_50 = lean_ctor_get(x_11, 7);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_51 = l_Lean_ScopedEnvExtension_addCore___rarg(x_44, x_1, x_2, x_3, x_9);
x_52 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__1;
x_53 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_45);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_48);
lean_ctor_set(x_53, 6, x_49);
lean_ctor_set(x_53, 7, x_50);
x_54 = lean_st_ref_set(x_7, x_53, x_12);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_st_ref_take(x_5, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 3);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 4);
lean_inc(x_62);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 lean_ctor_release(x_57, 2);
 lean_ctor_release(x_57, 3);
 lean_ctor_release(x_57, 4);
 x_63 = x_57;
} else {
 lean_dec_ref(x_57);
 x_63 = lean_box(0);
}
x_64 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__2;
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 5, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_59);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_65, 2, x_60);
lean_ctor_set(x_65, 3, x_61);
lean_ctor_set(x_65, 4, x_62);
x_66 = lean_st_ref_set(x_5, x_65, x_58);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_box(0);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
}
static lean_object* _init_l_Lean_Meta_addGlobalInstance___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_globalInstanceExtension;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addGlobalInstance(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_addGlobalInstance___closed__1;
x_9 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addGlobalInstance___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_addGlobalInstance(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_isGlobalInstance___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Name_instBEq;
x_2 = l_Lean_instHashableName;
x_3 = l_Lean_PersistentHashMap_instInhabited(lean_box(0), lean_box(0), x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lean_is_instance(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lean_Meta_isGlobalInstance___closed__1;
x_4 = l_Lean_Meta_addGlobalInstance___closed__1;
x_5 = l_Lean_ScopedEnvExtension_getState___rarg(x_3, x_4, x_1);
lean_dec(x_1);
x_6 = l_Lean_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__2(x_5, x_2);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isGlobalInstance___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_is_instance(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GlobalInstances(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__8);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3____closed__9);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_globalInstanceExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_globalInstanceExtension);
lean_dec_ref(res);
}l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__1 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__1();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__1);
l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__2 = _init_l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__2();
lean_mark_persistent(l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___closed__2);
l_Lean_Meta_addGlobalInstance___closed__1 = _init_l_Lean_Meta_addGlobalInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_addGlobalInstance___closed__1);
l_Lean_Meta_isGlobalInstance___closed__1 = _init_l_Lean_Meta_isGlobalInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_isGlobalInstance___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
