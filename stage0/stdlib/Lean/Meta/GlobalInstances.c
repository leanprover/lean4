// Lean compiler output
// Module: Lean.Meta.GlobalInstances
// Imports: Init Lean.Meta.Basic Lean.ScopedEnvExtension
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_is_instance(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isGlobalInstance___boxed(lean_object*, lean_object*);
lean_object* l_id___rarg___boxed(lean_object*);
extern lean_object* l_Lean_instHashableName;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__7;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__3;
lean_object* l_Lean_ScopedEnvExtension_addScopedEntry___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addGlobalInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addLocalEntry___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_isGlobalInstance___closed__1;
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_addGlobalInstance___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_addGlobalInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_globalInstanceExtension;
lean_object* l_Lean_ScopedEnvExtension_getState___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__8;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__2;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__4;
lean_object* l_Lean_ScopedEnvExtension_addEntry___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__6;
uint8_t l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEqName;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(0);
x_4 = l_Std_PersistentHashMap_insert___at_Lean_NameSSet_insert___spec__2(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ginstanceExt");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__4;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____lambda__1), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_id___rarg___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__2;
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__6;
x_3 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__5;
x_4 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__7;
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__8;
x_3 = l_Lean_registerSimpleScopedEnvExtension___rarg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at_Lean_Meta_addGlobalInstance___spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (x_3) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_6);
x_9 = lean_st_ref_take(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_ctor_get(x_10, 0);
x_14 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_13, x_2);
lean_ctor_set(x_10, 0, x_14);
x_15 = lean_st_ref_set(x_7, x_10, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_15, 0, x_18);
return x_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_10, 0);
x_23 = lean_ctor_get(x_10, 1);
x_24 = lean_ctor_get(x_10, 2);
x_25 = lean_ctor_get(x_10, 3);
x_26 = lean_ctor_get(x_10, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_10);
x_27 = l_Lean_ScopedEnvExtension_addEntry___rarg(x_1, x_22, x_2);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_24);
lean_ctor_set(x_28, 3, x_25);
lean_ctor_set(x_28, 4, x_26);
x_29 = lean_st_ref_set(x_7, x_28, x_11);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_31 = x_29;
} else {
 lean_dec_ref(x_29);
 x_31 = lean_box(0);
}
x_32 = lean_box(0);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_6);
x_34 = lean_st_ref_take(x_7, x_8);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_38, x_2);
lean_ctor_set(x_35, 0, x_39);
x_40 = lean_st_ref_set(x_7, x_35, x_36);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
x_43 = lean_box(0);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
x_49 = lean_ctor_get(x_35, 2);
x_50 = lean_ctor_get(x_35, 3);
x_51 = lean_ctor_get(x_35, 4);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
x_52 = l_Lean_ScopedEnvExtension_addLocalEntry___rarg(x_1, x_47, x_2);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
x_54 = lean_st_ref_set(x_7, x_53, x_36);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = lean_box(0);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
default: 
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_59 = lean_ctor_get(x_6, 4);
lean_inc(x_59);
lean_dec(x_6);
x_60 = lean_st_ref_take(x_7, x_8);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = !lean_is_exclusive(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_61, 0);
x_65 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_64, x_59, x_2);
lean_ctor_set(x_61, 0, x_65);
x_66 = lean_st_ref_set(x_7, x_61, x_62);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_73 = lean_ctor_get(x_61, 0);
x_74 = lean_ctor_get(x_61, 1);
x_75 = lean_ctor_get(x_61, 2);
x_76 = lean_ctor_get(x_61, 3);
x_77 = lean_ctor_get(x_61, 4);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_61);
x_78 = l_Lean_ScopedEnvExtension_addScopedEntry___rarg(x_1, x_73, x_59, x_2);
x_79 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_74);
lean_ctor_set(x_79, 2, x_75);
lean_ctor_set(x_79, 3, x_76);
lean_ctor_set(x_79, 4, x_77);
x_80 = lean_st_ref_set(x_7, x_79, x_62);
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
x_83 = lean_box(0);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
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
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_isGlobalInstance___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Name_instBEqName;
x_2 = l_Lean_instHashableName;
x_3 = l_Std_PersistentHashMap_instInhabitedPersistentHashMap___rarg(x_1, x_2);
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
x_6 = l_Std_PersistentHashMap_contains___at_Lean_NameSSet_contains___spec__3(x_5, x_2);
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_GlobalInstances(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__1);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__2);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__3();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__3);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__4);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__5);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__6);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__7);
l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4____closed__8);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_GlobalInstances___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_globalInstanceExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_globalInstanceExtension);
lean_dec_ref(res);
}l_Lean_Meta_addGlobalInstance___closed__1 = _init_l_Lean_Meta_addGlobalInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_addGlobalInstance___closed__1);
l_Lean_Meta_isGlobalInstance___closed__1 = _init_l_Lean_Meta_isGlobalInstance___closed__1();
lean_mark_persistent(l_Lean_Meta_isGlobalInstance___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
