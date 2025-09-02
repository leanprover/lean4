// Lean compiler output
// Module: Lean.Util.CollectAxioms
// Imports: Lean.MonadEnv Lean.Util.FoldConsts
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_collectAxioms___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_environment_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_State_ctorIdx(lean_object*);
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_collectAxioms___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_State_ctorIdx___boxed(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
static lean_object* l_Lean_collectAxioms___redArg___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_CollectAxioms_collect_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_State_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_State_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_CollectAxioms_State_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_8 = lean_array_uget(x_1, x_2);
lean_inc_ref(x_5);
x_9 = l_Lean_CollectAxioms_collect(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___Lean_CollectAxioms_collect_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
x_8 = l_Lean_CollectAxioms_collect(x_6, x_2, x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lean_Expr_getUsedConstants(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_array_get_size(x_4);
x_7 = lean_box(0);
x_8 = lean_nat_dec_lt(x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_6, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_14 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0(x_4, x_12, x_13, x_7, x_2, x_3);
lean_dec_ref(x_4);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_Lean_NameSet_contains(x_4, x_1);
if (x_6 == 0)
{
uint8_t x_7; 
lean_inc_ref(x_5);
lean_inc(x_4);
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_11 = l_Lean_NameSet_insert(x_4, x_1);
lean_inc_ref(x_5);
lean_inc(x_11);
lean_ctor_set(x_3, 0, x_11);
lean_inc_ref(x_10);
x_12 = lean_task_get_own(x_10);
lean_inc(x_1);
x_13 = lean_environment_find(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec_ref(x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get(x_18, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = lean_array_push(x_5, x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_CollectAxioms_collect___lam__0(x_19, x_2, x_21);
return x_22;
}
case 4:
{
lean_object* x_23; lean_object* x_24; 
lean_dec_ref(x_16);
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec(x_1);
x_25 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_25);
lean_dec_ref(x_16);
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_25, 4);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_26, 2);
lean_inc_ref(x_28);
lean_dec_ref(x_26);
lean_inc_ref(x_2);
x_29 = l_Lean_CollectAxioms_collect___lam__0(x_28, x_2, x_3);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = l_List_forM___at___Lean_CollectAxioms_collect_spec__1(x_27, x_2, x_30);
return x_31;
}
case 6:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec(x_1);
x_32 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_16);
x_33 = lean_ctor_get(x_32, 0);
lean_inc_ref(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 2);
lean_inc_ref(x_34);
lean_dec_ref(x_33);
x_35 = l_Lean_CollectAxioms_collect___lam__0(x_34, x_2, x_3);
return x_35;
}
case 7:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec(x_1);
x_36 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_36);
lean_dec_ref(x_16);
x_37 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_37);
lean_dec_ref(x_36);
x_38 = lean_ctor_get(x_37, 2);
lean_inc_ref(x_38);
lean_dec_ref(x_37);
x_39 = l_Lean_CollectAxioms_collect___lam__0(x_38, x_2, x_3);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_11);
lean_dec_ref(x_5);
lean_dec(x_1);
x_40 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_40);
lean_dec(x_16);
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_40);
x_43 = lean_ctor_get(x_41, 2);
lean_inc_ref(x_43);
lean_dec_ref(x_41);
lean_inc_ref(x_2);
x_44 = l_Lean_CollectAxioms_collect___lam__0(x_43, x_2, x_3);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l_Lean_CollectAxioms_collect___lam__0(x_42, x_2, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_1);
x_48 = l_Lean_NameSet_insert(x_4, x_1);
lean_inc_ref(x_5);
lean_inc(x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_5);
lean_inc_ref(x_47);
x_50 = lean_task_get_own(x_47);
lean_inc(x_1);
x_51 = lean_environment_find(x_50, x_1);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
else
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec_ref(x_51);
switch (lean_obj_tag(x_54)) {
case 0:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec_ref(x_49);
x_55 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_55);
lean_dec_ref(x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc_ref(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_56, 2);
lean_inc_ref(x_57);
lean_dec_ref(x_56);
x_58 = lean_array_push(x_5, x_1);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_CollectAxioms_collect___lam__0(x_57, x_2, x_59);
return x_60;
}
case 4:
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_54);
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_49);
return x_62;
}
case 5:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec(x_1);
x_63 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_63);
lean_dec_ref(x_54);
x_64 = lean_ctor_get(x_63, 0);
lean_inc_ref(x_64);
x_65 = lean_ctor_get(x_63, 4);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = lean_ctor_get(x_64, 2);
lean_inc_ref(x_66);
lean_dec_ref(x_64);
lean_inc_ref(x_2);
x_67 = l_Lean_CollectAxioms_collect___lam__0(x_66, x_2, x_49);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_List_forM___at___Lean_CollectAxioms_collect_spec__1(x_65, x_2, x_68);
return x_69;
}
case 6:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec(x_1);
x_70 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_70);
lean_dec_ref(x_54);
x_71 = lean_ctor_get(x_70, 0);
lean_inc_ref(x_71);
lean_dec_ref(x_70);
x_72 = lean_ctor_get(x_71, 2);
lean_inc_ref(x_72);
lean_dec_ref(x_71);
x_73 = l_Lean_CollectAxioms_collect___lam__0(x_72, x_2, x_49);
return x_73;
}
case 7:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec(x_1);
x_74 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_74);
lean_dec_ref(x_54);
x_75 = lean_ctor_get(x_74, 0);
lean_inc_ref(x_75);
lean_dec_ref(x_74);
x_76 = lean_ctor_get(x_75, 2);
lean_inc_ref(x_76);
lean_dec_ref(x_75);
x_77 = l_Lean_CollectAxioms_collect___lam__0(x_76, x_2, x_49);
return x_77;
}
default: 
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_48);
lean_dec_ref(x_5);
lean_dec(x_1);
x_78 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_78);
lean_dec(x_54);
x_79 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc_ref(x_80);
lean_dec_ref(x_78);
x_81 = lean_ctor_get(x_79, 2);
lean_inc_ref(x_81);
lean_dec_ref(x_79);
lean_inc_ref(x_2);
x_82 = l_Lean_CollectAxioms_collect___lam__0(x_81, x_2, x_49);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l_Lean_CollectAxioms_collect___lam__0(x_80, x_2, x_83);
return x_84;
}
}
}
}
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_3);
return x_86;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec_ref(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_collectAxioms___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_NameSet_empty;
return x_1;
}
}
static lean_object* _init_l_Lean_collectAxioms___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_collectAxioms___redArg___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_collectAxioms___redArg___lam__0___closed__1;
x_2 = l_Lean_collectAxioms___redArg___lam__0___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_Lean_collectAxioms___redArg___lam__0___closed__2;
x_5 = l_Lean_CollectAxioms_collect(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_apply_2(x_2, lean_box(0), x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec_ref(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec_ref(x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec_ref(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_collectAxioms___redArg___lam__0), 3, 2);
lean_closure_set(x_8, 0, x_3);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_collectAxioms___redArg(x_2, x_3, x_4);
return x_5;
}
}
lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectAxioms(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_collectAxioms___redArg___lam__0___closed__0 = _init_l_Lean_collectAxioms___redArg___lam__0___closed__0();
lean_mark_persistent(l_Lean_collectAxioms___redArg___lam__0___closed__0);
l_Lean_collectAxioms___redArg___lam__0___closed__1 = _init_l_Lean_collectAxioms___redArg___lam__0___closed__1();
lean_mark_persistent(l_Lean_collectAxioms___redArg___lam__0___closed__1);
l_Lean_collectAxioms___redArg___lam__0___closed__2 = _init_l_Lean_collectAxioms___redArg___lam__0___closed__2();
lean_mark_persistent(l_Lean_collectAxioms___redArg___lam__0___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
