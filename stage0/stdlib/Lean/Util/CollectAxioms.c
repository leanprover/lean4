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
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_collectAxioms___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_task_get_own(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_CollectAxioms_collect_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lean_CollectAxioms_collect(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
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
lean_dec(x_5);
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
lean_dec(x_2);
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
lean_dec(x_1);
lean_inc(x_2);
x_8 = l_Lean_CollectAxioms_collect(x_6, x_2, x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
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
lean_dec(x_4);
lean_dec(x_2);
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
lean_dec(x_4);
lean_dec(x_2);
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
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0(x_4, x_12, x_13, x_7, x_2, x_3);
lean_dec(x_4);
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
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Lean_NameSet_contains(x_4, x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_Lean_NameSet_insert(x_4, x_1);
lean_inc(x_5);
lean_inc(x_11);
lean_ctor_set(x_3, 0, x_11);
x_12 = lean_task_get_own(x_10);
lean_inc(x_1);
x_13 = lean_environment_find(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
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
lean_dec(x_13);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_box(0);
x_18 = lean_array_push(x_5, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
case 4:
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_3);
return x_22;
}
case 5:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_23 = lean_ctor_get(x_16, 0);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 4);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 2);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_2);
x_27 = l_Lean_CollectAxioms_collect___lam__0(x_26, x_2, x_3);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l_List_forM___at___Lean_CollectAxioms_collect_spec__1(x_25, x_2, x_28);
return x_29;
}
case 6:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_CollectAxioms_collect___lam__0(x_32, x_2, x_3);
return x_33;
}
case 7:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_CollectAxioms_collect___lam__0(x_36, x_2, x_3);
return x_37;
}
default: 
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 2);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_2);
x_42 = l_Lean_CollectAxioms_collect___lam__0(x_41, x_2, x_3);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_CollectAxioms_collect___lam__0(x_40, x_2, x_43);
return x_44;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_3);
x_45 = lean_ctor_get(x_2, 2);
lean_inc(x_45);
lean_inc(x_1);
x_46 = l_Lean_NameSet_insert(x_4, x_1);
lean_inc(x_5);
lean_inc(x_46);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_5);
x_48 = lean_task_get_own(x_45);
lean_inc(x_1);
x_49 = lean_environment_find(x_48, x_1);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_47);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
switch (lean_obj_tag(x_52)) {
case 0:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_47);
lean_dec(x_2);
x_53 = lean_box(0);
x_54 = lean_array_push(x_5, x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_46);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
case 4:
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_47);
return x_58;
}
case 5:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_1);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
lean_dec(x_52);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 4);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 2);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_2);
x_63 = l_Lean_CollectAxioms_collect___lam__0(x_62, x_2, x_47);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_65 = l_List_forM___at___Lean_CollectAxioms_collect_spec__1(x_61, x_2, x_64);
return x_65;
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_1);
x_66 = lean_ctor_get(x_52, 0);
lean_inc(x_66);
lean_dec(x_52);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get(x_67, 2);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_CollectAxioms_collect___lam__0(x_68, x_2, x_47);
return x_69;
}
case 7:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_1);
x_70 = lean_ctor_get(x_52, 0);
lean_inc(x_70);
lean_dec(x_52);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 2);
lean_inc(x_72);
lean_dec(x_71);
x_73 = l_Lean_CollectAxioms_collect___lam__0(x_72, x_2, x_47);
return x_73;
}
default: 
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_46);
lean_dec(x_5);
lean_dec(x_1);
x_74 = lean_ctor_get(x_52, 0);
lean_inc(x_74);
lean_dec(x_52);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 2);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_2);
x_78 = l_Lean_CollectAxioms_collect___lam__0(x_77, x_2, x_47);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_CollectAxioms_collect___lam__0(x_76, x_2, x_79);
return x_80;
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_3);
return x_82;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_CollectAxioms_collect_spec__0(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_collectAxioms___redArg___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_collectAxioms___redArg___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_collectAxioms___redArg___lam__0___closed__0;
x_2 = lean_box(0);
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
x_4 = l_Lean_collectAxioms___redArg___lam__0___closed__1;
x_5 = l_Lean_CollectAxioms_collect(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
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
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
