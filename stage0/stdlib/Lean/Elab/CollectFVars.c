// Lean compiler output
// Module: Lean.Elab.CollectFVars
// Imports: Init Lean.Util.CollectFVars Lean.Elab.Term
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
lean_object* l_Lean_Elab_Term_removeUnused(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVarsAtFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_removeUnused___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_removeUnused___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalInstances_erase(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main___main(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVarsAtFVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLocalInsts(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_getLCtx(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_removeUnused___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_collectUsedFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Elab_Term_instantiateMVars(x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_Lean_CollectFVars_main___main(x_7, x_1);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = l_Lean_CollectFVars_main___main(x_9, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
lean_inc(x_5);
x_13 = l_Lean_Elab_Term_inferType(x_10, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
x_16 = l_Lean_Elab_Term_collectUsedFVars(x_4, x_14, x_5, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_3 = x_12;
x_4 = x_17;
x_6 = x_18;
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_13, 0);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_13);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
lean_object* l_Lean_Elab_Term_collectUsedFVarsAtFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(x_2, x_2, x_5, x_1, x_3, x_4);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at_Lean_Elab_Term_collectUsedFVarsAtFVars___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Elab_Term_collectUsedFVarsAtFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_collectUsedFVarsAtFVars(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_removeUnused___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_3, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_3);
x_12 = lean_array_fget(x_2, x_11);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = !lean_is_exclusive(x_5);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_5, 0);
x_17 = lean_ctor_get(x_5, 1);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = l_Lean_Expr_fvarId_x21(x_12);
x_25 = l_Lean_NameSet_contains(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_12);
lean_inc(x_24);
x_26 = lean_local_ctx_erase(x_16, x_24);
x_27 = l_Lean_LocalInstances_erase(x_19, x_24);
lean_dec(x_24);
lean_ctor_set(x_13, 0, x_27);
lean_ctor_set(x_5, 0, x_26);
x_3 = x_11;
x_4 = lean_box(0);
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_24);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 1);
lean_dec(x_30);
x_31 = lean_ctor_get(x_14, 0);
lean_dec(x_31);
lean_inc(x_6);
lean_inc(x_12);
x_32 = l_Lean_Elab_Term_inferType(x_12, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_6);
x_35 = l_Lean_Elab_Term_collectUsedFVars(x_22, x_33, x_6, x_34);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_array_push(x_21, x_12);
lean_ctor_set(x_14, 1, x_36);
lean_ctor_set(x_14, 0, x_38);
x_3 = x_11;
x_4 = lean_box(0);
x_7 = x_37;
goto _start;
}
else
{
uint8_t x_40; 
lean_free_object(x_14);
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_13);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; 
lean_dec(x_14);
lean_inc(x_6);
lean_inc(x_12);
x_44 = l_Lean_Elab_Term_inferType(x_12, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_6);
x_47 = l_Lean_Elab_Term_collectUsedFVars(x_22, x_45, x_6, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_array_push(x_21, x_12);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_48);
lean_ctor_set(x_13, 1, x_51);
x_3 = x_11;
x_4 = lean_box(0);
x_7 = x_49;
goto _start;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_22);
lean_dec(x_21);
lean_free_object(x_13);
lean_dec(x_19);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_44, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_55 = x_44;
} else {
 lean_dec_ref(x_44);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_13, 0);
lean_inc(x_57);
lean_dec(x_13);
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
x_61 = l_Lean_Expr_fvarId_x21(x_12);
x_62 = l_Lean_NameSet_contains(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_12);
lean_inc(x_61);
x_63 = lean_local_ctx_erase(x_16, x_61);
x_64 = l_Lean_LocalInstances_erase(x_57, x_61);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_14);
lean_ctor_set(x_5, 1, x_65);
lean_ctor_set(x_5, 0, x_63);
x_3 = x_11;
x_4 = lean_box(0);
goto _start;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_61);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_67 = x_14;
} else {
 lean_dec_ref(x_14);
 x_67 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_12);
x_68 = l_Lean_Elab_Term_inferType(x_12, x_6, x_7);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_6);
x_71 = l_Lean_Elab_Term_collectUsedFVars(x_59, x_69, x_6, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_array_push(x_58, x_12);
if (lean_is_scalar(x_67)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_67;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_57);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_5, 1, x_76);
x_3 = x_11;
x_4 = lean_box(0);
x_7 = x_73;
goto _start;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_78 = lean_ctor_get(x_68, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_68, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_80 = x_68;
} else {
 lean_dec_ref(x_68);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_82 = lean_ctor_get(x_5, 0);
lean_inc(x_82);
lean_dec(x_5);
x_83 = lean_ctor_get(x_13, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_84 = x_13;
} else {
 lean_dec_ref(x_13);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_14, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_14, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
x_88 = l_Lean_Expr_fvarId_x21(x_12);
x_89 = l_Lean_NameSet_contains(x_87, x_88);
lean_dec(x_87);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_12);
lean_inc(x_88);
x_90 = lean_local_ctx_erase(x_82, x_88);
x_91 = l_Lean_LocalInstances_erase(x_83, x_88);
lean_dec(x_88);
if (lean_is_scalar(x_84)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_84;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_14);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_93;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_88);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_95 = x_14;
} else {
 lean_dec_ref(x_14);
 x_95 = lean_box(0);
}
lean_inc(x_6);
lean_inc(x_12);
x_96 = l_Lean_Elab_Term_inferType(x_12, x_6, x_7);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
lean_inc(x_6);
x_99 = l_Lean_Elab_Term_collectUsedFVars(x_86, x_97, x_6, x_98);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_array_push(x_85, x_12);
if (lean_is_scalar(x_95)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_95;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
if (lean_is_scalar(x_84)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_84;
}
lean_ctor_set(x_104, 0, x_83);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_82);
lean_ctor_set(x_105, 1, x_104);
x_3 = x_11;
x_4 = lean_box(0);
x_5 = x_105;
x_7 = x_101;
goto _start;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_95);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
x_107 = lean_ctor_get(x_96, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_96, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_109 = x_96;
} else {
 lean_dec_ref(x_96);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
}
}
else
{
lean_object* x_111; 
lean_dec(x_6);
lean_dec(x_3);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_5);
lean_ctor_set(x_111, 1, x_7);
return x_111;
}
}
}
lean_object* l_Lean_Elab_Term_removeUnused(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_5 = l_Lean_Elab_Term_getLocalInsts(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Elab_Term_getLCtx(x_3, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Array_empty___closed__1;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_array_get_size(x_1);
x_16 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_removeUnused___spec__1(x_1, x_1, x_15, lean_box(0), x_14, x_3, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_19);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_dec(x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = l_Array_reverseAux___main___rarg(x_27, x_29);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_19, 0, x_24);
lean_ctor_set(x_18, 0, x_22);
lean_ctor_set(x_16, 0, x_18);
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_19, 0);
lean_inc(x_31);
lean_dec(x_19);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_reverseAux___main___rarg(x_31, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_18, 1, x_34);
lean_ctor_set(x_18, 0, x_22);
lean_ctor_set(x_16, 0, x_18);
return x_16;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_37 = x_19;
} else {
 lean_dec_ref(x_19);
 x_37 = lean_box(0);
}
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_reverseAux___main___rarg(x_36, x_38);
if (lean_is_scalar(x_37)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_37;
}
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_16, 0, x_41);
return x_16;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_dec(x_16);
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
lean_dec(x_17);
x_44 = lean_ctor_get(x_18, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_45 = x_18;
} else {
 lean_dec_ref(x_18);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_19, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_47 = x_19;
} else {
 lean_dec_ref(x_19);
 x_47 = lean_box(0);
}
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Array_reverseAux___main___rarg(x_46, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
if (lean_is_scalar(x_45)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_45;
}
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_16);
if (x_53 == 0)
{
return x_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_16, 0);
x_55 = lean_ctor_get(x_16, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_16);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_removeUnused___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_Basic_3__iterateRevMAux___main___at_Lean_Elab_Term_removeUnused___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Elab_Term_removeUnused___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_removeUnused(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(lean_object*);
lean_object* initialize_Lean_Elab_Term(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_CollectFVars(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
