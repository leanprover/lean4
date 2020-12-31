// Lean compiler output
// Module: Lean.Meta.Tactic.Revert
// Imports: Init Lean.Meta.Tactic.Util
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
lean_object* l_Lean_Meta_revert___lambda__2___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_revert___spec__1___boxed(lean_object*, lean_object*, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_revert___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_revert_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarKind(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_revert___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_revert___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_revert___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_liftMkBindingM___rarg___closed__3;
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_revert___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_HashMap_instInhabitedHashMap___closed__1;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert_match__1(lean_object*);
lean_object* l_Lean_MetavarContext_MkBinding_revert(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_revert_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_revert_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_revert_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_revert___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = x_2 < x_1;
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = x_3;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = x_6;
x_10 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = x_2 + x_11;
x_13 = x_10;
x_14 = lean_array_uset(x_8, x_2, x_13);
x_2 = x_12;
x_3 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_revert___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_Meta_revert___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = l_Lean_Expr_getAppFn(x_9);
lean_dec(x_9);
x_12 = l_Lean_Expr_mvarId_x21(x_11);
lean_dec(x_11);
lean_inc(x_12);
x_13 = l_Lean_Meta_setMVarTag(x_12, x_1, x_3, x_4, x_5, x_6, x_7);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_array_get_size(x_10);
x_17 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_18 = 0;
x_19 = x_10;
x_20 = l_Array_mapMUnsafe_map___at_Lean_Meta_revert___spec__1(x_17, x_18, x_19);
x_21 = x_20;
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_21);
lean_ctor_set(x_13, 0, x_2);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; size_t x_24; size_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_array_get_size(x_10);
x_24 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_25 = 0;
x_26 = x_10;
x_27 = l_Array_mapMUnsafe_map___at_Lean_Meta_revert___spec__1(x_24, x_25, x_26);
x_28 = x_27;
lean_ctor_set(x_2, 1, x_12);
lean_ctor_set(x_2, 0, x_28);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_2);
x_32 = l_Lean_Expr_getAppFn(x_30);
lean_dec(x_30);
x_33 = l_Lean_Expr_mvarId_x21(x_32);
lean_dec(x_32);
lean_inc(x_33);
x_34 = l_Lean_Meta_setMVarTag(x_33, x_1, x_3, x_4, x_5, x_6, x_7);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_36 = x_34;
} else {
 lean_dec_ref(x_34);
 x_36 = lean_box(0);
}
x_37 = lean_array_get_size(x_31);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = 0;
x_40 = x_31;
x_41 = l_Array_mapMUnsafe_map___at_Lean_Meta_revert___spec__1(x_38, x_39, x_40);
x_42 = x_41;
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
if (lean_is_scalar(x_36)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_36;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_35);
return x_44;
}
}
}
static lean_object* _init_l_Lean_Meta_revert___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Parser_Tactic_revert___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_revert___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_revert___lambda__2___closed__1;
lean_inc(x_1);
x_11 = l_Lean_Meta_checkNotAssigned(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_26; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = 0;
lean_inc(x_1);
x_14 = l_Lean_Meta_setMVarKind(x_1, x_13, x_5, x_6, x_7, x_8, x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_47 = lean_array_get_size(x_2);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = 0;
x_50 = x_2;
x_51 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_48, x_49, x_50);
x_52 = x_51;
x_53 = lean_st_ref_get(x_8, x_15);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_6, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_st_ref_get(x_8, x_57);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 2);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Std_HashMap_instInhabitedHashMap___closed__1;
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_62);
lean_ctor_set(x_64, 2, x_63);
lean_inc(x_1);
x_65 = l_Lean_MetavarContext_MkBinding_revert(x_52, x_1, x_3, x_64);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
x_69 = lean_st_ref_take(x_8, x_61);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = !lean_is_exclusive(x_70);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_73 = lean_ctor_get(x_70, 2);
lean_dec(x_73);
lean_ctor_set(x_70, 2, x_68);
x_74 = lean_st_ref_set(x_8, x_70, x_71);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = lean_ctor_get(x_67, 0);
lean_inc(x_76);
lean_dec(x_67);
x_77 = l_Lean_Meta_setMCtx(x_76, x_5, x_6, x_7, x_8, x_75);
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_66);
x_26 = x_77;
goto block_46;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_80);
x_26 = x_81;
goto block_46;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_82 = lean_ctor_get(x_70, 0);
x_83 = lean_ctor_get(x_70, 1);
x_84 = lean_ctor_get(x_70, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_70);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_82);
lean_ctor_set(x_85, 1, x_83);
lean_ctor_set(x_85, 2, x_68);
lean_ctor_set(x_85, 3, x_84);
x_86 = lean_st_ref_set(x_8, x_85, x_71);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = lean_ctor_get(x_67, 0);
lean_inc(x_88);
lean_dec(x_67);
x_89 = l_Lean_Meta_setMCtx(x_88, x_5, x_6, x_7, x_8, x_87);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_66);
lean_ctor_set(x_92, 1, x_90);
x_26 = x_92;
goto block_46;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_93 = lean_ctor_get(x_65, 1);
lean_inc(x_93);
lean_dec(x_65);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = l_Lean_Meta_setMCtx(x_94, x_5, x_6, x_7, x_8, x_61);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_ctor_get(x_93, 1);
lean_inc(x_97);
lean_dec(x_93);
x_98 = lean_st_ref_take(x_8, x_96);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = !lean_is_exclusive(x_99);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_99, 2);
lean_dec(x_102);
lean_ctor_set(x_99, 2, x_97);
x_103 = lean_st_ref_set(x_8, x_99, x_100);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l_Lean_Meta_liftMkBindingM___rarg___closed__3;
x_106 = l_Lean_throwError___at_Lean_Meta_revert___spec__2(x_105, x_5, x_6, x_7, x_8, x_104);
x_26 = x_106;
goto block_46;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_107 = lean_ctor_get(x_99, 0);
x_108 = lean_ctor_get(x_99, 1);
x_109 = lean_ctor_get(x_99, 3);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_99);
x_110 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_110, 2, x_97);
lean_ctor_set(x_110, 3, x_109);
x_111 = lean_st_ref_set(x_8, x_110, x_100);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l_Lean_Meta_liftMkBindingM___rarg___closed__3;
x_114 = l_Lean_throwError___at_Lean_Meta_revert___spec__2(x_113, x_5, x_6, x_7, x_8, x_112);
x_26 = x_114;
goto block_46;
}
}
block_25:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_revert___lambda__1(x_4, x_19, x_5, x_6, x_7, x_8, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
block_46:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 2;
x_30 = l_Lean_Meta_setMVarKind(x_1, x_29, x_5, x_6, x_7, x_8, x_28);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_30, 0, x_33);
x_16 = x_30;
goto block_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
x_16 = x_37;
goto block_25;
}
}
else
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_26, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_26, 1);
lean_inc(x_39);
lean_dec(x_26);
x_40 = 2;
x_41 = l_Lean_Meta_setMVarKind(x_1, x_40, x_5, x_6, x_7, x_8, x_39);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 0, x_38);
x_16 = x_41;
goto block_25;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_44);
x_16 = x_45;
goto block_25;
}
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_11);
if (x_115 == 0)
{
return x_11;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_11, 0);
x_117 = lean_ctor_get(x_11, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_11);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
lean_object* l_Lean_Meta_revert(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = l_Array_isEmpty___rarg(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_box(x_3);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_revert___lambda__2___boxed), 9, 3);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_11);
x_13 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_instMonadLCtxMetaM___spec__2___rarg), 7, 2);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_12);
x_14 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
}
}
lean_object* l_Array_mapMUnsafe_map___at_Lean_Meta_revert___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Meta_revert___spec__1(x_4, x_5, x_3);
return x_6;
}
}
lean_object* l_Lean_throwError___at_Lean_Meta_revert___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_Lean_Meta_revert___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_revert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_revert___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
lean_object* l_Lean_Meta_revert___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_revert___lambda__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
lean_object* l_Lean_Meta_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_revert(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_revert___lambda__2___closed__1 = _init_l_Lean_Meta_revert___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_revert___lambda__2___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
