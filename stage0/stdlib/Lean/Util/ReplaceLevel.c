// Lean compiler output
// Module: Lean.Util.ReplaceLevel
// Imports: Init Lean.Expr
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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___main___rarg(lean_object*, lean_object*);
size_t l_Lean_Expr_ReplaceLevelImpl_cacheSize;
extern lean_object* l_Id_monad;
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__1;
lean_object* l_Lean_mkLevelIMax(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited___closed__1;
lean_object* l_Lean_mkLevelMax(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
lean_object* l_Lean_Expr_replaceLevel___main(lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Level_replace(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_replaceLevel(lean_object*, lean_object*);
lean_object* l_Lean_mkLevelSucc(lean_object*);
lean_object* lean_expr_update_sort(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_StateT_Monad___rarg(lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache;
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__2;
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_List_map___main___at_Lean_Expr_replaceLevel___main___spec__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Level_replace___main(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_const(lean_object*, lean_object*);
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Level_replace___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Level_replace___main(x_1, x_4);
x_6 = l_Lean_mkLevelSucc(x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
lean_inc(x_1);
x_9 = l_Lean_Level_replace___main(x_1, x_7);
x_10 = l_Lean_Level_replace___main(x_1, x_8);
x_11 = l_Lean_mkLevelMax(x_9, x_10);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_Level_replace___main(x_1, x_12);
x_15 = l_Lean_Level_replace___main(x_1, x_13);
x_16 = l_Lean_mkLevelIMax(x_14, x_15);
return x_16;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
else
{
lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
return x_17;
}
}
}
lean_object* l_Lean_Level_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Level_replace___main(x_1, x_2);
return x_3;
}
}
size_t _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_array_uset(x_5, x_1, x_2);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
lean_inc(x_3);
x_8 = lean_array_uset(x_7, x_1, x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceLevelImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Id_monad;
x_2 = l_StateT_Monad___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__1;
x_2 = l_Lean_Expr_Inhabited;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; uint8_t x_10; 
x_5 = lean_ptr_addr(x_3);
x_6 = x_2 == 0 ? 0 : x_5 % x_2;
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_array_uget(x_7, x_6);
x_9 = lean_ptr_addr(x_8);
lean_dec(x_8);
x_10 = x_9 == x_5;
if (x_10 == 0)
{
switch (lean_obj_tag(x_3)) {
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
x_12 = l_Lean_Level_replace___main(x_1, x_11);
lean_inc(x_3);
x_13 = lean_expr_update_sort(x_3, x_12);
x_14 = lean_array_uset(x_7, x_6, x_3);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
lean_inc(x_13);
x_16 = lean_array_uset(x_15, x_6, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
case 4:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
x_20 = lean_alloc_closure((void*)(l_Lean_Level_replace), 2, 1);
lean_closure_set(x_20, 0, x_1);
x_21 = l_List_map___main___rarg(x_20, x_19);
lean_inc(x_3);
x_22 = lean_expr_update_const(x_3, x_21);
x_23 = lean_array_uset(x_7, x_6, x_3);
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
lean_inc(x_22);
x_25 = lean_array_uset(x_24, x_6, x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
case 5:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_7);
x_28 = lean_ctor_get(x_3, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_1);
x_30 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_28, x_4);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_29, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_inc(x_3);
x_38 = lean_array_uset(x_37, x_6, x_3);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_expr_update_app(x_3, x_31, x_35);
lean_inc(x_40);
x_41 = lean_array_uset(x_39, x_6, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_33, 1, x_42);
lean_ctor_set(x_33, 0, x_40);
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_inc(x_3);
x_46 = lean_array_uset(x_45, x_6, x_3);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_expr_update_app(x_3, x_31, x_43);
lean_inc(x_48);
x_49 = lean_array_uset(x_47, x_6, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
case 6:
{
lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_7);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_55 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_52, x_4);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_53, x_57);
x_59 = !lean_is_exclusive(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_inc(x_3);
x_63 = lean_array_uset(x_62, x_6, x_3);
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = (uint8_t)((x_54 << 24) >> 61);
x_66 = lean_expr_update_lambda(x_3, x_65, x_56, x_60);
lean_inc(x_66);
x_67 = lean_array_uset(x_64, x_6, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_63);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_58, 1, x_68);
lean_ctor_set(x_58, 0, x_66);
return x_58;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_69 = lean_ctor_get(x_58, 0);
x_70 = lean_ctor_get(x_58, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_58);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_inc(x_3);
x_72 = lean_array_uset(x_71, x_6, x_3);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
lean_dec(x_70);
x_74 = (uint8_t)((x_54 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_3, x_74, x_56, x_69);
lean_inc(x_75);
x_76 = lean_array_uset(x_73, x_6, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
case 7:
{
lean_object* x_79; lean_object* x_80; uint64_t x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_7);
x_79 = lean_ctor_get(x_3, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 2);
lean_inc(x_80);
x_81 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_1);
x_82 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_79, x_4);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_80, x_84);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_inc(x_3);
x_90 = lean_array_uset(x_89, x_6, x_3);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = (uint8_t)((x_81 << 24) >> 61);
x_93 = lean_expr_update_forall(x_3, x_92, x_83, x_87);
lean_inc(x_93);
x_94 = lean_array_uset(x_91, x_6, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_90);
lean_ctor_set(x_95, 1, x_94);
lean_ctor_set(x_85, 1, x_95);
lean_ctor_set(x_85, 0, x_93);
return x_85;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_96 = lean_ctor_get(x_85, 0);
x_97 = lean_ctor_get(x_85, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_85);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_inc(x_3);
x_99 = lean_array_uset(x_98, x_6, x_3);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_101 = (uint8_t)((x_81 << 24) >> 61);
x_102 = lean_expr_update_forall(x_3, x_101, x_83, x_96);
lean_inc(x_102);
x_103 = lean_array_uset(x_100, x_6, x_102);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
case 8:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_7);
x_106 = lean_ctor_get(x_3, 1);
lean_inc(x_106);
x_107 = lean_ctor_get(x_3, 2);
lean_inc(x_107);
x_108 = lean_ctor_get(x_3, 3);
lean_inc(x_108);
lean_inc(x_1);
x_109 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_106, x_4);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
lean_inc(x_1);
x_112 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_107, x_111);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_108, x_114);
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_ctor_get(x_115, 1);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_inc(x_3);
x_120 = lean_array_uset(x_119, x_6, x_3);
x_121 = lean_ctor_get(x_118, 1);
lean_inc(x_121);
lean_dec(x_118);
x_122 = lean_expr_update_let(x_3, x_110, x_113, x_117);
lean_inc(x_122);
x_123 = lean_array_uset(x_121, x_6, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_120);
lean_ctor_set(x_124, 1, x_123);
lean_ctor_set(x_115, 1, x_124);
lean_ctor_set(x_115, 0, x_122);
return x_115;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_125 = lean_ctor_get(x_115, 0);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_115);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_inc(x_3);
x_128 = lean_array_uset(x_127, x_6, x_3);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_expr_update_let(x_3, x_110, x_113, x_125);
lean_inc(x_130);
x_131 = lean_array_uset(x_129, x_6, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_128);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
case 10:
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; 
lean_dec(x_7);
x_134 = lean_ctor_get(x_3, 1);
lean_inc(x_134);
x_135 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_134, x_4);
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ctor_get(x_135, 1);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_inc(x_3);
x_140 = lean_array_uset(x_139, x_6, x_3);
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec(x_138);
x_142 = lean_expr_update_mdata(x_3, x_137);
lean_inc(x_142);
x_143 = lean_array_uset(x_141, x_6, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_140);
lean_ctor_set(x_144, 1, x_143);
lean_ctor_set(x_135, 1, x_144);
lean_ctor_set(x_135, 0, x_142);
return x_135;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_145 = lean_ctor_get(x_135, 0);
x_146 = lean_ctor_get(x_135, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_135);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_inc(x_3);
x_148 = lean_array_uset(x_147, x_6, x_3);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_150 = lean_expr_update_mdata(x_3, x_145);
lean_inc(x_150);
x_151 = lean_array_uset(x_149, x_6, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
case 11:
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_7);
x_154 = lean_ctor_get(x_3, 2);
lean_inc(x_154);
x_155 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_154, x_4);
x_156 = !lean_is_exclusive(x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_157 = lean_ctor_get(x_155, 0);
x_158 = lean_ctor_get(x_155, 1);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_inc(x_3);
x_160 = lean_array_uset(x_159, x_6, x_3);
x_161 = lean_ctor_get(x_158, 1);
lean_inc(x_161);
lean_dec(x_158);
x_162 = lean_expr_update_proj(x_3, x_157);
lean_inc(x_162);
x_163 = lean_array_uset(x_161, x_6, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_160);
lean_ctor_set(x_164, 1, x_163);
lean_ctor_set(x_155, 1, x_164);
lean_ctor_set(x_155, 0, x_162);
return x_155;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_155, 0);
x_166 = lean_ctor_get(x_155, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_155);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_inc(x_3);
x_168 = lean_array_uset(x_167, x_6, x_3);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = lean_expr_update_proj(x_3, x_165);
lean_inc(x_170);
x_171 = lean_array_uset(x_169, x_6, x_170);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
case 12:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_174 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__2;
x_175 = l_unreachable_x21___rarg(x_174);
x_176 = lean_apply_1(x_175, x_4);
return x_176;
}
default: 
{
lean_object* x_177; 
lean_dec(x_7);
lean_dec(x_1);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_3);
lean_ctor_set(x_177, 1, x_4);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_178 = lean_ctor_get(x_4, 1);
lean_inc(x_178);
x_179 = lean_array_uget(x_178, x_6);
lean_dec(x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_4);
return x_180;
}
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = l_Lean_Expr_Inhabited___closed__1;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Expr_ReplaceLevelImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceLevelImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceLevelImpl_initCache;
x_5 = l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_List_map___main___at_Lean_Expr_replaceLevel___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_1);
x_7 = l_Lean_Level_replace___main(x_1, x_5);
x_8 = l_List_map___main___at_Lean_Expr_replaceLevel___main___spec__1(x_1, x_6);
lean_ctor_set(x_2, 1, x_8);
lean_ctor_set(x_2, 0, x_7);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_1);
x_11 = l_Lean_Level_replace___main(x_1, x_9);
x_12 = l_List_map___main___at_Lean_Expr_replaceLevel___main___spec__1(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Expr_replaceLevel___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = l_Lean_Level_replace___main(x_1, x_3);
x_5 = lean_expr_update_sort(x_2, x_4);
return x_5;
}
case 4:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = l_List_map___main___at_Lean_Expr_replaceLevel___main___spec__1(x_1, x_6);
x_8 = lean_expr_update_const(x_2, x_7);
return x_8;
}
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_1);
x_11 = l_Lean_Expr_replaceLevel___main(x_1, x_9);
x_12 = l_Lean_Expr_replaceLevel___main(x_1, x_10);
x_13 = lean_expr_update_app(x_2, x_11, x_12);
return x_13;
}
case 6:
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
x_16 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_1);
x_17 = l_Lean_Expr_replaceLevel___main(x_1, x_14);
x_18 = l_Lean_Expr_replaceLevel___main(x_1, x_15);
x_19 = (uint8_t)((x_16 << 24) >> 61);
x_20 = lean_expr_update_lambda(x_2, x_19, x_17, x_18);
return x_20;
}
case 7:
{
lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_1);
x_24 = l_Lean_Expr_replaceLevel___main(x_1, x_21);
x_25 = l_Lean_Expr_replaceLevel___main(x_1, x_22);
x_26 = (uint8_t)((x_23 << 24) >> 61);
x_27 = lean_expr_update_forall(x_2, x_26, x_24, x_25);
return x_27;
}
case 8:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_2, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_inc(x_1);
x_31 = l_Lean_Expr_replaceLevel___main(x_1, x_28);
lean_inc(x_1);
x_32 = l_Lean_Expr_replaceLevel___main(x_1, x_29);
x_33 = l_Lean_Expr_replaceLevel___main(x_1, x_30);
x_34 = lean_expr_update_let(x_2, x_31, x_32, x_33);
return x_34;
}
case 10:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = l_Lean_Expr_replaceLevel___main(x_1, x_35);
x_37 = lean_expr_update_mdata(x_2, x_36);
return x_37;
}
case 11:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
x_39 = l_Lean_Expr_replaceLevel___main(x_1, x_38);
x_40 = lean_expr_update_proj(x_2, x_39);
return x_40;
}
default: 
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Lean_Expr_replaceLevel(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_replaceLevel___main(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_ReplaceLevel(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceLevelImpl_cacheSize = _init_l_Lean_Expr_ReplaceLevelImpl_cacheSize();
l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__1 = _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__1);
l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__2 = _init_l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_replaceUnsafeM___main___closed__2);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__1);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__2);
l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache___closed__3);
l_Lean_Expr_ReplaceLevelImpl_initCache = _init_l_Lean_Expr_ReplaceLevelImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceLevelImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
