// Lean compiler output
// Module: Lean.Util.ReplaceExpr
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
extern lean_object* l_Lean_Expr_Lean_Expr___instance__1;
lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__1;
lean_object* l_unreachable_x21___rarg(lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__2;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object*, lean_object*);
extern lean_object* l___private_Lean_Data_Format_11__be___main___closed__1;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(lean_object*, size_t, lean_object*, lean_object*);
size_t l_Lean_Expr_ReplaceImpl_cacheSize;
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object*, size_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t, lean_object*, lean_object*, lean_object*);
size_t l_USize_mod(size_t, size_t);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replace___main(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1;
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replace(lean_object*, lean_object*);
lean_object* l_Lean_Expr_ReplaceImpl_initCache___closed__3;
lean_object* l_Lean_Expr_ReplaceImpl_initCache;
extern lean_object* l_Lean_Expr_Lean_Expr___instance__1___closed__1;
lean_object* l_monadInhabited___rarg(lean_object*, lean_object*);
static size_t _init_l_Lean_Expr_ReplaceImpl_cacheSize() {
_start:
{
size_t x_1; 
x_1 = 8192;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_cache(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* l_Lean_Expr_ReplaceImpl_cache___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_6 = l_Lean_Expr_ReplaceImpl_cache(x_5, x_2, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Data_Format_11__be___main___closed__1;
x_2 = l_Lean_Expr_Lean_Expr___instance__1;
x_3 = l_monadInhabited___rarg(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_11; 
lean_inc(x_1);
lean_inc(x_3);
x_11 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_7);
switch (lean_obj_tag(x_3)) {
case 5:
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_12);
lean_inc(x_1);
x_15 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_12, x_4);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_13);
x_18 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_13, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_inc(x_3);
x_23 = lean_array_uset(x_22, x_6, x_3);
x_24 = !lean_is_exclusive(x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_3, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_3, 0);
lean_dec(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_expr_update_app(x_3, x_16, x_20);
lean_inc(x_28);
x_29 = lean_array_uset(x_27, x_6, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_18, 0, x_28);
return x_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_3);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_13);
lean_ctor_set_uint64(x_32, sizeof(void*)*2, x_14);
x_33 = lean_expr_update_app(x_32, x_16, x_20);
lean_inc(x_33);
x_34 = lean_array_uset(x_31, x_6, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_18, 1, x_35);
lean_ctor_set(x_18, 0, x_33);
return x_18;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_18, 0);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_18);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_inc(x_3);
x_39 = lean_array_uset(x_38, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_40 = x_3;
} else {
 lean_dec_ref(x_3);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(5, 2, 8);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_12);
lean_ctor_set(x_42, 1, x_13);
lean_ctor_set_uint64(x_42, sizeof(void*)*2, x_14);
x_43 = lean_expr_update_app(x_42, x_16, x_36);
lean_inc(x_43);
x_44 = lean_array_uset(x_41, x_6, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint64_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 2);
lean_inc(x_49);
x_50 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_48);
lean_inc(x_1);
x_51 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_48, x_4);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_49);
x_54 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_49, x_53);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_inc(x_3);
x_59 = lean_array_uset(x_58, x_6, x_3);
x_60 = !lean_is_exclusive(x_3);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_3, 2);
lean_dec(x_61);
x_62 = lean_ctor_get(x_3, 1);
lean_dec(x_62);
x_63 = lean_ctor_get(x_3, 0);
lean_dec(x_63);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_dec(x_57);
x_65 = (uint8_t)((x_50 << 24) >> 61);
x_66 = lean_expr_update_lambda(x_3, x_65, x_52, x_56);
lean_inc(x_66);
x_67 = lean_array_uset(x_64, x_6, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_54, 1, x_68);
lean_ctor_set(x_54, 0, x_66);
return x_54;
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_3);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_dec(x_57);
x_70 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_70, 0, x_47);
lean_ctor_set(x_70, 1, x_48);
lean_ctor_set(x_70, 2, x_49);
lean_ctor_set_uint64(x_70, sizeof(void*)*3, x_50);
x_71 = (uint8_t)((x_50 << 24) >> 61);
x_72 = lean_expr_update_lambda(x_70, x_71, x_52, x_56);
lean_inc(x_72);
x_73 = lean_array_uset(x_69, x_6, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_59);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set(x_54, 1, x_74);
lean_ctor_set(x_54, 0, x_72);
return x_54;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_ctor_get(x_54, 0);
x_76 = lean_ctor_get(x_54, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_54);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_inc(x_3);
x_78 = lean_array_uset(x_77, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_79 = x_3;
} else {
 lean_dec_ref(x_3);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_76, 1);
lean_inc(x_80);
lean_dec(x_76);
if (lean_is_scalar(x_79)) {
 x_81 = lean_alloc_ctor(6, 3, 8);
} else {
 x_81 = x_79;
}
lean_ctor_set(x_81, 0, x_47);
lean_ctor_set(x_81, 1, x_48);
lean_ctor_set(x_81, 2, x_49);
lean_ctor_set_uint64(x_81, sizeof(void*)*3, x_50);
x_82 = (uint8_t)((x_50 << 24) >> 61);
x_83 = lean_expr_update_lambda(x_81, x_82, x_52, x_75);
lean_inc(x_83);
x_84 = lean_array_uset(x_80, x_6, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint64_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_ctor_get(x_3, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_3, 1);
lean_inc(x_88);
x_89 = lean_ctor_get(x_3, 2);
lean_inc(x_89);
x_90 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_88);
lean_inc(x_1);
x_91 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_88, x_4);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_89);
x_94 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_89, x_93);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_inc(x_3);
x_99 = lean_array_uset(x_98, x_6, x_3);
x_100 = !lean_is_exclusive(x_3);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_3, 2);
lean_dec(x_101);
x_102 = lean_ctor_get(x_3, 1);
lean_dec(x_102);
x_103 = lean_ctor_get(x_3, 0);
lean_dec(x_103);
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_dec(x_97);
x_105 = (uint8_t)((x_90 << 24) >> 61);
x_106 = lean_expr_update_forall(x_3, x_105, x_92, x_96);
lean_inc(x_106);
x_107 = lean_array_uset(x_104, x_6, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_99);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_94, 1, x_108);
lean_ctor_set(x_94, 0, x_106);
return x_94;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_3);
x_109 = lean_ctor_get(x_97, 1);
lean_inc(x_109);
lean_dec(x_97);
x_110 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_110, 0, x_87);
lean_ctor_set(x_110, 1, x_88);
lean_ctor_set(x_110, 2, x_89);
lean_ctor_set_uint64(x_110, sizeof(void*)*3, x_90);
x_111 = (uint8_t)((x_90 << 24) >> 61);
x_112 = lean_expr_update_forall(x_110, x_111, x_92, x_96);
lean_inc(x_112);
x_113 = lean_array_uset(x_109, x_6, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_99);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_94, 1, x_114);
lean_ctor_set(x_94, 0, x_112);
return x_94;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_115 = lean_ctor_get(x_94, 0);
x_116 = lean_ctor_get(x_94, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_94);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_inc(x_3);
x_118 = lean_array_uset(x_117, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_119 = x_3;
} else {
 lean_dec_ref(x_3);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
lean_dec(x_116);
if (lean_is_scalar(x_119)) {
 x_121 = lean_alloc_ctor(7, 3, 8);
} else {
 x_121 = x_119;
}
lean_ctor_set(x_121, 0, x_87);
lean_ctor_set(x_121, 1, x_88);
lean_ctor_set(x_121, 2, x_89);
lean_ctor_set_uint64(x_121, sizeof(void*)*3, x_90);
x_122 = (uint8_t)((x_90 << 24) >> 61);
x_123 = lean_expr_update_forall(x_121, x_122, x_92, x_115);
lean_inc(x_123);
x_124 = lean_array_uset(x_120, x_6, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_118);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
case 8:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint64_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_127 = lean_ctor_get(x_3, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_3, 1);
lean_inc(x_128);
x_129 = lean_ctor_get(x_3, 2);
lean_inc(x_129);
x_130 = lean_ctor_get(x_3, 3);
lean_inc(x_130);
x_131 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
lean_inc(x_128);
lean_inc(x_1);
x_132 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_128, x_4);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_129);
lean_inc(x_1);
x_135 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_129, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_130);
x_138 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_130, x_137);
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_ctor_get(x_138, 1);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_inc(x_3);
x_143 = lean_array_uset(x_142, x_6, x_3);
x_144 = !lean_is_exclusive(x_3);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_145 = lean_ctor_get(x_3, 3);
lean_dec(x_145);
x_146 = lean_ctor_get(x_3, 2);
lean_dec(x_146);
x_147 = lean_ctor_get(x_3, 1);
lean_dec(x_147);
x_148 = lean_ctor_get(x_3, 0);
lean_dec(x_148);
x_149 = lean_ctor_get(x_141, 1);
lean_inc(x_149);
lean_dec(x_141);
x_150 = lean_expr_update_let(x_3, x_133, x_136, x_140);
lean_inc(x_150);
x_151 = lean_array_uset(x_149, x_6, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_143);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_138, 1, x_152);
lean_ctor_set(x_138, 0, x_150);
return x_138;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_3);
x_153 = lean_ctor_get(x_141, 1);
lean_inc(x_153);
lean_dec(x_141);
x_154 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_154, 0, x_127);
lean_ctor_set(x_154, 1, x_128);
lean_ctor_set(x_154, 2, x_129);
lean_ctor_set(x_154, 3, x_130);
lean_ctor_set_uint64(x_154, sizeof(void*)*4, x_131);
x_155 = lean_expr_update_let(x_154, x_133, x_136, x_140);
lean_inc(x_155);
x_156 = lean_array_uset(x_153, x_6, x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_143);
lean_ctor_set(x_157, 1, x_156);
lean_ctor_set(x_138, 1, x_157);
lean_ctor_set(x_138, 0, x_155);
return x_138;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_158 = lean_ctor_get(x_138, 0);
x_159 = lean_ctor_get(x_138, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_138);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
lean_inc(x_3);
x_161 = lean_array_uset(x_160, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 lean_ctor_release(x_3, 3);
 x_162 = x_3;
} else {
 lean_dec_ref(x_3);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(8, 4, 8);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_127);
lean_ctor_set(x_164, 1, x_128);
lean_ctor_set(x_164, 2, x_129);
lean_ctor_set(x_164, 3, x_130);
lean_ctor_set_uint64(x_164, sizeof(void*)*4, x_131);
x_165 = lean_expr_update_let(x_164, x_133, x_136, x_158);
lean_inc(x_165);
x_166 = lean_array_uset(x_163, x_6, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_161);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
case 10:
{
lean_object* x_169; lean_object* x_170; uint64_t x_171; lean_object* x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_3, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_3, 1);
lean_inc(x_170);
x_171 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
lean_inc(x_170);
x_172 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_170, x_4);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_ctor_get(x_172, 1);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_inc(x_3);
x_177 = lean_array_uset(x_176, x_6, x_3);
x_178 = !lean_is_exclusive(x_3);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_179 = lean_ctor_get(x_3, 1);
lean_dec(x_179);
x_180 = lean_ctor_get(x_3, 0);
lean_dec(x_180);
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
lean_dec(x_175);
x_182 = lean_expr_update_mdata(x_3, x_174);
lean_inc(x_182);
x_183 = lean_array_uset(x_181, x_6, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_177);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_172, 1, x_184);
lean_ctor_set(x_172, 0, x_182);
return x_172;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_3);
x_185 = lean_ctor_get(x_175, 1);
lean_inc(x_185);
lean_dec(x_175);
x_186 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_186, 0, x_169);
lean_ctor_set(x_186, 1, x_170);
lean_ctor_set_uint64(x_186, sizeof(void*)*2, x_171);
x_187 = lean_expr_update_mdata(x_186, x_174);
lean_inc(x_187);
x_188 = lean_array_uset(x_185, x_6, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_177);
lean_ctor_set(x_189, 1, x_188);
lean_ctor_set(x_172, 1, x_189);
lean_ctor_set(x_172, 0, x_187);
return x_172;
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_190 = lean_ctor_get(x_172, 0);
x_191 = lean_ctor_get(x_172, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_172);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_inc(x_3);
x_193 = lean_array_uset(x_192, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_194 = x_3;
} else {
 lean_dec_ref(x_3);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_191, 1);
lean_inc(x_195);
lean_dec(x_191);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(10, 2, 8);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_169);
lean_ctor_set(x_196, 1, x_170);
lean_ctor_set_uint64(x_196, sizeof(void*)*2, x_171);
x_197 = lean_expr_update_mdata(x_196, x_190);
lean_inc(x_197);
x_198 = lean_array_uset(x_195, x_6, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_193);
lean_ctor_set(x_199, 1, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
case 11:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint64_t x_204; lean_object* x_205; uint8_t x_206; 
x_201 = lean_ctor_get(x_3, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_3, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_3, 2);
lean_inc(x_203);
x_204 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
lean_inc(x_203);
x_205 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_203, x_4);
x_206 = !lean_is_exclusive(x_205);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_205, 0);
x_208 = lean_ctor_get(x_205, 1);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
lean_inc(x_3);
x_210 = lean_array_uset(x_209, x_6, x_3);
x_211 = !lean_is_exclusive(x_3);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_212 = lean_ctor_get(x_3, 2);
lean_dec(x_212);
x_213 = lean_ctor_get(x_3, 1);
lean_dec(x_213);
x_214 = lean_ctor_get(x_3, 0);
lean_dec(x_214);
x_215 = lean_ctor_get(x_208, 1);
lean_inc(x_215);
lean_dec(x_208);
x_216 = lean_expr_update_proj(x_3, x_207);
lean_inc(x_216);
x_217 = lean_array_uset(x_215, x_6, x_216);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_210);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_205, 1, x_218);
lean_ctor_set(x_205, 0, x_216);
return x_205;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_3);
x_219 = lean_ctor_get(x_208, 1);
lean_inc(x_219);
lean_dec(x_208);
x_220 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_220, 0, x_201);
lean_ctor_set(x_220, 1, x_202);
lean_ctor_set(x_220, 2, x_203);
lean_ctor_set_uint64(x_220, sizeof(void*)*3, x_204);
x_221 = lean_expr_update_proj(x_220, x_207);
lean_inc(x_221);
x_222 = lean_array_uset(x_219, x_6, x_221);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_210);
lean_ctor_set(x_223, 1, x_222);
lean_ctor_set(x_205, 1, x_223);
lean_ctor_set(x_205, 0, x_221);
return x_205;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_224 = lean_ctor_get(x_205, 0);
x_225 = lean_ctor_get(x_205, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_205);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_inc(x_3);
x_227 = lean_array_uset(x_226, x_6, x_3);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_228 = x_3;
} else {
 lean_dec_ref(x_3);
 x_228 = lean_box(0);
}
x_229 = lean_ctor_get(x_225, 1);
lean_inc(x_229);
lean_dec(x_225);
if (lean_is_scalar(x_228)) {
 x_230 = lean_alloc_ctor(11, 3, 8);
} else {
 x_230 = x_228;
}
lean_ctor_set(x_230, 0, x_201);
lean_ctor_set(x_230, 1, x_202);
lean_ctor_set(x_230, 2, x_203);
lean_ctor_set_uint64(x_230, sizeof(void*)*3, x_204);
x_231 = lean_expr_update_proj(x_230, x_224);
lean_inc(x_231);
x_232 = lean_array_uset(x_229, x_6, x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_227);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
case 12:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_3);
lean_dec(x_1);
x_235 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1;
x_236 = l_unreachable_x21___rarg(x_235);
x_237 = lean_apply_1(x_236, x_4);
return x_237;
}
default: 
{
lean_object* x_238; 
lean_dec(x_1);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_3);
lean_ctor_set(x_238, 1, x_4);
return x_238;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_1);
x_239 = lean_ctor_get(x_11, 0);
lean_inc(x_239);
lean_dec(x_11);
x_240 = lean_array_uset(x_7, x_6, x_3);
x_241 = lean_ctor_get(x_4, 1);
lean_inc(x_241);
lean_dec(x_4);
lean_inc(x_239);
x_242 = lean_array_uset(x_241, x_6, x_239);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_239);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_245 = lean_ctor_get(x_4, 1);
lean_inc(x_245);
x_246 = lean_array_uget(x_245, x_6);
lean_dec(x_245);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_4);
return x_247;
}
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM(x_1, x_5, x_3, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = lean_box(0);
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8192u);
x_2 = l_Lean_Expr_Lean_Expr___instance__1___closed__1;
x_3 = lean_mk_array(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__1;
x_2 = l_Lean_Expr_ReplaceImpl_initCache___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_initCache() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Expr_ReplaceImpl_initCache___closed__3;
return x_1;
}
}
lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = 8192;
x_4 = l_Lean_Expr_ReplaceImpl_initCache;
x_5 = l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main(x_1, x_3, x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_Expr_replace___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
lean_inc(x_2);
x_3 = lean_apply_1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
switch (lean_obj_tag(x_2)) {
case 5:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_inc(x_1);
x_7 = l_Lean_Expr_replace___main(x_1, x_5);
lean_inc(x_6);
x_8 = l_Lean_Expr_replace___main(x_1, x_6);
x_9 = lean_expr_update_app(x_2, x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_1);
x_13 = l_Lean_Expr_replace___main(x_1, x_10);
lean_inc(x_11);
x_14 = l_Lean_Expr_replace___main(x_1, x_11);
x_15 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set_uint64(x_15, sizeof(void*)*2, x_12);
x_16 = lean_expr_update_app(x_15, x_13, x_14);
return x_16;
}
}
case 6:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_2, 1);
x_19 = lean_ctor_get(x_2, 2);
x_20 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_18);
lean_inc(x_1);
x_21 = l_Lean_Expr_replace___main(x_1, x_18);
lean_inc(x_19);
x_22 = l_Lean_Expr_replace___main(x_1, x_19);
x_23 = (uint8_t)((x_20 << 24) >> 61);
x_24 = lean_expr_update_lambda(x_2, x_23, x_21, x_22);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
lean_inc(x_26);
lean_inc(x_1);
x_29 = l_Lean_Expr_replace___main(x_1, x_26);
lean_inc(x_27);
x_30 = l_Lean_Expr_replace___main(x_1, x_27);
x_31 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set_uint64(x_31, sizeof(void*)*3, x_28);
x_32 = (uint8_t)((x_28 << 24) >> 61);
x_33 = lean_expr_update_lambda(x_31, x_32, x_29, x_30);
return x_33;
}
}
case 7:
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_35);
lean_inc(x_1);
x_38 = l_Lean_Expr_replace___main(x_1, x_35);
lean_inc(x_36);
x_39 = l_Lean_Expr_replace___main(x_1, x_36);
x_40 = (uint8_t)((x_37 << 24) >> 61);
x_41 = lean_expr_update_forall(x_2, x_40, x_38, x_39);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 2);
x_45 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_2);
lean_inc(x_43);
lean_inc(x_1);
x_46 = l_Lean_Expr_replace___main(x_1, x_43);
lean_inc(x_44);
x_47 = l_Lean_Expr_replace___main(x_1, x_44);
x_48 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_48, 0, x_42);
lean_ctor_set(x_48, 1, x_43);
lean_ctor_set(x_48, 2, x_44);
lean_ctor_set_uint64(x_48, sizeof(void*)*3, x_45);
x_49 = (uint8_t)((x_45 << 24) >> 61);
x_50 = lean_expr_update_forall(x_48, x_49, x_46, x_47);
return x_50;
}
}
case 8:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = lean_ctor_get(x_2, 3);
lean_inc(x_52);
lean_inc(x_1);
x_55 = l_Lean_Expr_replace___main(x_1, x_52);
lean_inc(x_53);
lean_inc(x_1);
x_56 = l_Lean_Expr_replace___main(x_1, x_53);
lean_inc(x_54);
x_57 = l_Lean_Expr_replace___main(x_1, x_54);
x_58 = lean_expr_update_let(x_2, x_55, x_56, x_57);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_2, 0);
x_60 = lean_ctor_get(x_2, 1);
x_61 = lean_ctor_get(x_2, 2);
x_62 = lean_ctor_get(x_2, 3);
x_63 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_2);
lean_inc(x_60);
lean_inc(x_1);
x_64 = l_Lean_Expr_replace___main(x_1, x_60);
lean_inc(x_61);
lean_inc(x_1);
x_65 = l_Lean_Expr_replace___main(x_1, x_61);
lean_inc(x_62);
x_66 = l_Lean_Expr_replace___main(x_1, x_62);
x_67 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_61);
lean_ctor_set(x_67, 3, x_62);
lean_ctor_set_uint64(x_67, sizeof(void*)*4, x_63);
x_68 = lean_expr_update_let(x_67, x_64, x_65, x_66);
return x_68;
}
}
case 10:
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
x_71 = l_Lean_Expr_replace___main(x_1, x_70);
x_72 = lean_expr_update_mdata(x_2, x_71);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; uint64_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_2);
lean_inc(x_74);
x_76 = l_Lean_Expr_replace___main(x_1, x_74);
x_77 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_77, 0, x_73);
lean_ctor_set(x_77, 1, x_74);
lean_ctor_set_uint64(x_77, sizeof(void*)*2, x_75);
x_78 = lean_expr_update_mdata(x_77, x_76);
return x_78;
}
}
case 11:
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_2);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_2, 2);
lean_inc(x_80);
x_81 = l_Lean_Expr_replace___main(x_1, x_80);
x_82 = lean_expr_update_proj(x_2, x_81);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_83 = lean_ctor_get(x_2, 0);
x_84 = lean_ctor_get(x_2, 1);
x_85 = lean_ctor_get(x_2, 2);
x_86 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_2);
lean_inc(x_85);
x_87 = l_Lean_Expr_replace___main(x_1, x_85);
x_88 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_84);
lean_ctor_set(x_88, 2, x_85);
lean_ctor_set_uint64(x_88, sizeof(void*)*3, x_86);
x_89 = lean_expr_update_proj(x_88, x_87);
return x_89;
}
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
lean_object* x_90; 
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_3, 0);
lean_inc(x_90);
lean_dec(x_3);
return x_90;
}
}
}
lean_object* l_Lean_Expr_replace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_replace___main(x_1, x_2);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Util_ReplaceExpr(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_ReplaceImpl_cacheSize = _init_l_Lean_Expr_ReplaceImpl_cacheSize();
l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1 = _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_replaceUnsafeM___main___closed__1);
l_Lean_Expr_ReplaceImpl_initCache___closed__1 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__1();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__1);
l_Lean_Expr_ReplaceImpl_initCache___closed__2 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__2();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__2);
l_Lean_Expr_ReplaceImpl_initCache___closed__3 = _init_l_Lean_Expr_ReplaceImpl_initCache___closed__3();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache___closed__3);
l_Lean_Expr_ReplaceImpl_initCache = _init_l_Lean_Expr_ReplaceImpl_initCache();
lean_mark_persistent(l_Lean_Expr_ReplaceImpl_initCache);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
