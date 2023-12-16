// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Ite
// Imports: Init Lean.Meta.Transform
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___closed__2;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__6;
static lean_object* l_Lean_Meta_iteToDIte___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__1;
extern lean_object* l_Lean_levelZero;
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__3;
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__7;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__5;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__4;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* _init_l_Lean_Meta_iteToDIte___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ite", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_iteToDIte___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("h", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_iteToDIte___lambda__1___closed__4;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___lambda__1___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("dite", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_iteToDIte___lambda__1___closed__6;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_iteToDIte___lambda__1___closed__2;
x_8 = lean_unsigned_to_nat(5u);
x_9 = l_Lean_Expr_isAppOfArity(x_1, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_12 = l_Lean_Expr_getAppFn(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_13);
x_15 = l_Lean_Meta_iteToDIte___lambda__1___closed__3;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_16, x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_nat_dec_lt(x_17, x_20);
if (x_21 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = l_Lean_instInhabitedExpr;
x_119 = l___private_Init_Util_0__outOfBounds___rarg(x_118);
x_22 = x_119;
goto block_117;
}
else
{
lean_object* x_120; 
x_120 = lean_array_fget(x_19, x_17);
x_22 = x_120;
goto block_117;
}
block_117:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = l_Lean_Meta_iteToDIte___lambda__1___closed__5;
x_24 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_23, x_4, x_5, x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_unsigned_to_nat(3u);
x_28 = lean_nat_dec_lt(x_27, x_20);
lean_dec(x_20);
lean_inc(x_22);
x_29 = l_Lean_mkNot(x_22);
x_30 = l_Lean_Expr_constLevels_x21(x_12);
x_31 = l_Lean_Meta_iteToDIte___lambda__1___closed__7;
x_32 = l_Lean_Expr_const___override(x_31, x_30);
if (x_28 == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_33 = l_Lean_instInhabitedExpr;
x_34 = l___private_Init_Util_0__outOfBounds___rarg(x_33);
x_35 = 0;
lean_inc(x_26);
x_36 = l_Lean_Expr_lam___override(x_26, x_22, x_34, x_35);
x_37 = lean_array_set(x_19, x_27, x_36);
x_38 = lean_array_get_size(x_37);
x_39 = lean_unsigned_to_nat(4u);
x_40 = lean_nat_dec_lt(x_39, x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = l___private_Init_Util_0__outOfBounds___rarg(x_33);
x_42 = l_Lean_Expr_lam___override(x_26, x_29, x_41, x_35);
x_43 = lean_array_set(x_37, x_39, x_42);
x_44 = l_Lean_mkAppN(x_32, x_43);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_24, 0, x_45);
return x_24;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_array_fget(x_37, x_39);
x_47 = l_Lean_Expr_lam___override(x_26, x_29, x_46, x_35);
x_48 = lean_array_set(x_37, x_39, x_47);
x_49 = l_Lean_mkAppN(x_32, x_48);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_24, 0, x_50);
return x_24;
}
}
else
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_array_fget(x_19, x_27);
x_52 = 0;
lean_inc(x_26);
x_53 = l_Lean_Expr_lam___override(x_26, x_22, x_51, x_52);
x_54 = lean_array_set(x_19, x_27, x_53);
x_55 = lean_array_get_size(x_54);
x_56 = lean_unsigned_to_nat(4u);
x_57 = lean_nat_dec_lt(x_56, x_55);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = l_Lean_instInhabitedExpr;
x_59 = l___private_Init_Util_0__outOfBounds___rarg(x_58);
x_60 = l_Lean_Expr_lam___override(x_26, x_29, x_59, x_52);
x_61 = lean_array_set(x_54, x_56, x_60);
x_62 = l_Lean_mkAppN(x_32, x_61);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_24, 0, x_63);
return x_24;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_array_fget(x_54, x_56);
x_65 = l_Lean_Expr_lam___override(x_26, x_29, x_64, x_52);
x_66 = lean_array_set(x_54, x_56, x_65);
x_67 = l_Lean_mkAppN(x_32, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_24, 0, x_68);
return x_24;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_24, 0);
x_70 = lean_ctor_get(x_24, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_24);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_nat_dec_lt(x_71, x_20);
lean_dec(x_20);
lean_inc(x_22);
x_73 = l_Lean_mkNot(x_22);
x_74 = l_Lean_Expr_constLevels_x21(x_12);
x_75 = l_Lean_Meta_iteToDIte___lambda__1___closed__7;
x_76 = l_Lean_Expr_const___override(x_75, x_74);
if (x_72 == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_77 = l_Lean_instInhabitedExpr;
x_78 = l___private_Init_Util_0__outOfBounds___rarg(x_77);
x_79 = 0;
lean_inc(x_69);
x_80 = l_Lean_Expr_lam___override(x_69, x_22, x_78, x_79);
x_81 = lean_array_set(x_19, x_71, x_80);
x_82 = lean_array_get_size(x_81);
x_83 = lean_unsigned_to_nat(4u);
x_84 = lean_nat_dec_lt(x_83, x_82);
lean_dec(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_85 = l___private_Init_Util_0__outOfBounds___rarg(x_77);
x_86 = l_Lean_Expr_lam___override(x_69, x_73, x_85, x_79);
x_87 = lean_array_set(x_81, x_83, x_86);
x_88 = l_Lean_mkAppN(x_76, x_87);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_70);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_91 = lean_array_fget(x_81, x_83);
x_92 = l_Lean_Expr_lam___override(x_69, x_73, x_91, x_79);
x_93 = lean_array_set(x_81, x_83, x_92);
x_94 = l_Lean_mkAppN(x_76, x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_70);
return x_96;
}
}
else
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_97 = lean_array_fget(x_19, x_71);
x_98 = 0;
lean_inc(x_69);
x_99 = l_Lean_Expr_lam___override(x_69, x_22, x_97, x_98);
x_100 = lean_array_set(x_19, x_71, x_99);
x_101 = lean_array_get_size(x_100);
x_102 = lean_unsigned_to_nat(4u);
x_103 = lean_nat_dec_lt(x_102, x_101);
lean_dec(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = l_Lean_instInhabitedExpr;
x_105 = l___private_Init_Util_0__outOfBounds___rarg(x_104);
x_106 = l_Lean_Expr_lam___override(x_69, x_73, x_105, x_98);
x_107 = lean_array_set(x_100, x_102, x_106);
x_108 = l_Lean_mkAppN(x_76, x_107);
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_70);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_111 = lean_array_fget(x_100, x_102);
x_112 = l_Lean_Expr_lam___override(x_69, x_73, x_111, x_98);
x_113 = lean_array_set(x_100, x_102, x_112);
x_114 = l_Lean_mkAppN(x_76, x_113);
x_115 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_70);
return x_116;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_iteToDIte___lambda__2___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_iteToDIte___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_iteToDIte___lambda__1___boxed), 6, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_iteToDIte___closed__1;
x_8 = l_Lean_Meta_iteToDIte___closed__2;
x_9 = 0;
x_10 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_7, x_8, x_9, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_iteToDIte___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_iteToDIte___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Ite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_iteToDIte___lambda__1___closed__1 = _init_l_Lean_Meta_iteToDIte___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_iteToDIte___lambda__1___closed__1);
l_Lean_Meta_iteToDIte___lambda__1___closed__2 = _init_l_Lean_Meta_iteToDIte___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_iteToDIte___lambda__1___closed__2);
l_Lean_Meta_iteToDIte___lambda__1___closed__3 = _init_l_Lean_Meta_iteToDIte___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_iteToDIte___lambda__1___closed__3);
l_Lean_Meta_iteToDIte___lambda__1___closed__4 = _init_l_Lean_Meta_iteToDIte___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_iteToDIte___lambda__1___closed__4);
l_Lean_Meta_iteToDIte___lambda__1___closed__5 = _init_l_Lean_Meta_iteToDIte___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_iteToDIte___lambda__1___closed__5);
l_Lean_Meta_iteToDIte___lambda__1___closed__6 = _init_l_Lean_Meta_iteToDIte___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_iteToDIte___lambda__1___closed__6);
l_Lean_Meta_iteToDIte___lambda__1___closed__7 = _init_l_Lean_Meta_iteToDIte___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_iteToDIte___lambda__1___closed__7);
l_Lean_Meta_iteToDIte___lambda__2___closed__1 = _init_l_Lean_Meta_iteToDIte___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_iteToDIte___lambda__2___closed__1);
l_Lean_Meta_iteToDIte___closed__1 = _init_l_Lean_Meta_iteToDIte___closed__1();
lean_mark_persistent(l_Lean_Meta_iteToDIte___closed__1);
l_Lean_Meta_iteToDIte___closed__2 = _init_l_Lean_Meta_iteToDIte___closed__2();
lean_mark_persistent(l_Lean_Meta_iteToDIte___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
