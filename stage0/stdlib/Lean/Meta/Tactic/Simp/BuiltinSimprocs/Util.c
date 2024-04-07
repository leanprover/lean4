// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util
// Imports: Lean.Meta.Tactic.Simp.Simproc
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__13;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__9;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__5;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__6;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__11;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__19;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__7;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__4;
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__12;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__10;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__20;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__16;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__3;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__8;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__17;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__2;
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Simp_evalPropStep___closed__18;
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Bool", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("false", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_evalPropStep___closed__1;
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("False", 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__6;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_false_of_decide", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__8;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__9;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("true", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Simp_evalPropStep___closed__1;
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__12;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("True", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__15;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("eq_true_of_decide", 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__18;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Simp_evalPropStep___closed__19;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Meta_mkDecide(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
if (x_2 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_Simp_evalPropStep___closed__4;
x_15 = l_Lean_Meta_mkEqRefl(x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_19 = l_Lean_Meta_Simp_evalPropStep___closed__11;
x_20 = lean_array_push(x_19, x_1);
x_21 = lean_array_push(x_20, x_18);
x_22 = lean_array_push(x_21, x_17);
x_23 = l_Lean_Meta_Simp_evalPropStep___closed__10;
x_24 = l_Lean_mkAppN(x_23, x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_Meta_Simp_evalPropStep___closed__7;
x_27 = 1;
x_28 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_25);
lean_ctor_set_uint8(x_28, sizeof(void*)*2, x_27);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
x_33 = l_Lean_Meta_Simp_evalPropStep___closed__11;
x_34 = lean_array_push(x_33, x_1);
x_35 = lean_array_push(x_34, x_32);
x_36 = lean_array_push(x_35, x_30);
x_37 = l_Lean_Meta_Simp_evalPropStep___closed__10;
x_38 = l_Lean_mkAppN(x_37, x_36);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = l_Lean_Meta_Simp_evalPropStep___closed__7;
x_41 = 1;
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_39);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
}
else
{
uint8_t x_45; 
lean_dec(x_12);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_11, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_11, 1);
lean_inc(x_50);
lean_dec(x_11);
x_51 = l_Lean_Meta_Simp_evalPropStep___closed__14;
x_52 = l_Lean_Meta_mkEqRefl(x_51, x_6, x_7, x_8, x_9, x_50);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = l_Lean_Expr_appArg_x21(x_49);
lean_dec(x_49);
x_56 = l_Lean_Meta_Simp_evalPropStep___closed__11;
x_57 = lean_array_push(x_56, x_1);
x_58 = lean_array_push(x_57, x_55);
x_59 = lean_array_push(x_58, x_54);
x_60 = l_Lean_Meta_Simp_evalPropStep___closed__20;
x_61 = l_Lean_mkAppN(x_60, x_59);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Lean_Meta_Simp_evalPropStep___closed__17;
x_64 = 1;
x_65 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2, x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_52, 0, x_66);
return x_52;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_67 = lean_ctor_get(x_52, 0);
x_68 = lean_ctor_get(x_52, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_52);
x_69 = l_Lean_Expr_appArg_x21(x_49);
lean_dec(x_49);
x_70 = l_Lean_Meta_Simp_evalPropStep___closed__11;
x_71 = lean_array_push(x_70, x_1);
x_72 = lean_array_push(x_71, x_69);
x_73 = lean_array_push(x_72, x_67);
x_74 = l_Lean_Meta_Simp_evalPropStep___closed__20;
x_75 = l_Lean_mkAppN(x_74, x_73);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
x_77 = l_Lean_Meta_Simp_evalPropStep___closed__17;
x_78 = 1;
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_76);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_68);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_49);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_52);
if (x_82 == 0)
{
return x_52;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_52, 0);
x_84 = lean_ctor_get(x_52, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_52);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_11);
if (x_86 == 0)
{
return x_11;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_11, 0);
x_88 = lean_ctor_get(x_11, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_11);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_Simp_evalPropStep(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_evalPropStep___closed__1 = _init_l_Lean_Meta_Simp_evalPropStep___closed__1();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__1);
l_Lean_Meta_Simp_evalPropStep___closed__2 = _init_l_Lean_Meta_Simp_evalPropStep___closed__2();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__2);
l_Lean_Meta_Simp_evalPropStep___closed__3 = _init_l_Lean_Meta_Simp_evalPropStep___closed__3();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__3);
l_Lean_Meta_Simp_evalPropStep___closed__4 = _init_l_Lean_Meta_Simp_evalPropStep___closed__4();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__4);
l_Lean_Meta_Simp_evalPropStep___closed__5 = _init_l_Lean_Meta_Simp_evalPropStep___closed__5();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__5);
l_Lean_Meta_Simp_evalPropStep___closed__6 = _init_l_Lean_Meta_Simp_evalPropStep___closed__6();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__6);
l_Lean_Meta_Simp_evalPropStep___closed__7 = _init_l_Lean_Meta_Simp_evalPropStep___closed__7();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__7);
l_Lean_Meta_Simp_evalPropStep___closed__8 = _init_l_Lean_Meta_Simp_evalPropStep___closed__8();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__8);
l_Lean_Meta_Simp_evalPropStep___closed__9 = _init_l_Lean_Meta_Simp_evalPropStep___closed__9();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__9);
l_Lean_Meta_Simp_evalPropStep___closed__10 = _init_l_Lean_Meta_Simp_evalPropStep___closed__10();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__10);
l_Lean_Meta_Simp_evalPropStep___closed__11 = _init_l_Lean_Meta_Simp_evalPropStep___closed__11();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__11);
l_Lean_Meta_Simp_evalPropStep___closed__12 = _init_l_Lean_Meta_Simp_evalPropStep___closed__12();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__12);
l_Lean_Meta_Simp_evalPropStep___closed__13 = _init_l_Lean_Meta_Simp_evalPropStep___closed__13();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__13);
l_Lean_Meta_Simp_evalPropStep___closed__14 = _init_l_Lean_Meta_Simp_evalPropStep___closed__14();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__14);
l_Lean_Meta_Simp_evalPropStep___closed__15 = _init_l_Lean_Meta_Simp_evalPropStep___closed__15();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__15);
l_Lean_Meta_Simp_evalPropStep___closed__16 = _init_l_Lean_Meta_Simp_evalPropStep___closed__16();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__16);
l_Lean_Meta_Simp_evalPropStep___closed__17 = _init_l_Lean_Meta_Simp_evalPropStep___closed__17();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__17);
l_Lean_Meta_Simp_evalPropStep___closed__18 = _init_l_Lean_Meta_Simp_evalPropStep___closed__18();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__18);
l_Lean_Meta_Simp_evalPropStep___closed__19 = _init_l_Lean_Meta_Simp_evalPropStep___closed__19();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__19);
l_Lean_Meta_Simp_evalPropStep___closed__20 = _init_l_Lean_Meta_Simp_evalPropStep___closed__20();
lean_mark_persistent(l_Lean_Meta_Simp_evalPropStep___closed__20);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
