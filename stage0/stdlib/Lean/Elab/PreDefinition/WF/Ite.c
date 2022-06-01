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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__3;
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__5;
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_Meta_iteToDIte___closed__2;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__7;
lean_object* l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__1;
static lean_object* l_Lean_Meta_iteToDIte___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__6;
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_iteToDIte___lambda__1___closed__4;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_iteToDIte___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
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
x_3 = lean_name_mk_string(x_1, x_2);
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
x_3 = lean_name_mk_string(x_1, x_2);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_12 = l_Lean_Expr_getAppFn(x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux(x_1, x_13);
x_15 = l_Lean_Meta_iteToDIte___lambda__1___closed__3;
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_14, x_17);
lean_dec(x_14);
x_19 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_16, x_18);
x_20 = l_Lean_instInhabitedExpr;
x_21 = lean_array_get(x_20, x_19, x_17);
x_22 = l_Lean_Meta_iteToDIte___lambda__1___closed__5;
x_23 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_22, x_4, x_5, x_6);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_unsigned_to_nat(3u);
x_27 = lean_array_get(x_20, x_19, x_26);
x_28 = 0;
lean_inc(x_21);
lean_inc(x_25);
x_29 = l_Lean_mkLambda(x_25, x_28, x_21, x_27);
x_30 = lean_array_set(x_19, x_26, x_29);
x_31 = l_Lean_mkNot(x_21);
x_32 = lean_unsigned_to_nat(4u);
x_33 = lean_array_get(x_20, x_30, x_32);
x_34 = l_Lean_mkLambda(x_25, x_28, x_31, x_33);
x_35 = lean_array_set(x_30, x_32, x_34);
x_36 = l_Lean_Expr_constLevels_x21(x_12);
x_37 = l_Lean_Meta_iteToDIte___lambda__1___closed__7;
x_38 = l_Lean_mkConst(x_37, x_36);
x_39 = l_Lean_mkAppN(x_38, x_35);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_23, 0, x_40);
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_unsigned_to_nat(3u);
x_44 = lean_array_get(x_20, x_19, x_43);
x_45 = 0;
lean_inc(x_21);
lean_inc(x_41);
x_46 = l_Lean_mkLambda(x_41, x_45, x_21, x_44);
x_47 = lean_array_set(x_19, x_43, x_46);
x_48 = l_Lean_mkNot(x_21);
x_49 = lean_unsigned_to_nat(4u);
x_50 = lean_array_get(x_20, x_47, x_49);
x_51 = l_Lean_mkLambda(x_41, x_45, x_48, x_50);
x_52 = lean_array_set(x_47, x_49, x_51);
x_53 = l_Lean_Expr_constLevels_x21(x_12);
x_54 = l_Lean_Meta_iteToDIte___lambda__1___closed__7;
x_55 = l_Lean_mkConst(x_54, x_53);
x_56 = l_Lean_mkAppN(x_55, x_52);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_42);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_iteToDIte___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_1);
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
x_10 = l_Lean_Meta_transform___at_Lean_Meta_zetaReduce___spec__1(x_1, x_7, x_8, x_9, x_2, x_3, x_4, x_5, x_6);
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
l_Lean_Meta_iteToDIte___closed__1 = _init_l_Lean_Meta_iteToDIte___closed__1();
lean_mark_persistent(l_Lean_Meta_iteToDIte___closed__1);
l_Lean_Meta_iteToDIte___closed__2 = _init_l_Lean_Meta_iteToDIte___closed__2();
lean_mark_persistent(l_Lean_Meta_iteToDIte___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
