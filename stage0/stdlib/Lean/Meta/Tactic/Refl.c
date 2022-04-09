// Lean compiler output
// Module: Lean.Meta.Tactic.Refl
// Imports: Init Lean.Meta.Reduce Lean.Meta.Tactic.Util
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
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_refl_useReduceAll(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_refl_useReduceAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_reduce(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_refl___closed__2;
static lean_object* l_Lean_Meta_refl___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_refl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_refl___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_refl___lambda__2___closed__5;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_refl___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
static lean_object* l_Lean_Meta_refl___lambda__1___closed__1;
static lean_object* l_Lean_Meta_refl___lambda__2___closed__7;
static lean_object* l_Lean_Meta_refl___lambda__1___closed__4;
static lean_object* l_Lean_Meta_refl___lambda__2___closed__3;
static lean_object* l_Lean_Meta_refl___lambda__2___closed__2;
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_refl___lambda__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getTransparency(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_refl___lambda__2___closed__4;
static lean_object* l_Lean_Meta_refl___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_refl___lambda__1___closed__3;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_refl___lambda__2___closed__8;
static lean_object* l_Lean_Meta_refl___lambda__4___closed__3;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_refl___lambda__2___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_refl_useReduceAll(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (x_1 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = l_Lean_Expr_hasFVar(x_2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Expr_hasMVar(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Meta_getTransparency(x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
switch (lean_obj_tag(x_15)) {
case 2:
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = 0;
x_19 = lean_box(x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
case 3:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
lean_dec(x_25);
x_26 = 0;
x_27 = lean_box(x_26);
lean_ctor_set(x_14, 0, x_27);
return x_14;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = 0;
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_28);
return x_31;
}
}
default: 
{
uint8_t x_32; 
lean_dec(x_15);
x_32 = !lean_is_exclusive(x_14);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_14, 0);
lean_dec(x_33);
x_34 = 1;
x_35 = lean_box(x_34);
lean_ctor_set(x_14, 0, x_35);
return x_14;
}
else
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_dec(x_14);
x_37 = 1;
x_38 = lean_box(x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
}
}
}
else
{
uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
return x_42;
}
}
else
{
uint8_t x_43; lean_object* x_44; lean_object* x_45; 
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_8);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl_useReduceAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Meta_refl_useReduceAll(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_refl___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refl");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_refl___lambda__1___closed__2;
x_2 = l_Lean_Meta_refl___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = l_Lean_Expr_getAppFn(x_1);
x_12 = l_Lean_Expr_constLevels_x21(x_11);
x_13 = l_Lean_Expr_appFn_x21(x_2);
x_14 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_15 = l_Lean_Meta_refl___lambda__1___closed__4;
x_16 = l_Lean_mkConst(x_15, x_12);
x_17 = l_Lean_mkAppB(x_16, x_14, x_3);
x_18 = l_Lean_Meta_assignExprMVar(x_4, x_17, x_6, x_7, x_8, x_9, x_10);
return x_18;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("rfl");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_refl___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality lhs");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_refl___lambda__2___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nis not definitionally equal to rhs");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__2___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_refl___lambda__2___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_refl___lambda__2___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (x_6 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_12 = l_Lean_indentExpr(x_3);
x_13 = l_Lean_Meta_refl___lambda__2___closed__4;
x_14 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_refl___lambda__2___closed__6;
x_16 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_indentExpr(x_5);
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_refl___lambda__2___closed__8;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_refl___lambda__2___closed__2;
x_22 = lean_box(0);
x_23 = l_Lean_Meta_throwTacticEx___rarg(x_21, x_4, x_20, x_22, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
return x_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_5);
x_28 = lean_box(0);
x_29 = l_Lean_Meta_refl___lambda__1(x_1, x_2, x_3, x_4, x_28, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_4);
x_10 = l_Lean_Expr_appFn_x21(x_1);
x_11 = l_Lean_Expr_appArg_x21(x_10);
lean_inc(x_6);
x_12 = l_Lean_Meta_instantiateMVars(x_11, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_6);
x_16 = l_Lean_Meta_instantiateMVars(x_15, x_5, x_6, x_7, x_8, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_refl_useReduceAll(x_2, x_13, x_17, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
lean_inc(x_13);
x_23 = l_Lean_Meta_isExprDefEq(x_13, x_17, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unbox(x_24);
lean_dec(x_24);
x_27 = l_Lean_Meta_refl___lambda__2(x_1, x_10, x_13, x_3, x_17, x_26, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_10);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_34 = l_Lean_Meta_reduce(x_13, x_33, x_33, x_33, x_5, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
x_37 = l_Lean_Meta_reduce(x_17, x_33, x_33, x_33, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_expr_eqv(x_35, x_38);
if (x_40 == 0)
{
lean_object* x_41; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_41 = l_Lean_Meta_isExprDefEq(x_35, x_38, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unbox(x_42);
lean_dec(x_42);
x_45 = l_Lean_Meta_refl___lambda__2(x_1, x_10, x_13, x_3, x_17, x_44, x_5, x_6, x_7, x_8, x_43);
lean_dec(x_10);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
return x_41;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; lean_object* x_51; 
lean_dec(x_38);
lean_dec(x_35);
x_50 = 1;
x_51 = l_Lean_Meta_refl___lambda__2(x_1, x_10, x_13, x_3, x_17, x_50, x_5, x_6, x_7, x_8, x_39);
lean_dec(x_10);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_35);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_37);
if (x_52 == 0)
{
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_37, 0);
x_54 = lean_ctor_get(x_37, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_37);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_34);
if (x_56 == 0)
{
return x_34;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_34, 0);
x_58 = lean_ctor_get(x_34, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_34);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality expected{indentExpr targetType}");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_refl___lambda__4___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_refl___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_refl___lambda__4___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_1);
x_9 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_11 = l_Lean_Meta_getMVarType_x27(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_refl___lambda__1___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_12);
x_17 = l_Lean_Meta_refl___lambda__2___closed__2;
x_18 = l_Lean_Meta_refl___lambda__4___closed__3;
x_19 = lean_box(0);
x_20 = l_Lean_Meta_throwTacticEx___rarg(x_17, x_1, x_18, x_19, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Meta_refl___lambda__3(x_12, x_3, x_1, x_25, x_4, x_5, x_6, x_7, x_13);
lean_dec(x_12);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Meta_refl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("apply");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_refl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_refl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_refl___closed__2;
x_9 = lean_box(x_2);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_refl___lambda__4___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_9);
x_11 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_refl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_Meta_refl___lambda__2(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_refl___lambda__3(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_refl___lambda__4(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_refl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_refl(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Reduce(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Reduce(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_refl___lambda__1___closed__1 = _init_l_Lean_Meta_refl___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_refl___lambda__1___closed__1);
l_Lean_Meta_refl___lambda__1___closed__2 = _init_l_Lean_Meta_refl___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_refl___lambda__1___closed__2);
l_Lean_Meta_refl___lambda__1___closed__3 = _init_l_Lean_Meta_refl___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_refl___lambda__1___closed__3);
l_Lean_Meta_refl___lambda__1___closed__4 = _init_l_Lean_Meta_refl___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_refl___lambda__1___closed__4);
l_Lean_Meta_refl___lambda__2___closed__1 = _init_l_Lean_Meta_refl___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_refl___lambda__2___closed__1);
l_Lean_Meta_refl___lambda__2___closed__2 = _init_l_Lean_Meta_refl___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_refl___lambda__2___closed__2);
l_Lean_Meta_refl___lambda__2___closed__3 = _init_l_Lean_Meta_refl___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_refl___lambda__2___closed__3);
l_Lean_Meta_refl___lambda__2___closed__4 = _init_l_Lean_Meta_refl___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_refl___lambda__2___closed__4);
l_Lean_Meta_refl___lambda__2___closed__5 = _init_l_Lean_Meta_refl___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_refl___lambda__2___closed__5);
l_Lean_Meta_refl___lambda__2___closed__6 = _init_l_Lean_Meta_refl___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_refl___lambda__2___closed__6);
l_Lean_Meta_refl___lambda__2___closed__7 = _init_l_Lean_Meta_refl___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_refl___lambda__2___closed__7);
l_Lean_Meta_refl___lambda__2___closed__8 = _init_l_Lean_Meta_refl___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_refl___lambda__2___closed__8);
l_Lean_Meta_refl___lambda__4___closed__1 = _init_l_Lean_Meta_refl___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_refl___lambda__4___closed__1);
l_Lean_Meta_refl___lambda__4___closed__2 = _init_l_Lean_Meta_refl___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_refl___lambda__4___closed__2);
l_Lean_Meta_refl___lambda__4___closed__3 = _init_l_Lean_Meta_refl___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_refl___lambda__4___closed__3);
l_Lean_Meta_refl___closed__1 = _init_l_Lean_Meta_refl___closed__1();
lean_mark_persistent(l_Lean_Meta_refl___closed__1);
l_Lean_Meta_refl___closed__2 = _init_l_Lean_Meta_refl___closed__2();
lean_mark_persistent(l_Lean_Meta_refl___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
