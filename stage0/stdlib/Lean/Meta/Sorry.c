// Lean compiler output
// Module: Lean.Meta.Sorry
// Imports: Lean.Data.Lsp.Utf16 Lean.Meta.InferType Lean.Util.Recognizers
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__0;
static lean_object* l_Lean_Meta_mkSorry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f(lean_object*);
lean_object* l_Lean_Expr_name_x3f(lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__4;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__8;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__4;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__12;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__7;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__17;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__15;
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__7;
static lean_object* l_Lean_Meta_mkSorry___closed__2;
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__13;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__11;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f(lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__0;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__9;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__6;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__6;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__3;
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__16;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__10;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f___boxed(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__3;
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__2;
static lean_object* l_Lean_Meta_SorryLabelView_encode___redArg___closed__0;
static lean_object* _init_l_Lean_Meta_mkSorry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sorryAx", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkSorry___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSorry___closed__3;
x_2 = l_Lean_Meta_mkSorry___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__4;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkSorry___closed__6;
x_2 = l_Lean_Meta_mkSorry___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkSorry___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkSorry___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_12 = l_Lean_Meta_mkSorry___closed__1;
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_Expr_const___override(x_12, x_14);
if (x_2 == 0)
{
lean_object* x_20; 
x_20 = l_Lean_Meta_mkSorry___closed__5;
x_16 = x_20;
goto block_19;
}
else
{
lean_object* x_21; 
x_21 = l_Lean_Meta_mkSorry___closed__8;
x_16 = x_21;
goto block_19;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_mkAppB(x_15, x_1, x_16);
if (lean_is_scalar(x_11)) {
 x_18 = lean_alloc_ctor(0, 2, 0);
} else {
 x_18 = x_11;
}
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
}
else
{
uint8_t x_22; 
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_mkSorry(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_SorryLabelView_encode___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_sorry", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
x_4 = x_9;
goto block_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 3);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec(x_13);
x_21 = l_Lean_Name_num___override(x_14, x_17);
x_22 = l_Lean_Name_num___override(x_21, x_18);
x_23 = l_Lean_Name_num___override(x_22, x_19);
x_24 = l_Lean_Name_num___override(x_23, x_20);
x_25 = l_Lean_Name_num___override(x_24, x_15);
x_26 = l_Lean_Name_num___override(x_25, x_16);
x_4 = x_26;
goto block_8;
}
block_8:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Lean_Meta_SorryLabelView_encode___redArg___closed__0;
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp___redArg(x_6, x_2, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SorryLabelView_encode___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SorryLabelView_encode___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SorryLabelView_encode(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Name_hasMacroScopes(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
lean_dec(x_1);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_erase_macro_scopes(x_1);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Meta_SorryLabelView_encode___redArg___closed__0;
x_8 = lean_string_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
if (lean_obj_tag(x_5) == 2)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 2)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 2)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_18);
lean_ctor_set(x_23, 1, x_17);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_16);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_15);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_28 = lean_box(0);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_29 = lean_box(0);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_30 = lean_box(0);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_5);
x_31 = lean_box(0);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_10);
lean_dec(x_5);
x_32 = lean_box(0);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_5);
x_33 = lean_box(0);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_4);
x_34 = lean_box(0);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tag", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__3;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Function", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("const", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__6;
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__8;
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__9;
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__7;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__12;
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__13;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__15;
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__2;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__16;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___lam__0(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (x_1 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__1;
x_11 = lean_box(0);
x_12 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__4;
x_13 = lean_unbox(x_11);
x_14 = l_Lean_Expr_forallE___override(x_10, x_12, x_2, x_13);
x_15 = l_Lean_Meta_mkSorry(x_14, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__10;
x_19 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__14;
x_20 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__17;
x_21 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_4);
x_22 = l_Lean_mkApp4(x_18, x_12, x_19, x_20, x_21);
x_23 = l_Lean_Expr_app___override(x_17, x_22);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__10;
x_27 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__14;
x_28 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__17;
x_29 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_4);
x_30 = l_Lean_mkApp4(x_26, x_12, x_27, x_28, x_29);
x_31 = l_Lean_Expr_app___override(x_24, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
else
{
lean_dec(x_4);
return x_15;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_33 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__1;
x_34 = lean_box(0);
x_35 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__14;
x_36 = lean_unbox(x_34);
x_37 = l_Lean_Expr_forallE___override(x_33, x_35, x_2, x_36);
x_38 = l_Lean_Meta_mkSorry(x_37, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_4);
x_42 = l_Lean_Expr_app___override(x_40, x_41);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_4);
x_46 = l_Lean_Expr_app___override(x_43, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
else
{
lean_dec(x_4);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_6, 5);
lean_inc(x_10);
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
x_24 = l_Lean_Syntax_getPos_x3f(x_10, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_10);
lean_dec(x_9);
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_21;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_unbox(x_22);
x_27 = l_Lean_Syntax_getTailPos_x3f(x_10, x_26);
lean_dec(x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_dec(x_25);
lean_dec(x_9);
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_7;
x_15 = x_8;
goto block_21;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_st_ref_get(x_7, x_8);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_9);
x_34 = l_Lean_FileMap_utf8PosToLspPos(x_9, x_25);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
lean_inc(x_9);
x_36 = l_Lean_FileMap_utf8PosToLspPos(x_9, x_29);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_38 = lean_ctor_get(x_36, 1);
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = l_Lean_Environment_mainModule(x_33);
lean_dec(x_33);
lean_inc(x_9);
x_41 = l_Lean_FileMap_toPosition(x_9, x_25);
lean_dec(x_25);
x_42 = l_Lean_FileMap_toPosition(x_9, x_29);
lean_dec(x_29);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_35);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_36, 1, x_43);
lean_ctor_set(x_36, 0, x_40);
lean_ctor_set(x_27, 0, x_36);
x_44 = l_Lean_Meta_SorryLabelView_encode___redArg(x_27, x_7, x_32);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_mkLabeledSorry___lam__0(x_3, x_1, x_2, x_45, x_4, x_5, x_6, x_7, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_dec(x_36);
x_49 = l_Lean_Environment_mainModule(x_33);
lean_dec(x_33);
lean_inc(x_9);
x_50 = l_Lean_FileMap_toPosition(x_9, x_25);
lean_dec(x_25);
x_51 = l_Lean_FileMap_toPosition(x_9, x_29);
lean_dec(x_29);
x_52 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_35);
lean_ctor_set(x_52, 2, x_51);
lean_ctor_set(x_52, 3, x_48);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_27, 0, x_53);
x_54 = l_Lean_Meta_SorryLabelView_encode___redArg(x_27, x_7, x_32);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = l_Lean_Meta_mkLabeledSorry___lam__0(x_3, x_1, x_2, x_55, x_4, x_5, x_6, x_7, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_58 = lean_ctor_get(x_27, 0);
lean_inc(x_58);
lean_dec(x_27);
x_59 = lean_st_ref_get(x_7, x_8);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_9);
x_63 = l_Lean_FileMap_utf8PosToLspPos(x_9, x_25);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
lean_inc(x_9);
x_65 = l_Lean_FileMap_utf8PosToLspPos(x_9, x_58);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
x_68 = l_Lean_Environment_mainModule(x_62);
lean_dec(x_62);
lean_inc(x_9);
x_69 = l_Lean_FileMap_toPosition(x_9, x_25);
lean_dec(x_25);
x_70 = l_Lean_FileMap_toPosition(x_9, x_58);
lean_dec(x_58);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_64);
lean_ctor_set(x_71, 2, x_70);
lean_ctor_set(x_71, 3, x_66);
if (lean_is_scalar(x_67)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_67;
}
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = l_Lean_Meta_SorryLabelView_encode___redArg(x_73, x_7, x_61);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Meta_mkLabeledSorry___lam__0(x_3, x_1, x_2, x_75, x_4, x_5, x_6, x_7, x_76);
return x_77;
}
}
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_box(0);
x_17 = l_Lean_Meta_SorryLabelView_encode___redArg(x_16, x_14, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_mkLabeledSorry___lam__0(x_3, x_1, x_2, x_18, x_11, x_12, x_13, x_14, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_mkLabeledSorry___lam__0(x_10, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_mkLabeledSorry(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Meta_mkSorry___closed__1;
x_3 = l_Lean_Expr_isAppOf(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_Expr_getAppNumArgs(x_1);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_dec_le(x_6, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_sub(x_5, x_9);
lean_dec(x_5);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = l_Lean_Expr_getRevArg_x21(x_1, x_12);
lean_inc(x_13);
x_14 = l_Lean_Expr_name_x3f(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__7;
x_16 = lean_unsigned_to_nat(4u);
x_17 = l_Lean_Expr_isAppOfArity(x_13, x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = l_Lean_Expr_appFn_x21(x_13);
x_20 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_21 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__16;
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_isAppOfArity(x_20, x_21, x_22);
lean_dec(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_13);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Expr_appArg_x21(x_13);
lean_dec(x_13);
x_26 = l_Lean_Expr_name_x3f(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_box(0);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l_Lean_Meta_SorryLabelView_decode_x3f(x_28);
return x_29;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_13);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = l_Lean_Meta_SorryLabelView_decode_x3f(x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_isLabeledSorry_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sorry(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Utf16(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_mkSorry___closed__0 = _init_l_Lean_Meta_mkSorry___closed__0();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__0);
l_Lean_Meta_mkSorry___closed__1 = _init_l_Lean_Meta_mkSorry___closed__1();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__1);
l_Lean_Meta_mkSorry___closed__2 = _init_l_Lean_Meta_mkSorry___closed__2();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__2);
l_Lean_Meta_mkSorry___closed__3 = _init_l_Lean_Meta_mkSorry___closed__3();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__3);
l_Lean_Meta_mkSorry___closed__4 = _init_l_Lean_Meta_mkSorry___closed__4();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__4);
l_Lean_Meta_mkSorry___closed__5 = _init_l_Lean_Meta_mkSorry___closed__5();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__5);
l_Lean_Meta_mkSorry___closed__6 = _init_l_Lean_Meta_mkSorry___closed__6();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__6);
l_Lean_Meta_mkSorry___closed__7 = _init_l_Lean_Meta_mkSorry___closed__7();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__7);
l_Lean_Meta_mkSorry___closed__8 = _init_l_Lean_Meta_mkSorry___closed__8();
lean_mark_persistent(l_Lean_Meta_mkSorry___closed__8);
l_Lean_Meta_SorryLabelView_encode___redArg___closed__0 = _init_l_Lean_Meta_SorryLabelView_encode___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_SorryLabelView_encode___redArg___closed__0);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__0 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__0);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__1 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__1);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__2 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__2);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__3 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__3);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__4 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__4);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__5 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__5);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__6 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__6);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__7 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__7();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__7);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__8 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__8();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__8);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__9 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__9();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__9);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__10 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__10();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__10);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__11 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__11();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__11);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__12 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__12();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__12);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__13 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__13();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__13);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__14 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__14();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__14);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__15 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__15();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__15);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__16 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__16();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__16);
l_Lean_Meta_mkLabeledSorry___lam__0___closed__17 = _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__17();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___lam__0___closed__17);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
