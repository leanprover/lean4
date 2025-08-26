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
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__0;
static lean_object* l_Lean_Meta_mkSorry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f(lean_object*);
lean_object* l_Lean_Expr_name_x3f(lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__4;
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__8;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__4;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__12;
static lean_object* l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__1;
static lean_object* l_Lean_Meta_SorryLabelView_encode___closed__0;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__7;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__0;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___lam__0(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__7;
static lean_object* l_Lean_Meta_mkSorry___closed__2;
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__13;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__2;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__11;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_instToExprName___private__1(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f(lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__5;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__0;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__9;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
static lean_object* l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__0;
static lean_object* l_Lean_Meta_mkSorry___closed__6;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__3;
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__1;
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__1;
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__10;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f___boxed(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__3;
static lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = l_Lean_Environment_contains(x_8, x_1, x_2);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_13);
lean_dec(x_11);
x_14 = l_Lean_Environment_contains(x_13, x_1, x_2);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___redArg(x_1, x_2, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_abortCommandExceptionId;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg(x_6);
return x_7;
}
}
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
x_3 = l_Lean_mkConst(x_2, x_1);
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
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_Lean_Meta_mkSorry___closed__1;
x_15 = 1;
x_16 = l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___redArg(x_14, x_15, x_6, x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec_ref(x_16);
x_20 = l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg(x_19);
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
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
x_27 = lean_ctor_get(x_16, 0);
lean_dec(x_27);
lean_inc_ref(x_1);
x_28 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = lean_box(0);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 1, x_31);
lean_ctor_set(x_16, 0, x_29);
x_32 = l_Lean_mkConst(x_14, x_16);
if (x_2 == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Meta_mkSorry___closed__5;
x_8 = x_30;
x_9 = x_32;
x_10 = x_33;
goto block_13;
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Meta_mkSorry___closed__8;
x_8 = x_30;
x_9 = x_32;
x_10 = x_34;
goto block_13;
}
}
else
{
uint8_t x_35; 
lean_free_object(x_16);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_28);
if (x_35 == 0)
{
return x_28;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_28, 0);
x_37 = lean_ctor_get(x_28, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_28);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_dec(x_16);
lean_inc_ref(x_1);
x_40 = l_Lean_Meta_getLevel(x_1, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_mkConst(x_14, x_44);
if (x_2 == 0)
{
lean_object* x_46; 
x_46 = l_Lean_Meta_mkSorry___closed__5;
x_8 = x_42;
x_9 = x_45;
x_10 = x_46;
goto block_13;
}
else
{
lean_object* x_47; 
x_47 = l_Lean_Meta_mkSorry___closed__8;
x_8 = x_42;
x_9 = x_45;
x_10 = x_47;
goto block_13;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec_ref(x_1);
x_48 = lean_ctor_get(x_40, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_50 = x_40;
} else {
 lean_dec_ref(x_40);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(1, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkAppB(x_9, x_1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___redArg(x_1, x_5, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_mkSorry(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_SorryLabelView_encode___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_sorry", 6, 6);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
x_10 = lean_box(0);
x_5 = x_10;
goto block_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = lean_ctor_get(x_11, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_12, 2);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_12, 3);
lean_inc(x_17);
lean_dec_ref(x_12);
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec_ref(x_13);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec_ref(x_14);
x_22 = l_Lean_Name_num___override(x_15, x_18);
x_23 = l_Lean_Name_num___override(x_22, x_19);
x_24 = l_Lean_Name_num___override(x_23, x_20);
x_25 = l_Lean_Name_num___override(x_24, x_21);
x_26 = l_Lean_Name_num___override(x_25, x_16);
x_27 = l_Lean_Name_num___override(x_26, x_17);
x_5 = x_27;
goto block_9;
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Meta_SorryLabelView_encode___closed__0;
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = l_Lean_Core_mkFreshUserName(x_7, x_2, x_3, x_4);
return x_8;
}
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
lean_inc_ref(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Meta_SorryLabelView_encode___closed__0;
x_8 = lean_string_dec_eq(x_6, x_7);
lean_dec_ref(x_6);
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
lean_dec_ref(x_5);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec_ref(x_10);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec_ref(x_11);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec_ref(x_12);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec_ref(x_13);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec_ref(x_14);
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
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
x_28 = lean_box(0);
return x_28;
}
}
else
{
lean_object* x_29; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
x_29 = lean_box(0);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
x_30 = lean_box(0);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_5);
x_31 = lean_box(0);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_10);
lean_dec_ref(x_5);
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
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_3);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = l_Lean_Environment_header(x_11);
lean_dec_ref(x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___redArg(x_4, x_5);
return x_6;
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
x_3 = l_Lean_mkConst(x_2, x_1);
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
lean_object* x_1; 
x_1 = l_Lean_levelOne;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__8;
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
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__10;
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__7;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__12;
x_2 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__2;
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
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___lam__0(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (x_1 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__1;
x_12 = 0;
x_13 = lean_box(0);
x_14 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__4;
x_15 = l_Lean_mkForall(x_11, x_12, x_14, x_2);
x_16 = l_Lean_Meta_mkSorry(x_15, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__11;
x_20 = l_Lean_mkConst(x_4, x_13);
x_21 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__14;
x_22 = l_Lean_instToExprName___private__1(x_5);
x_23 = l_Lean_mkApp4(x_19, x_14, x_20, x_21, x_22);
x_24 = l_Lean_Expr_app___override(x_18, x_23);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__11;
x_28 = l_Lean_mkConst(x_4, x_13);
x_29 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__14;
x_30 = l_Lean_instToExprName___private__1(x_5);
x_31 = l_Lean_mkApp4(x_27, x_14, x_28, x_29, x_30);
x_32 = l_Lean_Expr_app___override(x_25, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
}
else
{
lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__1;
x_35 = 0;
x_36 = lean_box(0);
x_37 = l_Lean_mkConst(x_4, x_36);
x_38 = l_Lean_mkForall(x_34, x_35, x_37, x_2);
x_39 = l_Lean_Meta_mkSorry(x_38, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = l_Lean_instToExprName___private__1(x_5);
x_43 = l_Lean_Expr_app___override(x_41, x_42);
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_39, 0);
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_39);
x_46 = l_Lean_instToExprName___private__1(x_5);
x_47 = l_Lean_Expr_app___override(x_44, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
else
{
lean_dec(x_5);
return x_39;
}
}
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Name", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___closed__1;
x_2 = l_Lean_Meta_mkLabeledSorry___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_29; 
x_9 = l_Lean_Meta_mkLabeledSorry___closed__2;
x_10 = 1;
x_11 = l_Lean_hasConst___at___Lean_Meta_mkSorry_spec__0___redArg(x_9, x_10, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_29 = lean_unbox(x_12);
lean_dec(x_12);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_30 = l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg(x_13);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
return x_30;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_6, 1);
x_36 = lean_ctor_get(x_6, 5);
x_37 = 0;
x_38 = l_Lean_Syntax_getPos_x3f(x_36, x_37);
if (lean_obj_tag(x_38) == 0)
{
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_13;
goto block_28;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l_Lean_Syntax_getTailPos_x3f(x_36, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_dec(x_39);
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
x_18 = x_13;
goto block_28;
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___redArg(x_7, x_13);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
lean_inc_ref(x_35);
x_46 = l_Lean_FileMap_utf8PosToLspPos(x_35, x_39);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
lean_inc_ref(x_35);
x_48 = l_Lean_FileMap_utf8PosToLspPos(x_35, x_42);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_48, 1);
x_51 = lean_ctor_get(x_48, 0);
lean_dec(x_51);
lean_inc_ref(x_35);
x_52 = l_Lean_FileMap_toPosition(x_35, x_39);
lean_dec(x_39);
lean_inc_ref(x_35);
x_53 = l_Lean_FileMap_toPosition(x_35, x_42);
lean_dec(x_42);
x_54 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_47);
lean_ctor_set(x_54, 2, x_53);
lean_ctor_set(x_54, 3, x_50);
lean_ctor_set(x_48, 1, x_54);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_40, 0, x_48);
lean_inc(x_7);
lean_inc_ref(x_6);
x_55 = l_Lean_Meta_SorryLabelView_encode(x_40, x_6, x_7, x_45);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec_ref(x_55);
x_58 = l_Lean_Meta_mkLabeledSorry___lam__0(x_3, x_1, x_2, x_9, x_56, x_4, x_5, x_6, x_7, x_57);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
return x_55;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_55, 0);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_55);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_dec(x_48);
lean_inc_ref(x_35);
x_64 = l_Lean_FileMap_toPosition(x_35, x_39);
lean_dec(x_39);
lean_inc_ref(x_35);
x_65 = l_Lean_FileMap_toPosition(x_35, x_42);
lean_dec(x_42);
x_66 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_47);
lean_ctor_set(x_66, 2, x_65);
lean_ctor_set(x_66, 3, x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_44);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_40, 0, x_67);
lean_inc(x_7);
lean_inc_ref(x_6);
x_68 = l_Lean_Meta_SorryLabelView_encode(x_40, x_6, x_7, x_45);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_71 = l_Lean_Meta_mkLabeledSorry___lam__0(x_3, x_1, x_2, x_9, x_69, x_4, x_5, x_6, x_7, x_70);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_74 = x_68;
} else {
 lean_dec_ref(x_68);
 x_74 = lean_box(0);
}
if (lean_is_scalar(x_74)) {
 x_75 = lean_alloc_ctor(1, 2, 0);
} else {
 x_75 = x_74;
}
lean_ctor_set(x_75, 0, x_72);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_76 = lean_ctor_get(x_40, 0);
lean_inc(x_76);
lean_dec(x_40);
x_77 = l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___redArg(x_7, x_13);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec_ref(x_77);
lean_inc_ref(x_35);
x_80 = l_Lean_FileMap_utf8PosToLspPos(x_35, x_39);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec_ref(x_80);
lean_inc_ref(x_35);
x_82 = l_Lean_FileMap_utf8PosToLspPos(x_35, x_76);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
lean_inc_ref(x_35);
x_85 = l_Lean_FileMap_toPosition(x_35, x_39);
lean_dec(x_39);
lean_inc_ref(x_35);
x_86 = l_Lean_FileMap_toPosition(x_35, x_76);
lean_dec(x_76);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_81);
lean_ctor_set(x_87, 2, x_86);
lean_ctor_set(x_87, 3, x_83);
if (lean_is_scalar(x_84)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_84;
}
lean_ctor_set(x_88, 0, x_78);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_inc(x_7);
lean_inc_ref(x_6);
x_90 = l_Lean_Meta_SorryLabelView_encode(x_89, x_6, x_7, x_79);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec_ref(x_90);
x_93 = l_Lean_Meta_mkLabeledSorry___lam__0(x_3, x_1, x_2, x_9, x_91, x_4, x_5, x_6, x_7, x_92);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_90, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_90, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_96 = x_90;
} else {
 lean_dec_ref(x_90);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
}
}
block_28:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
lean_inc(x_17);
lean_inc_ref(x_16);
x_20 = l_Lean_Meta_SorryLabelView_encode(x_19, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Lean_Meta_mkLabeledSorry___lam__0(x_3, x_1, x_2, x_9, x_21, x_14, x_15, x_16, x_17, x_22);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 0);
x_26 = lean_ctor_get(x_20, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getMainModule___at___Lean_Meta_mkLabeledSorry_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_Meta_mkLabeledSorry___lam__0(x_11, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
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
lean_inc_ref(x_13);
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
lean_dec_ref(x_13);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = l_Lean_Expr_appFn_x21(x_13);
x_20 = l_Lean_Expr_appArg_x21(x_19);
lean_dec_ref(x_19);
x_21 = l_Lean_Meta_mkLabeledSorry___lam__0___closed__13;
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_isAppOfArity(x_20, x_21, x_22);
lean_dec_ref(x_20);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_13);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = l_Lean_Expr_appArg_x21(x_13);
lean_dec_ref(x_13);
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
lean_dec_ref(x_26);
x_29 = l_Lean_Meta_SorryLabelView_decode_x3f(x_28);
return x_29;
}
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_13);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec_ref(x_14);
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
lean_dec_ref(x_1);
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
l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__0 = _init_l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__0);
l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__1 = _init_l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_Elab_throwAbortCommand___at___Lean_Meta_mkSorry_spec__1___redArg___closed__1);
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
l_Lean_Meta_SorryLabelView_encode___closed__0 = _init_l_Lean_Meta_SorryLabelView_encode___closed__0();
lean_mark_persistent(l_Lean_Meta_SorryLabelView_encode___closed__0);
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
l_Lean_Meta_mkLabeledSorry___closed__0 = _init_l_Lean_Meta_mkLabeledSorry___closed__0();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__0);
l_Lean_Meta_mkLabeledSorry___closed__1 = _init_l_Lean_Meta_mkLabeledSorry___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__1);
l_Lean_Meta_mkLabeledSorry___closed__2 = _init_l_Lean_Meta_mkLabeledSorry___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
