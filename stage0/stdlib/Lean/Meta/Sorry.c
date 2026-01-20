// Lean compiler output
// Module: Lean.Meta.Sorry
// Imports: public import Lean.Data.Lsp.Utf16 public import Lean.Meta.ForEachExpr public import Lean.Meta.InferType public import Lean.Util.Recognizers
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_decode_x3f(lean_object*);
lean_object* l_Lean_Expr_name_x3f(lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__4;
lean_object* l_Lean_Environment_header(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__8;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__8;
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__7;
static lean_object* l_Lean_Meta_SorryLabelView_encode___closed__0;
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___boxed(lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Meta_mkSorry___closed__7;
lean_object* l_Lean_Meta_forEachExpr_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getBoundedAppFn(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__0;
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__3;
extern lean_object* l_Lean_Elab_abortCommandExceptionId;
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Declaration_foldExprM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__2;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__2;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f___boxed(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__5;
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__17;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_instToExprName___private__1(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f(lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__5;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__16;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkSorry___closed__0;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__14;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__12;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
static lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__10;
static lean_object* l_Lean_Meta_mkSorry___closed__6;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__11;
static lean_object* l_Lean_Meta_mkSorry___closed__3;
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__9;
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__6;
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__1;
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_mkLabeledSorry___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isSorry(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLabeledSorry_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Environment_contains(x_6, x_1, x_2);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(x_1, x_5, x_3);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(x_1, x_2, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0(x_1, x_8, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
static lean_object* _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_abortCommandExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0;
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_14 = l_Lean_Meta_mkSorry___closed__1;
x_31 = 1;
x_32 = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(x_14, x_31, x_6);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_35 = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
else
{
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = lean_box(0);
goto block_30;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkAppB(x_9, x_1, x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
block_30:
{
lean_object* x_20; 
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_getLevel(x_1, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_mkConst(x_14, x_23);
if (x_2 == 0)
{
lean_object* x_25; 
x_25 = l_Lean_Meta_mkSorry___closed__5;
x_8 = lean_box(0);
x_9 = x_24;
x_10 = x_25;
goto block_13;
}
else
{
lean_object* x_26; 
x_26 = l_Lean_Meta_mkSorry___closed__8;
x_8 = lean_box(0);
x_9 = x_24;
x_10 = x_26;
goto block_13;
}
}
else
{
uint8_t x_27; 
lean_dec_ref(x_1);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
x_9 = l_Lean_Meta_mkSorry(x_1, x_8, x_3, x_4, x_5, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_11, 2);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 3);
lean_inc(x_16);
lean_dec_ref(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec_ref(x_12);
x_19 = lean_ctor_get(x_13, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_dec_ref(x_13);
x_21 = l_Lean_Name_num___override(x_14, x_17);
x_22 = l_Lean_Name_num___override(x_21, x_18);
x_23 = l_Lean_Name_num___override(x_22, x_19);
x_24 = l_Lean_Name_num___override(x_23, x_20);
x_25 = l_Lean_Name_num___override(x_24, x_15);
x_26 = l_Lean_Name_num___override(x_25, x_16);
x_5 = x_26;
goto block_9;
}
else
{
lean_object* x_27; 
lean_dec(x_1);
x_27 = lean_box(0);
x_5 = x_27;
goto block_9;
}
block_9:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = l_Lean_Meta_SorryLabelView_encode___closed__0;
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = l_Lean_Core_mkFreshUserName(x_7, x_2, x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SorryLabelView_encode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SorryLabelView_encode(x_1, x_2, x_3);
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
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_st_ref_get(x_1);
x_4 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_4);
lean_dec(x_3);
x_5 = l_Lean_Environment_header(x_4);
lean_dec_ref(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(x_1);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
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
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("tag", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkLabeledSorry___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_mkLabeledSorry___closed__5;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLabeledSorry___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Function", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("const", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___closed__9;
x_2 = l_Lean_Meta_mkLabeledSorry___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__11() {
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
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___closed__11;
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___closed__12;
x_2 = l_Lean_Meta_mkLabeledSorry___closed__10;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLabeledSorry___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unit", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_mkLabeledSorry___closed__15;
x_2 = l_Lean_Meta_mkLabeledSorry___closed__5;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_mkLabeledSorry___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkLabeledSorry___closed__16;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_9 = l_Lean_Meta_mkLabeledSorry___closed__2;
x_119 = 1;
x_120 = l_Lean_hasConst___at___00Lean_Meta_mkSorry_spec__0___redArg(x_9, x_119, x_7);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; uint8_t x_124; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_123 = l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg();
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
return x_123;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
lean_dec(x_123);
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_125);
return x_126;
}
}
else
{
x_63 = x_4;
x_64 = x_5;
x_65 = x_6;
x_66 = x_7;
x_67 = lean_box(0);
goto block_118;
}
block_50:
{
if (x_3 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Meta_mkLabeledSorry___closed__4;
x_17 = 0;
x_18 = l_Lean_Meta_mkLabeledSorry___closed__7;
x_19 = l_Lean_mkForall(x_16, x_17, x_18, x_1);
x_20 = l_Lean_Meta_mkSorry(x_19, x_2, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = l_Lean_Meta_mkLabeledSorry___closed__13;
x_24 = l_Lean_Meta_mkLabeledSorry___closed__14;
x_25 = l_Lean_Meta_mkLabeledSorry___closed__17;
x_26 = l_Lean_instToExprName___private__1(x_10);
x_27 = l_Lean_mkApp4(x_23, x_18, x_24, x_25, x_26);
x_28 = l_Lean_Expr_app___override(x_22, x_27);
lean_ctor_set(x_20, 0, x_28);
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
x_30 = l_Lean_Meta_mkLabeledSorry___closed__13;
x_31 = l_Lean_Meta_mkLabeledSorry___closed__14;
x_32 = l_Lean_Meta_mkLabeledSorry___closed__17;
x_33 = l_Lean_instToExprName___private__1(x_10);
x_34 = l_Lean_mkApp4(x_30, x_18, x_31, x_32, x_33);
x_35 = l_Lean_Expr_app___override(x_29, x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
else
{
lean_dec(x_10);
return x_20;
}
}
else
{
lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = l_Lean_Meta_mkLabeledSorry___closed__4;
x_38 = 0;
x_39 = l_Lean_Meta_mkLabeledSorry___closed__14;
x_40 = l_Lean_mkForall(x_37, x_38, x_39, x_1);
x_41 = l_Lean_Meta_mkSorry(x_40, x_2, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = l_Lean_instToExprName___private__1(x_10);
x_45 = l_Lean_Expr_app___override(x_43, x_44);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_instToExprName___private__1(x_10);
x_48 = l_Lean_Expr_app___override(x_46, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_dec(x_10);
return x_41;
}
}
}
block_62:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
lean_inc(x_54);
lean_inc_ref(x_53);
x_57 = l_Lean_Meta_SorryLabelView_encode(x_56, x_53, x_54);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
x_10 = x_58;
x_11 = x_51;
x_12 = x_52;
x_13 = x_53;
x_14 = x_54;
x_15 = lean_box(0);
goto block_50;
}
else
{
uint8_t x_59; 
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
return x_57;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
block_118:
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_68 = lean_ctor_get(x_65, 1);
x_69 = lean_ctor_get(x_65, 5);
x_70 = 0;
x_71 = l_Lean_Syntax_getPos_x3f(x_69, x_70);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = l_Lean_Syntax_getTailPos_x3f(x_69, x_70);
if (lean_obj_tag(x_73) == 1)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(x_66);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
lean_inc_ref(x_68);
x_78 = l_Lean_FileMap_toPosition(x_68, x_72);
lean_inc_ref(x_68);
x_79 = l_Lean_FileMap_utf8PosToLspPos(x_68, x_72);
lean_dec(x_72);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec_ref(x_79);
lean_inc_ref(x_68);
x_81 = l_Lean_FileMap_toPosition(x_68, x_75);
lean_inc_ref(x_68);
x_82 = l_Lean_FileMap_utf8PosToLspPos(x_68, x_75);
lean_dec(x_75);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_82, 1);
x_85 = lean_ctor_get(x_82, 0);
lean_dec(x_85);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_84);
lean_ctor_set(x_82, 1, x_86);
lean_ctor_set(x_82, 0, x_77);
lean_ctor_set(x_73, 0, x_82);
lean_inc(x_66);
lean_inc_ref(x_65);
x_87 = l_Lean_Meta_SorryLabelView_encode(x_73, x_65, x_66);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_10 = x_88;
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = lean_box(0);
goto block_50;
}
else
{
uint8_t x_89; 
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_87);
if (x_89 == 0)
{
return x_87;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_82, 1);
lean_inc(x_92);
lean_dec(x_82);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_78);
lean_ctor_set(x_93, 1, x_80);
lean_ctor_set(x_93, 2, x_81);
lean_ctor_set(x_93, 3, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_77);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_73, 0, x_94);
lean_inc(x_66);
lean_inc_ref(x_65);
x_95 = l_Lean_Meta_SorryLabelView_encode(x_73, x_65, x_66);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_10 = x_96;
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = lean_box(0);
goto block_50;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_1);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 1, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_100 = lean_ctor_get(x_73, 0);
lean_inc(x_100);
lean_dec(x_73);
x_101 = l_Lean_getMainModule___at___00Lean_Meta_mkLabeledSorry_spec__0___redArg(x_66);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec_ref(x_101);
lean_inc_ref(x_68);
x_103 = l_Lean_FileMap_toPosition(x_68, x_72);
lean_inc_ref(x_68);
x_104 = l_Lean_FileMap_utf8PosToLspPos(x_68, x_72);
lean_dec(x_72);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec_ref(x_104);
lean_inc_ref(x_68);
x_106 = l_Lean_FileMap_toPosition(x_68, x_100);
lean_inc_ref(x_68);
x_107 = l_Lean_FileMap_utf8PosToLspPos(x_68, x_100);
lean_dec(x_100);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_110, 0, x_103);
lean_ctor_set(x_110, 1, x_105);
lean_ctor_set(x_110, 2, x_106);
lean_ctor_set(x_110, 3, x_108);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_102);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
lean_inc(x_66);
lean_inc_ref(x_65);
x_113 = l_Lean_Meta_SorryLabelView_encode(x_112, x_65, x_66);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_10 = x_114;
x_11 = x_63;
x_12 = x_64;
x_13 = x_65;
x_14 = x_66;
x_15 = lean_box(0);
goto block_50;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec_ref(x_1);
x_115 = lean_ctor_get(x_113, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_115);
return x_117;
}
}
}
else
{
lean_dec(x_73);
lean_dec(x_72);
x_51 = x_63;
x_52 = x_64;
x_53 = x_65;
x_54 = x_66;
x_55 = lean_box(0);
goto block_62;
}
}
else
{
lean_dec(x_71);
x_51 = x_63;
x_52 = x_64;
x_53 = x_65;
x_54 = x_66;
x_55 = lean_box(0);
goto block_62;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLabeledSorry___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Meta_mkLabeledSorry(x_1, x_9, x_10, x_4, x_5, x_6, x_7);
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
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_SorryLabelView_decode_x3f(x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_14);
x_17 = l_Lean_Meta_mkLabeledSorry___closed__10;
x_18 = lean_unsigned_to_nat(4u);
x_19 = l_Lean_Expr_isAppOfArity(x_13, x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_13);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = l_Lean_Expr_appFn_x21(x_13);
x_22 = l_Lean_Expr_appArg_x21(x_21);
lean_dec_ref(x_21);
x_23 = l_Lean_Meta_mkLabeledSorry___closed__16;
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_isAppOfArity(x_22, x_23, x_24);
lean_dec_ref(x_22);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_13);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Expr_appArg_x21(x_13);
lean_dec_ref(x_13);
x_28 = l_Lean_Expr_name_x3f(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_box(0);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l_Lean_Meta_SorryLabelView_decode_x3f(x_30);
return x_31;
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f(lean_object* x_1) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isSorry(x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lean_Meta_isLabeledSorry_x3f(x_1);
if (lean_obj_tag(x_10) == 0)
{
goto block_7;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
if (x_8 == 0)
{
lean_free_object(x_10);
goto block_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_sub(x_13, x_14);
lean_dec(x_13);
x_16 = l_Lean_Expr_getBoundedAppFn(x_15, x_1);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
}
else
{
lean_dec(x_10);
if (x_8 == 0)
{
goto block_7;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = l_Lean_Expr_getAppNumArgs(x_1);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_sub(x_17, x_18);
lean_dec(x_17);
x_20 = l_Lean_Expr_getBoundedAppFn(x_19, x_1);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
block_7:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_Expr_getAppNumArgs(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_Expr_getBoundedAppFn(x_4, x_1);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_getSorry_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_getSorry_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 0;
x_4 = lean_box(x_3);
x_5 = lean_apply_2(x_1, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Expr_getSorry_x3f(x_5);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec_ref(x_6);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_apply_4(x_2, lean_box(0), lean_box(0), x_8, x_3);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = 1;
x_11 = lean_box(x_10);
x_12 = lean_apply_2(x_4, lean_box(0), x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_forEachSorryM___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_8);
lean_inc(x_8);
lean_inc(x_7);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_7);
lean_closure_set(x_10, 2, x_9);
lean_closure_set(x_10, 3, x_8);
x_11 = l_Lean_Meta_forEachExpr_x27___redArg(x_1, x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_forEachSorryM___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_forEachSorryM___redArg(x_1, x_2, x_3, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc_ref(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Declaration_forEachSorryM___redArg___lam__0), 6, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Declaration_foldExprM___redArg(x_1, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Declaration_forEachSorryM___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Lean_Data_Lsp_Utf16(uint8_t builtin);
lean_object* initialize_Lean_Meta_ForEachExpr(uint8_t builtin);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sorry(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Lsp_Utf16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ForEachExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0 = _init_l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_Elab_throwAbortCommand___at___00Lean_Meta_mkSorry_spec__1___redArg___closed__0);
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
l_Lean_Meta_mkLabeledSorry___closed__0 = _init_l_Lean_Meta_mkLabeledSorry___closed__0();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__0);
l_Lean_Meta_mkLabeledSorry___closed__1 = _init_l_Lean_Meta_mkLabeledSorry___closed__1();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__1);
l_Lean_Meta_mkLabeledSorry___closed__2 = _init_l_Lean_Meta_mkLabeledSorry___closed__2();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__2);
l_Lean_Meta_mkLabeledSorry___closed__3 = _init_l_Lean_Meta_mkLabeledSorry___closed__3();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__3);
l_Lean_Meta_mkLabeledSorry___closed__4 = _init_l_Lean_Meta_mkLabeledSorry___closed__4();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__4);
l_Lean_Meta_mkLabeledSorry___closed__5 = _init_l_Lean_Meta_mkLabeledSorry___closed__5();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__5);
l_Lean_Meta_mkLabeledSorry___closed__6 = _init_l_Lean_Meta_mkLabeledSorry___closed__6();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__6);
l_Lean_Meta_mkLabeledSorry___closed__7 = _init_l_Lean_Meta_mkLabeledSorry___closed__7();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__7);
l_Lean_Meta_mkLabeledSorry___closed__8 = _init_l_Lean_Meta_mkLabeledSorry___closed__8();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__8);
l_Lean_Meta_mkLabeledSorry___closed__9 = _init_l_Lean_Meta_mkLabeledSorry___closed__9();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__9);
l_Lean_Meta_mkLabeledSorry___closed__10 = _init_l_Lean_Meta_mkLabeledSorry___closed__10();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__10);
l_Lean_Meta_mkLabeledSorry___closed__11 = _init_l_Lean_Meta_mkLabeledSorry___closed__11();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__11);
l_Lean_Meta_mkLabeledSorry___closed__12 = _init_l_Lean_Meta_mkLabeledSorry___closed__12();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__12);
l_Lean_Meta_mkLabeledSorry___closed__13 = _init_l_Lean_Meta_mkLabeledSorry___closed__13();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__13);
l_Lean_Meta_mkLabeledSorry___closed__14 = _init_l_Lean_Meta_mkLabeledSorry___closed__14();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__14);
l_Lean_Meta_mkLabeledSorry___closed__15 = _init_l_Lean_Meta_mkLabeledSorry___closed__15();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__15);
l_Lean_Meta_mkLabeledSorry___closed__16 = _init_l_Lean_Meta_mkLabeledSorry___closed__16();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__16);
l_Lean_Meta_mkLabeledSorry___closed__17 = _init_l_Lean_Meta_mkLabeledSorry___closed__17();
lean_mark_persistent(l_Lean_Meta_mkLabeledSorry___closed__17);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
