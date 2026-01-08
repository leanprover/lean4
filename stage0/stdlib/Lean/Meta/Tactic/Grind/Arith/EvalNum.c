// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.EvalNum
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.IntInstTesters import Lean.Meta.NatInstTesters
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9;
uint8_t l_Lean_Expr_isApp(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1;
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4;
lean_object* l_Lean_Meta_Structural_isInstHPowInt___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14;
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__3;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstNegInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__4;
lean_object* l_Lean_Meta_Structural_isInstHDivInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulNat___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__1;
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Int_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0;
lean_object* l_Lean_Meta_Structural_isInstHSubNat___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13;
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHPowNat___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4;
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHSubInt___redArg(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHAddInt___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHMulInt___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7;
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_checkExp___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0;
lean_object* lean_int_ediv(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstHModInt___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2;
lean_object* l_Lean_Meta_Structural_isInstHModNat___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20;
lean_object* l_Lean_Meta_Structural_isInstHDivNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exponent ", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_checkExp___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" exceeds threshold for exponentiation `(exp := ", 47, 47);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_checkExp___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(")`", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_checkExp___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 7);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_nat_dec_lt(x_21, x_1);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = l_Lean_Meta_Grind_Arith_checkExp___closed__0;
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
lean_object* x_24; 
lean_free_object(x_17);
x_24 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*10 + 13);
lean_dec(x_30);
if (x_31 == 0)
{
lean_free_object(x_28);
lean_free_object(x_26);
lean_dec(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 7);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Meta_Grind_Arith_checkExp___closed__2;
x_36 = l_Nat_reprFast(x_1);
lean_ctor_set_tag(x_28, 3);
lean_ctor_set(x_28, 0, x_36);
x_37 = l_Lean_MessageData_ofFormat(x_28);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_Meta_Grind_Arith_checkExp___closed__4;
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Nat_reprFast(x_34);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 0, x_41);
x_42 = l_Lean_MessageData_ofFormat(x_26);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_Grind_Arith_checkExp___closed__6;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_Grind_reportIssue(x_45, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
x_11 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_free_object(x_28);
lean_free_object(x_26);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_32, 0);
lean_inc(x_51);
lean_dec(x_32);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_28, 0);
lean_inc(x_53);
lean_dec(x_28);
x_54 = lean_ctor_get_uint8(x_53, sizeof(void*)*10 + 13);
lean_dec(x_53);
if (x_54 == 0)
{
lean_free_object(x_26);
lean_dec(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_55; 
x_55 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_56, 7);
lean_inc(x_57);
lean_dec(x_56);
x_58 = l_Lean_Meta_Grind_Arith_checkExp___closed__2;
x_59 = l_Nat_reprFast(x_1);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_MessageData_ofFormat(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_Grind_Arith_checkExp___closed__4;
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Nat_reprFast(x_57);
lean_ctor_set_tag(x_26, 3);
lean_ctor_set(x_26, 0, x_65);
x_66 = l_Lean_MessageData_ofFormat(x_26);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_Grind_Arith_checkExp___closed__6;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_Grind_reportIssue(x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_70) == 0)
{
lean_dec_ref(x_70);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_free_object(x_26);
lean_dec(x_1);
x_74 = lean_ctor_get(x_55, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_75 = x_55;
} else {
 lean_dec_ref(x_55);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_26, 0);
lean_inc(x_77);
lean_dec(x_26);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get_uint8(x_78, sizeof(void*)*10 + 13);
lean_dec(x_78);
if (x_80 == 0)
{
lean_dec(x_79);
lean_dec(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_81; 
x_81 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_ctor_get(x_82, 7);
lean_inc(x_83);
lean_dec(x_82);
x_84 = l_Lean_Meta_Grind_Arith_checkExp___closed__2;
x_85 = l_Nat_reprFast(x_1);
if (lean_is_scalar(x_79)) {
 x_86 = lean_alloc_ctor(3, 1, 0);
} else {
 x_86 = x_79;
 lean_ctor_set_tag(x_86, 3);
}
lean_ctor_set(x_86, 0, x_85);
x_87 = l_Lean_MessageData_ofFormat(x_86);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Meta_Grind_Arith_checkExp___closed__4;
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Nat_reprFast(x_83);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_MessageData_ofFormat(x_92);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Meta_Grind_Arith_checkExp___closed__6;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_Meta_Grind_reportIssue(x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_97) == 0)
{
lean_dec_ref(x_97);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_79);
lean_dec(x_1);
x_101 = lean_ctor_get(x_81, 0);
lean_inc(x_101);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_102 = x_81;
} else {
 lean_dec_ref(x_81);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 1, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_101);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_24);
if (x_104 == 0)
{
return x_24;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_24, 0);
lean_inc(x_105);
lean_dec(x_24);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_17, 0);
lean_inc(x_107);
lean_dec(x_17);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get(x_108, 7);
lean_inc(x_109);
lean_dec(x_108);
x_110 = lean_nat_dec_lt(x_109, x_1);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_1);
x_111 = l_Lean_Meta_Grind_Arith_checkExp___closed__0;
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
lean_object* x_113; 
x_113 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_114, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = lean_ctor_get_uint8(x_118, sizeof(void*)*10 + 13);
lean_dec(x_118);
if (x_120 == 0)
{
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_121; 
x_121 = l_Lean_Meta_Grind_getConfig___redArg(x_3);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = lean_ctor_get(x_122, 7);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l_Lean_Meta_Grind_Arith_checkExp___closed__2;
x_125 = l_Nat_reprFast(x_1);
if (lean_is_scalar(x_119)) {
 x_126 = lean_alloc_ctor(3, 1, 0);
} else {
 x_126 = x_119;
 lean_ctor_set_tag(x_126, 3);
}
lean_ctor_set(x_126, 0, x_125);
x_127 = l_Lean_MessageData_ofFormat(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_Meta_Grind_Arith_checkExp___closed__4;
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Nat_reprFast(x_123);
if (lean_is_scalar(x_117)) {
 x_132 = lean_alloc_ctor(3, 1, 0);
} else {
 x_132 = x_117;
 lean_ctor_set_tag(x_132, 3);
}
lean_ctor_set(x_132, 0, x_131);
x_133 = l_Lean_MessageData_ofFormat(x_132);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_130);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Meta_Grind_Arith_checkExp___closed__6;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Meta_Grind_reportIssue(x_136, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_137) == 0)
{
lean_dec_ref(x_137);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_119);
lean_dec(x_117);
lean_dec(x_1);
x_141 = lean_ctor_get(x_121, 0);
lean_inc(x_141);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 x_142 = x_121;
} else {
 lean_dec_ref(x_121);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 1, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_141);
return x_143;
}
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_1);
x_144 = lean_ctor_get(x_113, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_145 = x_113;
} else {
 lean_dec_ref(x_113);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 1, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_144);
return x_146;
}
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_15);
if (x_147 == 0)
{
return x_15;
}
else
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_15, 0);
lean_inc(x_148);
lean_dec(x_15);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
return x_149;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_checkExp___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_checkExp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_checkExp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("zero", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natAbs", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succ", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("OfNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ofNat", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hPow", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMod", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hDiv", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hSub", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("instNatCastInt", 14, 14);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cast", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("natCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("NatCast", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Neg", 3, 3);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
x_21 = l_Lean_Expr_cleanupAnnotations(x_16);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_inc_ref(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_inc_ref(x_23);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_21);
x_28 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_28);
lean_dec_ref(x_23);
lean_inc_ref(x_25);
x_66 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3;
x_68 = l_Lean_Expr_isConstOf(x_66, x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6;
x_70 = l_Lean_Expr_isConstOf(x_66, x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12;
x_72 = l_Lean_Expr_isConstOf(x_66, x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_dec_ref(x_1);
x_73 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9;
x_74 = l_Lean_Expr_isConstOf(x_66, x_73);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = l_Lean_Expr_isApp(x_66);
if (x_75 == 0)
{
lean_dec_ref(x_66);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
goto block_20;
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = l_Lean_Expr_appFnCleanup___redArg(x_66);
x_77 = l_Lean_Expr_isApp(x_76);
if (x_77 == 0)
{
lean_dec_ref(x_76);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
goto block_20;
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = l_Lean_Expr_appFnCleanup___redArg(x_76);
x_79 = l_Lean_Expr_isApp(x_78);
if (x_79 == 0)
{
lean_dec_ref(x_78);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
goto block_20;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_80);
lean_dec_ref(x_25);
x_81 = l_Lean_Expr_appFnCleanup___redArg(x_78);
x_82 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15;
x_83 = l_Lean_Expr_isConstOf(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18;
x_85 = l_Lean_Expr_isConstOf(x_81, x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21;
x_87 = l_Lean_Expr_isConstOf(x_81, x_86);
if (x_87 == 0)
{
lean_object* x_88; uint8_t x_89; 
x_88 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27;
x_89 = l_Lean_Expr_isConstOf(x_81, x_88);
if (x_89 == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24;
x_91 = l_Lean_Expr_isConstOf(x_81, x_90);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30;
x_93 = l_Lean_Expr_isConstOf(x_81, x_92);
lean_dec_ref(x_81);
if (x_93 == 0)
{
lean_dec_ref(x_80);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
goto block_20;
}
else
{
lean_object* x_94; 
lean_dec(x_17);
x_94 = l_Lean_Meta_Structural_isInstHAddInt___redArg(x_80, x_7);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_unbox(x_96);
lean_dec(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_98 = lean_box(0);
lean_ctor_set(x_94, 0, x_98);
return x_94;
}
else
{
lean_object* x_99; 
lean_free_object(x_94);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_99 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_99;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_99);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_dec(x_101);
return x_102;
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_102);
if (x_104 == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_102, 0);
lean_dec(x_105);
x_106 = !lean_is_exclusive(x_103);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_103, 0);
x_108 = lean_int_add(x_101, x_107);
lean_dec(x_107);
lean_dec(x_101);
lean_ctor_set(x_103, 0, x_108);
return x_102;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_103, 0);
lean_inc(x_109);
lean_dec(x_103);
x_110 = lean_int_add(x_101, x_109);
lean_dec(x_109);
lean_dec(x_101);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_102, 0, x_111);
return x_102;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_102);
x_112 = lean_ctor_get(x_103, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_113 = x_103;
} else {
 lean_dec_ref(x_103);
 x_113 = lean_box(0);
}
x_114 = lean_int_add(x_101, x_112);
lean_dec(x_112);
lean_dec(x_101);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
else
{
lean_dec(x_101);
return x_102;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_99;
}
}
}
else
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_94, 0);
lean_inc(x_117);
lean_dec(x_94);
x_118 = lean_unbox(x_117);
lean_dec(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_119 = lean_box(0);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
else
{
lean_object* x_121; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_121 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
if (lean_obj_tag(x_122) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_121;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_dec(x_123);
return x_124;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_126 = x_124;
} else {
 lean_dec_ref(x_124);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_int_add(x_123, x_127);
lean_dec(x_127);
lean_dec(x_123);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(1, 1, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_126)) {
 x_131 = lean_alloc_ctor(0, 1, 0);
} else {
 x_131 = x_126;
}
lean_ctor_set(x_131, 0, x_130);
return x_131;
}
}
else
{
lean_dec(x_123);
return x_124;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_121;
}
}
}
}
else
{
uint8_t x_132; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_132 = !lean_is_exclusive(x_94);
if (x_132 == 0)
{
return x_94;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_94, 0);
lean_inc(x_133);
lean_dec(x_94);
x_134 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
}
}
else
{
lean_object* x_135; 
lean_dec_ref(x_81);
lean_dec(x_17);
x_135 = l_Lean_Meta_Structural_isInstHSubInt___redArg(x_80, x_7);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_139 = lean_box(0);
lean_ctor_set(x_135, 0, x_139);
return x_135;
}
else
{
lean_object* x_140; 
lean_free_object(x_135);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_140 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_140;
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec_ref(x_140);
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_dec(x_142);
return x_143;
}
else
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_143);
if (x_145 == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_143, 0);
lean_dec(x_146);
x_147 = !lean_is_exclusive(x_144);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_144, 0);
x_149 = lean_int_sub(x_142, x_148);
lean_dec(x_148);
lean_dec(x_142);
lean_ctor_set(x_144, 0, x_149);
return x_143;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_144, 0);
lean_inc(x_150);
lean_dec(x_144);
x_151 = lean_int_sub(x_142, x_150);
lean_dec(x_150);
lean_dec(x_142);
x_152 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_143, 0, x_152);
return x_143;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_143);
x_153 = lean_ctor_get(x_144, 0);
lean_inc(x_153);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_154 = x_144;
} else {
 lean_dec_ref(x_144);
 x_154 = lean_box(0);
}
x_155 = lean_int_sub(x_142, x_153);
lean_dec(x_153);
lean_dec(x_142);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(1, 1, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
x_157 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_157, 0, x_156);
return x_157;
}
}
}
else
{
lean_dec(x_142);
return x_143;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_140;
}
}
}
else
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_135, 0);
lean_inc(x_158);
lean_dec(x_135);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_160 = lean_box(0);
x_161 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
else
{
lean_object* x_162; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_162 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
if (lean_obj_tag(x_163) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_162;
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec_ref(x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_dec(x_164);
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_166, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_169 = x_166;
} else {
 lean_dec_ref(x_166);
 x_169 = lean_box(0);
}
x_170 = lean_int_sub(x_164, x_168);
lean_dec(x_168);
lean_dec(x_164);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
if (lean_is_scalar(x_167)) {
 x_172 = lean_alloc_ctor(0, 1, 0);
} else {
 x_172 = x_167;
}
lean_ctor_set(x_172, 0, x_171);
return x_172;
}
}
else
{
lean_dec(x_164);
return x_165;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_162;
}
}
}
}
else
{
uint8_t x_173; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_173 = !lean_is_exclusive(x_135);
if (x_173 == 0)
{
return x_135;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_135, 0);
lean_inc(x_174);
lean_dec(x_135);
x_175 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
}
}
}
else
{
lean_object* x_176; 
lean_dec_ref(x_81);
lean_dec(x_17);
x_176 = l_Lean_Meta_Structural_isInstHMulInt___redArg(x_80, x_7);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; uint8_t x_179; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_unbox(x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_180 = lean_box(0);
lean_ctor_set(x_176, 0, x_180);
return x_176;
}
else
{
lean_object* x_181; 
lean_free_object(x_176);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_181 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
if (lean_obj_tag(x_182) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_181;
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec_ref(x_181);
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_dec(x_183);
return x_184;
}
else
{
uint8_t x_186; 
x_186 = !lean_is_exclusive(x_184);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_184, 0);
lean_dec(x_187);
x_188 = !lean_is_exclusive(x_185);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_185, 0);
x_190 = lean_int_mul(x_183, x_189);
lean_dec(x_189);
lean_dec(x_183);
lean_ctor_set(x_185, 0, x_190);
return x_184;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_185, 0);
lean_inc(x_191);
lean_dec(x_185);
x_192 = lean_int_mul(x_183, x_191);
lean_dec(x_191);
lean_dec(x_183);
x_193 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_184, 0, x_193);
return x_184;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_184);
x_194 = lean_ctor_get(x_185, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 x_195 = x_185;
} else {
 lean_dec_ref(x_185);
 x_195 = lean_box(0);
}
x_196 = lean_int_mul(x_183, x_194);
lean_dec(x_194);
lean_dec(x_183);
if (lean_is_scalar(x_195)) {
 x_197 = lean_alloc_ctor(1, 1, 0);
} else {
 x_197 = x_195;
}
lean_ctor_set(x_197, 0, x_196);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_197);
return x_198;
}
}
}
else
{
lean_dec(x_183);
return x_184;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_181;
}
}
}
else
{
lean_object* x_199; uint8_t x_200; 
x_199 = lean_ctor_get(x_176, 0);
lean_inc(x_199);
lean_dec(x_176);
x_200 = lean_unbox(x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_201 = lean_box(0);
x_202 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
else
{
lean_object* x_203; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_203 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_203;
}
else
{
lean_object* x_205; lean_object* x_206; 
lean_dec_ref(x_203);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_dec(x_205);
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_210 = x_207;
} else {
 lean_dec_ref(x_207);
 x_210 = lean_box(0);
}
x_211 = lean_int_mul(x_205, x_209);
lean_dec(x_209);
lean_dec(x_205);
if (lean_is_scalar(x_210)) {
 x_212 = lean_alloc_ctor(1, 1, 0);
} else {
 x_212 = x_210;
}
lean_ctor_set(x_212, 0, x_211);
if (lean_is_scalar(x_208)) {
 x_213 = lean_alloc_ctor(0, 1, 0);
} else {
 x_213 = x_208;
}
lean_ctor_set(x_213, 0, x_212);
return x_213;
}
}
else
{
lean_dec(x_205);
return x_206;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_203;
}
}
}
}
else
{
uint8_t x_214; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_214 = !lean_is_exclusive(x_176);
if (x_214 == 0)
{
return x_176;
}
else
{
lean_object* x_215; lean_object* x_216; 
x_215 = lean_ctor_get(x_176, 0);
lean_inc(x_215);
lean_dec(x_176);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
}
}
}
else
{
lean_object* x_217; 
lean_dec_ref(x_81);
lean_dec(x_17);
x_217 = l_Lean_Meta_Structural_isInstHDivInt___redArg(x_80, x_7);
if (lean_obj_tag(x_217) == 0)
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_unbox(x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_object* x_221; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_221 = lean_box(0);
lean_ctor_set(x_217, 0, x_221);
return x_217;
}
else
{
lean_object* x_222; 
lean_free_object(x_217);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_222 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
if (lean_obj_tag(x_223) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_222;
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec_ref(x_222);
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
lean_dec_ref(x_223);
x_225 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_dec(x_224);
return x_225;
}
else
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_225);
if (x_227 == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_ctor_get(x_225, 0);
lean_dec(x_228);
x_229 = !lean_is_exclusive(x_226);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_226, 0);
x_231 = lean_int_ediv(x_224, x_230);
lean_dec(x_230);
lean_dec(x_224);
lean_ctor_set(x_226, 0, x_231);
return x_225;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_226, 0);
lean_inc(x_232);
lean_dec(x_226);
x_233 = lean_int_ediv(x_224, x_232);
lean_dec(x_232);
lean_dec(x_224);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_225, 0, x_234);
return x_225;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_225);
x_235 = lean_ctor_get(x_226, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 x_236 = x_226;
} else {
 lean_dec_ref(x_226);
 x_236 = lean_box(0);
}
x_237 = lean_int_ediv(x_224, x_235);
lean_dec(x_235);
lean_dec(x_224);
if (lean_is_scalar(x_236)) {
 x_238 = lean_alloc_ctor(1, 1, 0);
} else {
 x_238 = x_236;
}
lean_ctor_set(x_238, 0, x_237);
x_239 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
}
}
else
{
lean_dec(x_224);
return x_225;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_222;
}
}
}
else
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_217, 0);
lean_inc(x_240);
lean_dec(x_217);
x_241 = lean_unbox(x_240);
lean_dec(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_242 = lean_box(0);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_242);
return x_243;
}
else
{
lean_object* x_244; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_244 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
if (lean_obj_tag(x_245) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_244;
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec_ref(x_244);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
x_247 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_dec(x_246);
return x_247;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 x_249 = x_247;
} else {
 lean_dec_ref(x_247);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 x_251 = x_248;
} else {
 lean_dec_ref(x_248);
 x_251 = lean_box(0);
}
x_252 = lean_int_ediv(x_246, x_250);
lean_dec(x_250);
lean_dec(x_246);
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(1, 1, 0);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_252);
if (lean_is_scalar(x_249)) {
 x_254 = lean_alloc_ctor(0, 1, 0);
} else {
 x_254 = x_249;
}
lean_ctor_set(x_254, 0, x_253);
return x_254;
}
}
else
{
lean_dec(x_246);
return x_247;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_244;
}
}
}
}
else
{
uint8_t x_255; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_255 = !lean_is_exclusive(x_217);
if (x_255 == 0)
{
return x_217;
}
else
{
lean_object* x_256; lean_object* x_257; 
x_256 = lean_ctor_get(x_217, 0);
lean_inc(x_256);
lean_dec(x_217);
x_257 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
}
}
}
else
{
lean_object* x_258; 
lean_dec_ref(x_81);
lean_dec(x_17);
x_258 = l_Lean_Meta_Structural_isInstHModInt___redArg(x_80, x_7);
if (lean_obj_tag(x_258) == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_258);
if (x_259 == 0)
{
lean_object* x_260; uint8_t x_261; 
x_260 = lean_ctor_get(x_258, 0);
x_261 = lean_unbox(x_260);
lean_dec(x_260);
if (x_261 == 0)
{
lean_object* x_262; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_262 = lean_box(0);
lean_ctor_set(x_258, 0, x_262);
return x_258;
}
else
{
lean_object* x_263; 
lean_free_object(x_258);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_263 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
if (lean_obj_tag(x_264) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_263;
}
else
{
lean_object* x_265; lean_object* x_266; 
lean_dec_ref(x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
lean_dec_ref(x_264);
x_266 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 0)
{
lean_dec(x_265);
return x_266;
}
else
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_266);
if (x_268 == 0)
{
lean_object* x_269; uint8_t x_270; 
x_269 = lean_ctor_get(x_266, 0);
lean_dec(x_269);
x_270 = !lean_is_exclusive(x_267);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; 
x_271 = lean_ctor_get(x_267, 0);
x_272 = lean_int_emod(x_265, x_271);
lean_dec(x_271);
lean_dec(x_265);
lean_ctor_set(x_267, 0, x_272);
return x_266;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_267, 0);
lean_inc(x_273);
lean_dec(x_267);
x_274 = lean_int_emod(x_265, x_273);
lean_dec(x_273);
lean_dec(x_265);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_266, 0, x_275);
return x_266;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_266);
x_276 = lean_ctor_get(x_267, 0);
lean_inc(x_276);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 x_277 = x_267;
} else {
 lean_dec_ref(x_267);
 x_277 = lean_box(0);
}
x_278 = lean_int_emod(x_265, x_276);
lean_dec(x_276);
lean_dec(x_265);
if (lean_is_scalar(x_277)) {
 x_279 = lean_alloc_ctor(1, 1, 0);
} else {
 x_279 = x_277;
}
lean_ctor_set(x_279, 0, x_278);
x_280 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_280, 0, x_279);
return x_280;
}
}
}
else
{
lean_dec(x_265);
return x_266;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_263;
}
}
}
else
{
lean_object* x_281; uint8_t x_282; 
x_281 = lean_ctor_get(x_258, 0);
lean_inc(x_281);
lean_dec(x_258);
x_282 = lean_unbox(x_281);
lean_dec(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_283 = lean_box(0);
x_284 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_284, 0, x_283);
return x_284;
}
else
{
lean_object* x_285; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_285 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
if (lean_obj_tag(x_286) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_285;
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_dec_ref(x_285);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec_ref(x_286);
x_288 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
if (lean_obj_tag(x_289) == 0)
{
lean_dec(x_287);
return x_288;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 x_290 = x_288;
} else {
 lean_dec_ref(x_288);
 x_290 = lean_box(0);
}
x_291 = lean_ctor_get(x_289, 0);
lean_inc(x_291);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 x_292 = x_289;
} else {
 lean_dec_ref(x_289);
 x_292 = lean_box(0);
}
x_293 = lean_int_emod(x_287, x_291);
lean_dec(x_291);
lean_dec(x_287);
if (lean_is_scalar(x_292)) {
 x_294 = lean_alloc_ctor(1, 1, 0);
} else {
 x_294 = x_292;
}
lean_ctor_set(x_294, 0, x_293);
if (lean_is_scalar(x_290)) {
 x_295 = lean_alloc_ctor(0, 1, 0);
} else {
 x_295 = x_290;
}
lean_ctor_set(x_295, 0, x_294);
return x_295;
}
}
else
{
lean_dec(x_287);
return x_288;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_285;
}
}
}
}
else
{
uint8_t x_296; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_296 = !lean_is_exclusive(x_258);
if (x_296 == 0)
{
return x_258;
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_258, 0);
lean_inc(x_297);
lean_dec(x_258);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
}
}
}
else
{
lean_object* x_299; 
lean_dec_ref(x_81);
lean_dec(x_17);
x_299 = l_Lean_Meta_Structural_isInstHPowInt___redArg(x_80, x_7);
if (lean_obj_tag(x_299) == 0)
{
uint8_t x_300; 
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_ctor_get(x_299, 0);
x_302 = lean_unbox(x_301);
lean_dec(x_301);
if (x_302 == 0)
{
lean_object* x_303; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_303 = lean_box(0);
lean_ctor_set(x_299, 0, x_303);
return x_299;
}
else
{
lean_object* x_304; 
lean_free_object(x_299);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_304 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
if (lean_obj_tag(x_305) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_304;
}
else
{
lean_object* x_306; lean_object* x_307; 
lean_dec_ref(x_304);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
lean_dec_ref(x_305);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_307 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_307) == 0)
{
uint8_t x_308; 
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_307, 0);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; 
lean_dec(x_306);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_310 = lean_box(0);
lean_ctor_set(x_307, 0, x_310);
return x_307;
}
else
{
lean_object* x_311; lean_object* x_312; 
lean_free_object(x_307);
x_311 = lean_ctor_get(x_309, 0);
lean_inc(x_311);
lean_dec_ref(x_309);
lean_inc(x_311);
x_312 = l_Lean_Meta_Grind_Arith_checkExp(x_311, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_312) == 0)
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; 
x_314 = lean_ctor_get(x_312, 0);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; 
lean_dec(x_311);
lean_dec(x_306);
x_315 = lean_box(0);
lean_ctor_set(x_312, 0, x_315);
return x_312;
}
else
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_314);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_314, 0);
lean_dec(x_317);
x_318 = l_Int_pow(x_306, x_311);
lean_dec(x_311);
lean_dec(x_306);
lean_ctor_set(x_314, 0, x_318);
return x_312;
}
else
{
lean_object* x_319; lean_object* x_320; 
lean_dec(x_314);
x_319 = l_Int_pow(x_306, x_311);
lean_dec(x_311);
lean_dec(x_306);
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_319);
lean_ctor_set(x_312, 0, x_320);
return x_312;
}
}
}
else
{
lean_object* x_321; 
x_321 = lean_ctor_get(x_312, 0);
lean_inc(x_321);
lean_dec(x_312);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_311);
lean_dec(x_306);
x_322 = lean_box(0);
x_323 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_323, 0, x_322);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 x_324 = x_321;
} else {
 lean_dec_ref(x_321);
 x_324 = lean_box(0);
}
x_325 = l_Int_pow(x_306, x_311);
lean_dec(x_311);
lean_dec(x_306);
if (lean_is_scalar(x_324)) {
 x_326 = lean_alloc_ctor(1, 1, 0);
} else {
 x_326 = x_324;
}
lean_ctor_set(x_326, 0, x_325);
x_327 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_327, 0, x_326);
return x_327;
}
}
}
else
{
uint8_t x_328; 
lean_dec(x_311);
lean_dec(x_306);
x_328 = !lean_is_exclusive(x_312);
if (x_328 == 0)
{
return x_312;
}
else
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_312, 0);
lean_inc(x_329);
lean_dec(x_312);
x_330 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_330, 0, x_329);
return x_330;
}
}
}
}
else
{
lean_object* x_331; 
x_331 = lean_ctor_get(x_307, 0);
lean_inc(x_331);
lean_dec(x_307);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; 
lean_dec(x_306);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_332 = lean_box(0);
x_333 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_333, 0, x_332);
return x_333;
}
else
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_331, 0);
lean_inc(x_334);
lean_dec_ref(x_331);
lean_inc(x_334);
x_335 = l_Lean_Meta_Grind_Arith_checkExp(x_334, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_337 = x_335;
} else {
 lean_dec_ref(x_335);
 x_337 = lean_box(0);
}
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_334);
lean_dec(x_306);
x_338 = lean_box(0);
if (lean_is_scalar(x_337)) {
 x_339 = lean_alloc_ctor(0, 1, 0);
} else {
 x_339 = x_337;
}
lean_ctor_set(x_339, 0, x_338);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_340 = x_336;
} else {
 lean_dec_ref(x_336);
 x_340 = lean_box(0);
}
x_341 = l_Int_pow(x_306, x_334);
lean_dec(x_334);
lean_dec(x_306);
if (lean_is_scalar(x_340)) {
 x_342 = lean_alloc_ctor(1, 1, 0);
} else {
 x_342 = x_340;
}
lean_ctor_set(x_342, 0, x_341);
if (lean_is_scalar(x_337)) {
 x_343 = lean_alloc_ctor(0, 1, 0);
} else {
 x_343 = x_337;
}
lean_ctor_set(x_343, 0, x_342);
return x_343;
}
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_dec(x_334);
lean_dec(x_306);
x_344 = lean_ctor_get(x_335, 0);
lean_inc(x_344);
if (lean_is_exclusive(x_335)) {
 lean_ctor_release(x_335, 0);
 x_345 = x_335;
} else {
 lean_dec_ref(x_335);
 x_345 = lean_box(0);
}
if (lean_is_scalar(x_345)) {
 x_346 = lean_alloc_ctor(1, 1, 0);
} else {
 x_346 = x_345;
}
lean_ctor_set(x_346, 0, x_344);
return x_346;
}
}
}
}
else
{
uint8_t x_347; 
lean_dec(x_306);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_347 = !lean_is_exclusive(x_307);
if (x_347 == 0)
{
return x_307;
}
else
{
lean_object* x_348; lean_object* x_349; 
x_348 = lean_ctor_get(x_307, 0);
lean_inc(x_348);
lean_dec(x_307);
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_348);
return x_349;
}
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_304;
}
}
}
else
{
lean_object* x_350; uint8_t x_351; 
x_350 = lean_ctor_get(x_299, 0);
lean_inc(x_350);
lean_dec(x_299);
x_351 = lean_unbox(x_350);
lean_dec(x_350);
if (x_351 == 0)
{
lean_object* x_352; lean_object* x_353; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_352 = lean_box(0);
x_353 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_353, 0, x_352);
return x_353;
}
else
{
lean_object* x_354; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_354 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_28, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_354;
}
else
{
lean_object* x_356; lean_object* x_357; 
lean_dec_ref(x_354);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
lean_dec_ref(x_355);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_357 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_359 = x_357;
} else {
 lean_dec_ref(x_357);
 x_359 = lean_box(0);
}
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_360; lean_object* x_361; 
lean_dec(x_356);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_360 = lean_box(0);
if (lean_is_scalar(x_359)) {
 x_361 = lean_alloc_ctor(0, 1, 0);
} else {
 x_361 = x_359;
}
lean_ctor_set(x_361, 0, x_360);
return x_361;
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_359);
x_362 = lean_ctor_get(x_358, 0);
lean_inc(x_362);
lean_dec_ref(x_358);
lean_inc(x_362);
x_363 = l_Lean_Meta_Grind_Arith_checkExp(x_362, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_365 = x_363;
} else {
 lean_dec_ref(x_363);
 x_365 = lean_box(0);
}
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_362);
lean_dec(x_356);
x_366 = lean_box(0);
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(0, 1, 0);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_366);
return x_367;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 x_368 = x_364;
} else {
 lean_dec_ref(x_364);
 x_368 = lean_box(0);
}
x_369 = l_Int_pow(x_356, x_362);
lean_dec(x_362);
lean_dec(x_356);
if (lean_is_scalar(x_368)) {
 x_370 = lean_alloc_ctor(1, 1, 0);
} else {
 x_370 = x_368;
}
lean_ctor_set(x_370, 0, x_369);
if (lean_is_scalar(x_365)) {
 x_371 = lean_alloc_ctor(0, 1, 0);
} else {
 x_371 = x_365;
}
lean_ctor_set(x_371, 0, x_370);
return x_371;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_362);
lean_dec(x_356);
x_372 = lean_ctor_get(x_363, 0);
lean_inc(x_372);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_373 = x_363;
} else {
 lean_dec_ref(x_363);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(1, 1, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_372);
return x_374;
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_356);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_375 = lean_ctor_get(x_357, 0);
lean_inc(x_375);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_376 = x_357;
} else {
 lean_dec_ref(x_357);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(1, 1, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_375);
return x_377;
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_354;
}
}
}
}
else
{
uint8_t x_378; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_378 = !lean_is_exclusive(x_299);
if (x_378 == 0)
{
return x_299;
}
else
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_299, 0);
lean_inc(x_379);
lean_dec(x_299);
x_380 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_380, 0, x_379);
return x_380;
}
}
}
}
}
}
}
else
{
lean_object* x_381; 
lean_dec_ref(x_66);
lean_dec_ref(x_25);
lean_dec(x_17);
x_381 = l_Lean_Meta_Structural_isInstNegInt___redArg(x_28, x_7);
if (lean_obj_tag(x_381) == 0)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; uint8_t x_384; 
x_383 = lean_ctor_get(x_381, 0);
x_384 = lean_unbox(x_383);
lean_dec(x_383);
if (x_384 == 0)
{
lean_object* x_385; 
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_385 = lean_box(0);
lean_ctor_set(x_381, 0, x_385);
return x_381;
}
else
{
lean_object* x_386; 
lean_free_object(x_381);
x_386 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
if (lean_obj_tag(x_387) == 0)
{
return x_386;
}
else
{
uint8_t x_388; 
x_388 = !lean_is_exclusive(x_386);
if (x_388 == 0)
{
lean_object* x_389; uint8_t x_390; 
x_389 = lean_ctor_get(x_386, 0);
lean_dec(x_389);
x_390 = !lean_is_exclusive(x_387);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; 
x_391 = lean_ctor_get(x_387, 0);
x_392 = lean_int_neg(x_391);
lean_dec(x_391);
lean_ctor_set(x_387, 0, x_392);
return x_386;
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_387, 0);
lean_inc(x_393);
lean_dec(x_387);
x_394 = lean_int_neg(x_393);
lean_dec(x_393);
x_395 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_395, 0, x_394);
lean_ctor_set(x_386, 0, x_395);
return x_386;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
lean_dec(x_386);
x_396 = lean_ctor_get(x_387, 0);
lean_inc(x_396);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 x_397 = x_387;
} else {
 lean_dec_ref(x_387);
 x_397 = lean_box(0);
}
x_398 = lean_int_neg(x_396);
lean_dec(x_396);
if (lean_is_scalar(x_397)) {
 x_399 = lean_alloc_ctor(1, 1, 0);
} else {
 x_399 = x_397;
}
lean_ctor_set(x_399, 0, x_398);
x_400 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_400, 0, x_399);
return x_400;
}
}
}
else
{
return x_386;
}
}
}
else
{
lean_object* x_401; uint8_t x_402; 
x_401 = lean_ctor_get(x_381, 0);
lean_inc(x_401);
lean_dec(x_381);
x_402 = lean_unbox(x_401);
lean_dec(x_401);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; 
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_403 = lean_box(0);
x_404 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_404, 0, x_403);
return x_404;
}
else
{
lean_object* x_405; 
x_405 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
if (lean_obj_tag(x_406) == 0)
{
return x_405;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
if (lean_is_exclusive(x_405)) {
 lean_ctor_release(x_405, 0);
 x_407 = x_405;
} else {
 lean_dec_ref(x_405);
 x_407 = lean_box(0);
}
x_408 = lean_ctor_get(x_406, 0);
lean_inc(x_408);
if (lean_is_exclusive(x_406)) {
 lean_ctor_release(x_406, 0);
 x_409 = x_406;
} else {
 lean_dec_ref(x_406);
 x_409 = lean_box(0);
}
x_410 = lean_int_neg(x_408);
lean_dec(x_408);
if (lean_is_scalar(x_409)) {
 x_411 = lean_alloc_ctor(1, 1, 0);
} else {
 x_411 = x_409;
}
lean_ctor_set(x_411, 0, x_410);
if (lean_is_scalar(x_407)) {
 x_412 = lean_alloc_ctor(0, 1, 0);
} else {
 x_412 = x_407;
}
lean_ctor_set(x_412, 0, x_411);
return x_412;
}
}
else
{
return x_405;
}
}
}
}
else
{
uint8_t x_413; 
lean_dec_ref(x_27);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_413 = !lean_is_exclusive(x_381);
if (x_413 == 0)
{
return x_381;
}
else
{
lean_object* x_414; lean_object* x_415; 
x_414 = lean_ctor_get(x_381, 0);
lean_inc(x_414);
lean_dec(x_381);
x_415 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_415, 0, x_414);
return x_415;
}
}
}
}
else
{
lean_object* x_416; 
lean_dec_ref(x_66);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec(x_17);
x_416 = l_Lean_Meta_getIntValue_x3f(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 1)
{
lean_dec_ref(x_417);
return x_416;
}
else
{
uint8_t x_418; 
lean_dec(x_417);
x_418 = !lean_is_exclusive(x_416);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_416, 0);
lean_dec(x_419);
x_420 = lean_box(0);
lean_ctor_set(x_416, 0, x_420);
return x_416;
}
else
{
lean_object* x_421; lean_object* x_422; 
lean_dec(x_416);
x_421 = lean_box(0);
x_422 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_422, 0, x_421);
return x_422;
}
}
}
else
{
return x_416;
}
}
}
else
{
lean_dec_ref(x_66);
lean_dec_ref(x_25);
lean_dec(x_17);
lean_dec_ref(x_1);
x_29 = x_27;
x_30 = x_2;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = lean_box(0);
goto block_65;
}
}
else
{
lean_dec_ref(x_66);
lean_dec_ref(x_25);
lean_dec(x_17);
lean_dec_ref(x_1);
x_29 = x_27;
x_30 = x_2;
x_31 = x_3;
x_32 = x_4;
x_33 = x_5;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = lean_box(0);
goto block_65;
}
block_65:
{
lean_object* x_39; 
x_39 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_28, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Expr_cleanupAnnotations(x_40);
x_42 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1;
x_43 = l_Lean_Expr_isConstOf(x_41, x_42);
lean_dec_ref(x_41);
if (x_43 == 0)
{
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_29);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_44; 
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_36, x_37);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
if (lean_obj_tag(x_46) == 0)
{
lean_free_object(x_44);
x_11 = lean_box(0);
goto block_14;
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_nat_to_int(x_48);
lean_ctor_set(x_46, 0, x_49);
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 0);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_nat_to_int(x_50);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_44, 0, x_52);
return x_44;
}
}
}
else
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
lean_dec(x_44);
if (lean_obj_tag(x_53) == 0)
{
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = lean_nat_to_int(x_54);
if (lean_is_scalar(x_55)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_55;
}
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_44);
if (x_59 == 0)
{
return x_44;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_44, 0);
lean_inc(x_60);
lean_dec(x_44);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec_ref(x_29);
x_62 = !lean_is_exclusive(x_39);
if (x_62 == 0)
{
return x_39;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_39, 0);
lean_inc(x_63);
lean_dec(x_39);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
}
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_423; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_423 = !lean_is_exclusive(x_15);
if (x_423 == 0)
{
return x_15;
}
else
{
lean_object* x_424; lean_object* x_425; 
x_424 = lean_ctor_get(x_15, 0);
lean_inc(x_424);
lean_dec(x_15);
x_425 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_425, 0, x_424);
return x_425;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = l_Lean_Expr_cleanupAnnotations(x_17);
x_19 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2;
x_20 = l_Lean_Expr_isConstOf(x_18, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
lean_free_object(x_15);
x_21 = l_Lean_Expr_isApp(x_18);
if (x_21 == 0)
{
lean_dec_ref(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_24 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5;
x_25 = l_Lean_Expr_isConstOf(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7;
x_27 = l_Lean_Expr_isConstOf(x_23, x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9;
x_29 = l_Lean_Expr_isConstOf(x_23, x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_isApp(x_23);
if (x_30 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_inc_ref(x_23);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_inc_ref(x_31);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12;
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec_ref(x_1);
x_36 = l_Lean_Expr_isApp(x_33);
if (x_36 == 0)
{
lean_dec_ref(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_38 = l_Lean_Expr_isApp(x_37);
if (x_38 == 0)
{
lean_dec_ref(x_37);
lean_dec_ref(x_31);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_39; uint8_t x_40; 
x_39 = l_Lean_Expr_appFnCleanup___redArg(x_37);
x_40 = l_Lean_Expr_isApp(x_39);
if (x_40 == 0)
{
lean_dec_ref(x_39);
lean_dec_ref(x_31);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_41);
lean_dec_ref(x_23);
x_42 = lean_ctor_get(x_31, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_31);
x_43 = l_Lean_Expr_appFnCleanup___redArg(x_39);
x_44 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15;
x_45 = l_Lean_Expr_isConstOf(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18;
x_47 = l_Lean_Expr_isConstOf(x_43, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21;
x_49 = l_Lean_Expr_isConstOf(x_43, x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24;
x_51 = l_Lean_Expr_isConstOf(x_43, x_50);
if (x_51 == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27;
x_53 = l_Lean_Expr_isConstOf(x_43, x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30;
x_55 = l_Lean_Expr_isConstOf(x_43, x_54);
lean_dec_ref(x_43);
if (x_55 == 0)
{
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_56; 
x_56 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_42, x_7);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_60 = lean_box(0);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; 
lean_free_object(x_56);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_61 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec_ref(x_61);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_dec(x_63);
return x_64;
}
else
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_nat_add(x_63, x_69);
lean_dec(x_69);
lean_dec(x_63);
lean_ctor_set(x_65, 0, x_70);
return x_64;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_nat_add(x_63, x_71);
lean_dec(x_71);
lean_dec(x_63);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_64, 0, x_73);
return x_64;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_64);
x_74 = lean_ctor_get(x_65, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_nat_add(x_63, x_74);
lean_dec(x_74);
lean_dec(x_63);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
lean_dec(x_63);
return x_64;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_61;
}
}
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_56, 0);
lean_inc(x_79);
lean_dec(x_56);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
else
{
lean_object* x_83; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_83 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_83;
}
else
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
if (lean_obj_tag(x_87) == 0)
{
lean_dec(x_85);
return x_86;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_90 = x_87;
} else {
 lean_dec_ref(x_87);
 x_90 = lean_box(0);
}
x_91 = lean_nat_add(x_85, x_89);
lean_dec(x_89);
lean_dec(x_85);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
else
{
lean_dec(x_85);
return x_86;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_83;
}
}
}
}
else
{
uint8_t x_94; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_94 = !lean_is_exclusive(x_56);
if (x_94 == 0)
{
return x_56;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_56, 0);
lean_inc(x_95);
lean_dec(x_56);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; 
lean_dec_ref(x_43);
x_97 = l_Lean_Meta_Structural_isInstHMulNat___redArg(x_42, x_7);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_101 = lean_box(0);
lean_ctor_set(x_97, 0, x_101);
return x_97;
}
else
{
lean_object* x_102; 
lean_free_object(x_97);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_102 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_102;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec_ref(x_102);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_dec(x_104);
return x_105;
}
else
{
uint8_t x_107; 
x_107 = !lean_is_exclusive(x_105);
if (x_107 == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_105, 0);
lean_dec(x_108);
x_109 = !lean_is_exclusive(x_106);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_106, 0);
x_111 = lean_nat_mul(x_104, x_110);
lean_dec(x_110);
lean_dec(x_104);
lean_ctor_set(x_106, 0, x_111);
return x_105;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_106, 0);
lean_inc(x_112);
lean_dec(x_106);
x_113 = lean_nat_mul(x_104, x_112);
lean_dec(x_112);
lean_dec(x_104);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_105, 0, x_114);
return x_105;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_105);
x_115 = lean_ctor_get(x_106, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_116 = x_106;
} else {
 lean_dec_ref(x_106);
 x_116 = lean_box(0);
}
x_117 = lean_nat_mul(x_104, x_115);
lean_dec(x_115);
lean_dec(x_104);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
lean_dec(x_104);
return x_105;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_102;
}
}
}
else
{
lean_object* x_120; uint8_t x_121; 
x_120 = lean_ctor_get(x_97, 0);
lean_inc(x_120);
lean_dec(x_97);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
else
{
lean_object* x_124; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_124 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
if (lean_obj_tag(x_125) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_124;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_dec(x_126);
return x_127;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_131 = x_128;
} else {
 lean_dec_ref(x_128);
 x_131 = lean_box(0);
}
x_132 = lean_nat_mul(x_126, x_130);
lean_dec(x_130);
lean_dec(x_126);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(1, 1, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
if (lean_is_scalar(x_129)) {
 x_134 = lean_alloc_ctor(0, 1, 0);
} else {
 x_134 = x_129;
}
lean_ctor_set(x_134, 0, x_133);
return x_134;
}
}
else
{
lean_dec(x_126);
return x_127;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_124;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_135 = !lean_is_exclusive(x_97);
if (x_135 == 0)
{
return x_97;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_97, 0);
lean_inc(x_136);
lean_dec(x_97);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_136);
return x_137;
}
}
}
}
else
{
lean_object* x_138; 
lean_dec_ref(x_43);
x_138 = l_Lean_Meta_Structural_isInstHSubNat___redArg(x_42, x_7);
if (lean_obj_tag(x_138) == 0)
{
uint8_t x_139; 
x_139 = !lean_is_exclusive(x_138);
if (x_139 == 0)
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_138, 0);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_142 = lean_box(0);
lean_ctor_set(x_138, 0, x_142);
return x_138;
}
else
{
lean_object* x_143; 
lean_free_object(x_138);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_143 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
if (lean_obj_tag(x_144) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_143;
}
else
{
lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_143);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
lean_dec(x_145);
return x_146;
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_146);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_146, 0);
lean_dec(x_149);
x_150 = !lean_is_exclusive(x_147);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_147, 0);
x_152 = lean_nat_sub(x_145, x_151);
lean_dec(x_151);
lean_dec(x_145);
lean_ctor_set(x_147, 0, x_152);
return x_146;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_147, 0);
lean_inc(x_153);
lean_dec(x_147);
x_154 = lean_nat_sub(x_145, x_153);
lean_dec(x_153);
lean_dec(x_145);
x_155 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_146, 0, x_155);
return x_146;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_146);
x_156 = lean_ctor_get(x_147, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_157 = x_147;
} else {
 lean_dec_ref(x_147);
 x_157 = lean_box(0);
}
x_158 = lean_nat_sub(x_145, x_156);
lean_dec(x_156);
lean_dec(x_145);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(1, 1, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
}
}
else
{
lean_dec(x_145);
return x_146;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_143;
}
}
}
else
{
lean_object* x_161; uint8_t x_162; 
x_161 = lean_ctor_get(x_138, 0);
lean_inc(x_161);
lean_dec(x_138);
x_162 = lean_unbox(x_161);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_163 = lean_box(0);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
else
{
lean_object* x_165; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_165 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
if (lean_obj_tag(x_169) == 0)
{
lean_dec(x_167);
return x_168;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
x_171 = lean_ctor_get(x_169, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
x_173 = lean_nat_sub(x_167, x_171);
lean_dec(x_171);
lean_dec(x_167);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
if (lean_is_scalar(x_170)) {
 x_175 = lean_alloc_ctor(0, 1, 0);
} else {
 x_175 = x_170;
}
lean_ctor_set(x_175, 0, x_174);
return x_175;
}
}
else
{
lean_dec(x_167);
return x_168;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_165;
}
}
}
}
else
{
uint8_t x_176; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_176 = !lean_is_exclusive(x_138);
if (x_176 == 0)
{
return x_138;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_138, 0);
lean_inc(x_177);
lean_dec(x_138);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
}
}
else
{
lean_object* x_179; 
lean_dec_ref(x_43);
x_179 = l_Lean_Meta_Structural_isInstHDivNat___redArg(x_42, x_7);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_183 = lean_box(0);
lean_ctor_set(x_179, 0, x_183);
return x_179;
}
else
{
lean_object* x_184; 
lean_free_object(x_179);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_184 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_184;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec_ref(x_184);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
lean_dec(x_186);
return x_187;
}
else
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_187);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; 
x_190 = lean_ctor_get(x_187, 0);
lean_dec(x_190);
x_191 = !lean_is_exclusive(x_188);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_188, 0);
x_193 = lean_nat_div(x_186, x_192);
lean_dec(x_192);
lean_dec(x_186);
lean_ctor_set(x_188, 0, x_193);
return x_187;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_188, 0);
lean_inc(x_194);
lean_dec(x_188);
x_195 = lean_nat_div(x_186, x_194);
lean_dec(x_194);
lean_dec(x_186);
x_196 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_187, 0, x_196);
return x_187;
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_187);
x_197 = lean_ctor_get(x_188, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 x_198 = x_188;
} else {
 lean_dec_ref(x_188);
 x_198 = lean_box(0);
}
x_199 = lean_nat_div(x_186, x_197);
lean_dec(x_197);
lean_dec(x_186);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_200);
return x_201;
}
}
}
else
{
lean_dec(x_186);
return x_187;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_184;
}
}
}
else
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_179, 0);
lean_inc(x_202);
lean_dec(x_179);
x_203 = lean_unbox(x_202);
lean_dec(x_202);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_204 = lean_box(0);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
else
{
lean_object* x_206; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_206 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_obj_tag(x_207) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_206;
}
else
{
lean_object* x_208; lean_object* x_209; 
lean_dec_ref(x_206);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
if (lean_obj_tag(x_210) == 0)
{
lean_dec(x_208);
return x_209;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_211 = x_209;
} else {
 lean_dec_ref(x_209);
 x_211 = lean_box(0);
}
x_212 = lean_ctor_get(x_210, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_213 = x_210;
} else {
 lean_dec_ref(x_210);
 x_213 = lean_box(0);
}
x_214 = lean_nat_div(x_208, x_212);
lean_dec(x_212);
lean_dec(x_208);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(1, 1, 0);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_214);
if (lean_is_scalar(x_211)) {
 x_216 = lean_alloc_ctor(0, 1, 0);
} else {
 x_216 = x_211;
}
lean_ctor_set(x_216, 0, x_215);
return x_216;
}
}
else
{
lean_dec(x_208);
return x_209;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_206;
}
}
}
}
else
{
uint8_t x_217; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_217 = !lean_is_exclusive(x_179);
if (x_217 == 0)
{
return x_179;
}
else
{
lean_object* x_218; lean_object* x_219; 
x_218 = lean_ctor_get(x_179, 0);
lean_inc(x_218);
lean_dec(x_179);
x_219 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_219, 0, x_218);
return x_219;
}
}
}
}
else
{
lean_object* x_220; 
lean_dec_ref(x_43);
x_220 = l_Lean_Meta_Structural_isInstHModNat___redArg(x_42, x_7);
if (lean_obj_tag(x_220) == 0)
{
uint8_t x_221; 
x_221 = !lean_is_exclusive(x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; 
x_222 = lean_ctor_get(x_220, 0);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_224 = lean_box(0);
lean_ctor_set(x_220, 0, x_224);
return x_220;
}
else
{
lean_object* x_225; 
lean_free_object(x_220);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_225 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
if (lean_obj_tag(x_226) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_225;
}
else
{
lean_object* x_227; lean_object* x_228; 
lean_dec_ref(x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec_ref(x_226);
x_228 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
if (lean_obj_tag(x_229) == 0)
{
lean_dec(x_227);
return x_228;
}
else
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_228);
if (x_230 == 0)
{
lean_object* x_231; uint8_t x_232; 
x_231 = lean_ctor_get(x_228, 0);
lean_dec(x_231);
x_232 = !lean_is_exclusive(x_229);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_229, 0);
x_234 = lean_nat_mod(x_227, x_233);
lean_dec(x_233);
lean_dec(x_227);
lean_ctor_set(x_229, 0, x_234);
return x_228;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_229, 0);
lean_inc(x_235);
lean_dec(x_229);
x_236 = lean_nat_mod(x_227, x_235);
lean_dec(x_235);
lean_dec(x_227);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_228, 0, x_237);
return x_228;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_228);
x_238 = lean_ctor_get(x_229, 0);
lean_inc(x_238);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 x_239 = x_229;
} else {
 lean_dec_ref(x_229);
 x_239 = lean_box(0);
}
x_240 = lean_nat_mod(x_227, x_238);
lean_dec(x_238);
lean_dec(x_227);
if (lean_is_scalar(x_239)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_239;
}
lean_ctor_set(x_241, 0, x_240);
x_242 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_242, 0, x_241);
return x_242;
}
}
}
else
{
lean_dec(x_227);
return x_228;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_225;
}
}
}
else
{
lean_object* x_243; uint8_t x_244; 
x_243 = lean_ctor_get(x_220, 0);
lean_inc(x_243);
lean_dec(x_220);
x_244 = lean_unbox(x_243);
lean_dec(x_243);
if (x_244 == 0)
{
lean_object* x_245; lean_object* x_246; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_245 = lean_box(0);
x_246 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_246, 0, x_245);
return x_246;
}
else
{
lean_object* x_247; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_247 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 0)
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_247;
}
else
{
lean_object* x_249; lean_object* x_250; 
lean_dec_ref(x_247);
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
x_250 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
lean_dec(x_249);
return x_250;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 x_252 = x_250;
} else {
 lean_dec_ref(x_250);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_251, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_255 = lean_nat_mod(x_249, x_253);
lean_dec(x_253);
lean_dec(x_249);
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(1, 1, 0);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_255);
if (lean_is_scalar(x_252)) {
 x_257 = lean_alloc_ctor(0, 1, 0);
} else {
 x_257 = x_252;
}
lean_ctor_set(x_257, 0, x_256);
return x_257;
}
}
else
{
lean_dec(x_249);
return x_250;
}
}
}
else
{
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_247;
}
}
}
}
else
{
uint8_t x_258; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_258 = !lean_is_exclusive(x_220);
if (x_258 == 0)
{
return x_220;
}
else
{
lean_object* x_259; lean_object* x_260; 
x_259 = lean_ctor_get(x_220, 0);
lean_inc(x_259);
lean_dec(x_220);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
return x_260;
}
}
}
}
else
{
lean_object* x_261; 
lean_dec_ref(x_43);
x_261 = l_Lean_Meta_Structural_isInstHPowNat___redArg(x_42, x_7);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = lean_unbox(x_263);
lean_dec(x_263);
if (x_264 == 0)
{
lean_object* x_265; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_265 = lean_box(0);
lean_ctor_set(x_261, 0, x_265);
return x_261;
}
else
{
lean_object* x_266; 
lean_free_object(x_261);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_266 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
if (lean_obj_tag(x_267) == 0)
{
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_266;
}
else
{
lean_object* x_268; lean_object* x_269; 
lean_dec_ref(x_266);
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
lean_dec_ref(x_267);
lean_inc(x_268);
x_269 = l_Lean_Meta_Grind_Arith_checkExp(x_268, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_269) == 0)
{
uint8_t x_270; 
x_270 = !lean_is_exclusive(x_269);
if (x_270 == 0)
{
lean_object* x_271; 
x_271 = lean_ctor_get(x_269, 0);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; 
lean_dec(x_268);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_272 = lean_box(0);
lean_ctor_set(x_269, 0, x_272);
return x_269;
}
else
{
lean_object* x_273; 
lean_free_object(x_269);
lean_dec_ref(x_271);
x_273 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
if (lean_obj_tag(x_274) == 0)
{
lean_dec(x_268);
return x_273;
}
else
{
uint8_t x_275; 
x_275 = !lean_is_exclusive(x_273);
if (x_275 == 0)
{
lean_object* x_276; uint8_t x_277; 
x_276 = lean_ctor_get(x_273, 0);
lean_dec(x_276);
x_277 = !lean_is_exclusive(x_274);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_274, 0);
x_279 = lean_nat_pow(x_278, x_268);
lean_dec(x_268);
lean_dec(x_278);
lean_ctor_set(x_274, 0, x_279);
return x_273;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_274, 0);
lean_inc(x_280);
lean_dec(x_274);
x_281 = lean_nat_pow(x_280, x_268);
lean_dec(x_268);
lean_dec(x_280);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_273, 0, x_282);
return x_273;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_273);
x_283 = lean_ctor_get(x_274, 0);
lean_inc(x_283);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 x_284 = x_274;
} else {
 lean_dec_ref(x_274);
 x_284 = lean_box(0);
}
x_285 = lean_nat_pow(x_283, x_268);
lean_dec(x_268);
lean_dec(x_283);
if (lean_is_scalar(x_284)) {
 x_286 = lean_alloc_ctor(1, 1, 0);
} else {
 x_286 = x_284;
}
lean_ctor_set(x_286, 0, x_285);
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_286);
return x_287;
}
}
}
else
{
lean_dec(x_268);
return x_273;
}
}
}
else
{
lean_object* x_288; 
x_288 = lean_ctor_get(x_269, 0);
lean_inc(x_288);
lean_dec(x_269);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_268);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_289 = lean_box(0);
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_289);
return x_290;
}
else
{
lean_object* x_291; 
lean_dec_ref(x_288);
x_291 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
if (lean_obj_tag(x_292) == 0)
{
lean_dec(x_268);
return x_291;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_293 = x_291;
} else {
 lean_dec_ref(x_291);
 x_293 = lean_box(0);
}
x_294 = lean_ctor_get(x_292, 0);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
x_296 = lean_nat_pow(x_294, x_268);
lean_dec(x_268);
lean_dec(x_294);
if (lean_is_scalar(x_295)) {
 x_297 = lean_alloc_ctor(1, 1, 0);
} else {
 x_297 = x_295;
}
lean_ctor_set(x_297, 0, x_296);
if (lean_is_scalar(x_293)) {
 x_298 = lean_alloc_ctor(0, 1, 0);
} else {
 x_298 = x_293;
}
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
}
else
{
lean_dec(x_268);
return x_291;
}
}
}
}
else
{
uint8_t x_299; 
lean_dec(x_268);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_299 = !lean_is_exclusive(x_269);
if (x_299 == 0)
{
return x_269;
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_269, 0);
lean_inc(x_300);
lean_dec(x_269);
x_301 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_301, 0, x_300);
return x_301;
}
}
}
}
else
{
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_266;
}
}
}
else
{
lean_object* x_302; uint8_t x_303; 
x_302 = lean_ctor_get(x_261, 0);
lean_inc(x_302);
lean_dec(x_261);
x_303 = lean_unbox(x_302);
lean_dec(x_302);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_304 = lean_box(0);
x_305 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_305, 0, x_304);
return x_305;
}
else
{
lean_object* x_306; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_306 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
if (lean_obj_tag(x_307) == 0)
{
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_306;
}
else
{
lean_object* x_308; lean_object* x_309; 
lean_dec_ref(x_306);
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
lean_dec_ref(x_307);
lean_inc(x_308);
x_309 = l_Lean_Meta_Grind_Arith_checkExp(x_308, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_309) == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_311 = x_309;
} else {
 lean_dec_ref(x_309);
 x_311 = lean_box(0);
}
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_308);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_312 = lean_box(0);
if (lean_is_scalar(x_311)) {
 x_313 = lean_alloc_ctor(0, 1, 0);
} else {
 x_313 = x_311;
}
lean_ctor_set(x_313, 0, x_312);
return x_313;
}
else
{
lean_object* x_314; 
lean_dec(x_311);
lean_dec_ref(x_310);
x_314 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_41, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
if (lean_obj_tag(x_315) == 0)
{
lean_dec(x_308);
return x_314;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 x_316 = x_314;
} else {
 lean_dec_ref(x_314);
 x_316 = lean_box(0);
}
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 x_318 = x_315;
} else {
 lean_dec_ref(x_315);
 x_318 = lean_box(0);
}
x_319 = lean_nat_pow(x_317, x_308);
lean_dec(x_308);
lean_dec(x_317);
if (lean_is_scalar(x_318)) {
 x_320 = lean_alloc_ctor(1, 1, 0);
} else {
 x_320 = x_318;
}
lean_ctor_set(x_320, 0, x_319);
if (lean_is_scalar(x_316)) {
 x_321 = lean_alloc_ctor(0, 1, 0);
} else {
 x_321 = x_316;
}
lean_ctor_set(x_321, 0, x_320);
return x_321;
}
}
else
{
lean_dec(x_308);
return x_314;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_308);
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_322 = lean_ctor_get(x_309, 0);
lean_inc(x_322);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 x_323 = x_309;
} else {
 lean_dec_ref(x_309);
 x_323 = lean_box(0);
}
if (lean_is_scalar(x_323)) {
 x_324 = lean_alloc_ctor(1, 1, 0);
} else {
 x_324 = x_323;
}
lean_ctor_set(x_324, 0, x_322);
return x_324;
}
}
}
else
{
lean_dec_ref(x_41);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_306;
}
}
}
}
else
{
uint8_t x_325; 
lean_dec_ref(x_41);
lean_dec_ref(x_22);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_325 = !lean_is_exclusive(x_261);
if (x_325 == 0)
{
return x_261;
}
else
{
lean_object* x_326; lean_object* x_327; 
x_326 = lean_ctor_get(x_261, 0);
lean_inc(x_326);
lean_dec(x_261);
x_327 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_327, 0, x_326);
return x_327;
}
}
}
}
}
}
}
else
{
lean_object* x_328; 
lean_dec_ref(x_33);
lean_dec_ref(x_31);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
x_328 = l_Lean_Meta_getNatValue_x3f(x_1, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
if (lean_obj_tag(x_329) == 1)
{
lean_dec_ref(x_329);
return x_328;
}
else
{
uint8_t x_330; 
lean_dec(x_329);
x_330 = !lean_is_exclusive(x_328);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_328, 0);
lean_dec(x_331);
x_332 = lean_box(0);
lean_ctor_set(x_328, 0, x_332);
return x_328;
}
else
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_328);
x_333 = lean_box(0);
x_334 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_334, 0, x_333);
return x_334;
}
}
}
else
{
return x_328;
}
}
}
}
}
else
{
lean_object* x_335; 
lean_dec_ref(x_23);
lean_dec_ref(x_1);
x_335 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
if (lean_obj_tag(x_336) == 0)
{
return x_335;
}
else
{
uint8_t x_337; 
x_337 = !lean_is_exclusive(x_335);
if (x_337 == 0)
{
lean_object* x_338; uint8_t x_339; 
x_338 = lean_ctor_get(x_335, 0);
lean_dec(x_338);
x_339 = !lean_is_exclusive(x_336);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_336, 0);
x_341 = lean_unsigned_to_nat(1u);
x_342 = lean_nat_add(x_340, x_341);
lean_dec(x_340);
lean_ctor_set(x_336, 0, x_342);
return x_335;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
x_343 = lean_ctor_get(x_336, 0);
lean_inc(x_343);
lean_dec(x_336);
x_344 = lean_unsigned_to_nat(1u);
x_345 = lean_nat_add(x_343, x_344);
lean_dec(x_343);
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_335, 0, x_346);
return x_335;
}
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_335);
x_347 = lean_ctor_get(x_336, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 x_348 = x_336;
} else {
 lean_dec_ref(x_336);
 x_348 = lean_box(0);
}
x_349 = lean_unsigned_to_nat(1u);
x_350 = lean_nat_add(x_347, x_349);
lean_dec(x_347);
if (lean_is_scalar(x_348)) {
 x_351 = lean_alloc_ctor(1, 1, 0);
} else {
 x_351 = x_348;
}
lean_ctor_set(x_351, 0, x_350);
x_352 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_352, 0, x_351);
return x_352;
}
}
}
else
{
return x_335;
}
}
}
else
{
lean_object* x_353; 
lean_dec_ref(x_23);
lean_dec_ref(x_1);
x_353 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_353) == 0)
{
uint8_t x_354; 
x_354 = !lean_is_exclusive(x_353);
if (x_354 == 0)
{
lean_object* x_355; 
x_355 = lean_ctor_get(x_353, 0);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; 
x_356 = lean_box(0);
lean_ctor_set(x_353, 0, x_356);
return x_353;
}
else
{
uint8_t x_357; 
x_357 = !lean_is_exclusive(x_355);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_355, 0);
x_359 = l_Int_toNat(x_358);
lean_dec(x_358);
lean_ctor_set(x_355, 0, x_359);
return x_353;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_355, 0);
lean_inc(x_360);
lean_dec(x_355);
x_361 = l_Int_toNat(x_360);
lean_dec(x_360);
x_362 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_353, 0, x_362);
return x_353;
}
}
}
else
{
lean_object* x_363; 
x_363 = lean_ctor_get(x_353, 0);
lean_inc(x_363);
lean_dec(x_353);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_box(0);
x_365 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_365, 0, x_364);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_366 = lean_ctor_get(x_363, 0);
lean_inc(x_366);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 x_367 = x_363;
} else {
 lean_dec_ref(x_363);
 x_367 = lean_box(0);
}
x_368 = l_Int_toNat(x_366);
lean_dec(x_366);
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(1, 1, 0);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_368);
x_370 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_370, 0, x_369);
return x_370;
}
}
}
else
{
uint8_t x_371; 
x_371 = !lean_is_exclusive(x_353);
if (x_371 == 0)
{
return x_353;
}
else
{
lean_object* x_372; lean_object* x_373; 
x_372 = lean_ctor_get(x_353, 0);
lean_inc(x_372);
lean_dec(x_353);
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_372);
return x_373;
}
}
}
}
else
{
lean_object* x_374; 
lean_dec_ref(x_23);
lean_dec_ref(x_1);
x_374 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_374) == 0)
{
uint8_t x_375; 
x_375 = !lean_is_exclusive(x_374);
if (x_375 == 0)
{
lean_object* x_376; 
x_376 = lean_ctor_get(x_374, 0);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; 
x_377 = lean_box(0);
lean_ctor_set(x_374, 0, x_377);
return x_374;
}
else
{
uint8_t x_378; 
x_378 = !lean_is_exclusive(x_376);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_376, 0);
x_380 = lean_nat_abs(x_379);
lean_dec(x_379);
lean_ctor_set(x_376, 0, x_380);
return x_374;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_376, 0);
lean_inc(x_381);
lean_dec(x_376);
x_382 = lean_nat_abs(x_381);
lean_dec(x_381);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_374, 0, x_383);
return x_374;
}
}
}
else
{
lean_object* x_384; 
x_384 = lean_ctor_get(x_374, 0);
lean_inc(x_384);
lean_dec(x_374);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_box(0);
x_386 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_386, 0, x_385);
return x_386;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_387 = lean_ctor_get(x_384, 0);
lean_inc(x_387);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 x_388 = x_384;
} else {
 lean_dec_ref(x_384);
 x_388 = lean_box(0);
}
x_389 = lean_nat_abs(x_387);
lean_dec(x_387);
if (lean_is_scalar(x_388)) {
 x_390 = lean_alloc_ctor(1, 1, 0);
} else {
 x_390 = x_388;
}
lean_ctor_set(x_390, 0, x_389);
x_391 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_391, 0, x_390);
return x_391;
}
}
}
else
{
uint8_t x_392; 
x_392 = !lean_is_exclusive(x_374);
if (x_392 == 0)
{
return x_374;
}
else
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_374, 0);
lean_inc(x_393);
lean_dec(x_374);
x_394 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_394, 0, x_393);
return x_394;
}
}
}
}
}
else
{
lean_object* x_395; 
lean_dec_ref(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_395 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31;
lean_ctor_set(x_15, 0, x_395);
return x_15;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; 
x_396 = lean_ctor_get(x_15, 0);
lean_inc(x_396);
lean_dec(x_15);
x_397 = l_Lean_Expr_cleanupAnnotations(x_396);
x_398 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2;
x_399 = l_Lean_Expr_isConstOf(x_397, x_398);
if (x_399 == 0)
{
uint8_t x_400; 
x_400 = l_Lean_Expr_isApp(x_397);
if (x_400 == 0)
{
lean_dec_ref(x_397);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint8_t x_404; 
x_401 = lean_ctor_get(x_397, 1);
lean_inc_ref(x_401);
x_402 = l_Lean_Expr_appFnCleanup___redArg(x_397);
x_403 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5;
x_404 = l_Lean_Expr_isConstOf(x_402, x_403);
if (x_404 == 0)
{
lean_object* x_405; uint8_t x_406; 
x_405 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7;
x_406 = l_Lean_Expr_isConstOf(x_402, x_405);
if (x_406 == 0)
{
lean_object* x_407; uint8_t x_408; 
x_407 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9;
x_408 = l_Lean_Expr_isConstOf(x_402, x_407);
if (x_408 == 0)
{
uint8_t x_409; 
x_409 = l_Lean_Expr_isApp(x_402);
if (x_409 == 0)
{
lean_dec_ref(x_402);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_410; uint8_t x_411; 
lean_inc_ref(x_402);
x_410 = l_Lean_Expr_appFnCleanup___redArg(x_402);
x_411 = l_Lean_Expr_isApp(x_410);
if (x_411 == 0)
{
lean_dec_ref(x_410);
lean_dec_ref(x_402);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_412; lean_object* x_413; uint8_t x_414; 
lean_inc_ref(x_410);
x_412 = l_Lean_Expr_appFnCleanup___redArg(x_410);
x_413 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12;
x_414 = l_Lean_Expr_isConstOf(x_412, x_413);
if (x_414 == 0)
{
uint8_t x_415; 
lean_dec_ref(x_1);
x_415 = l_Lean_Expr_isApp(x_412);
if (x_415 == 0)
{
lean_dec_ref(x_412);
lean_dec_ref(x_410);
lean_dec_ref(x_402);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_416; uint8_t x_417; 
x_416 = l_Lean_Expr_appFnCleanup___redArg(x_412);
x_417 = l_Lean_Expr_isApp(x_416);
if (x_417 == 0)
{
lean_dec_ref(x_416);
lean_dec_ref(x_410);
lean_dec_ref(x_402);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_418; uint8_t x_419; 
x_418 = l_Lean_Expr_appFnCleanup___redArg(x_416);
x_419 = l_Lean_Expr_isApp(x_418);
if (x_419 == 0)
{
lean_dec_ref(x_418);
lean_dec_ref(x_410);
lean_dec_ref(x_402);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_420 = lean_ctor_get(x_402, 1);
lean_inc_ref(x_420);
lean_dec_ref(x_402);
x_421 = lean_ctor_get(x_410, 1);
lean_inc_ref(x_421);
lean_dec_ref(x_410);
x_422 = l_Lean_Expr_appFnCleanup___redArg(x_418);
x_423 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15;
x_424 = l_Lean_Expr_isConstOf(x_422, x_423);
if (x_424 == 0)
{
lean_object* x_425; uint8_t x_426; 
x_425 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18;
x_426 = l_Lean_Expr_isConstOf(x_422, x_425);
if (x_426 == 0)
{
lean_object* x_427; uint8_t x_428; 
x_427 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21;
x_428 = l_Lean_Expr_isConstOf(x_422, x_427);
if (x_428 == 0)
{
lean_object* x_429; uint8_t x_430; 
x_429 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24;
x_430 = l_Lean_Expr_isConstOf(x_422, x_429);
if (x_430 == 0)
{
lean_object* x_431; uint8_t x_432; 
x_431 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27;
x_432 = l_Lean_Expr_isConstOf(x_422, x_431);
if (x_432 == 0)
{
lean_object* x_433; uint8_t x_434; 
x_433 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30;
x_434 = l_Lean_Expr_isConstOf(x_422, x_433);
lean_dec_ref(x_422);
if (x_434 == 0)
{
lean_dec_ref(x_421);
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_435; 
x_435 = l_Lean_Meta_Structural_isInstHAddNat___redArg(x_421, x_7);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; uint8_t x_438; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 x_437 = x_435;
} else {
 lean_dec_ref(x_435);
 x_437 = lean_box(0);
}
x_438 = lean_unbox(x_436);
lean_dec(x_436);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_439 = lean_box(0);
if (lean_is_scalar(x_437)) {
 x_440 = lean_alloc_ctor(0, 1, 0);
} else {
 x_440 = x_437;
}
lean_ctor_set(x_440, 0, x_439);
return x_440;
}
else
{
lean_object* x_441; 
lean_dec(x_437);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_441 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_420, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
if (lean_obj_tag(x_442) == 0)
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_441;
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_dec_ref(x_441);
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
lean_dec_ref(x_442);
x_444 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
if (lean_obj_tag(x_445) == 0)
{
lean_dec(x_443);
return x_444;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 x_446 = x_444;
} else {
 lean_dec_ref(x_444);
 x_446 = lean_box(0);
}
x_447 = lean_ctor_get(x_445, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 x_448 = x_445;
} else {
 lean_dec_ref(x_445);
 x_448 = lean_box(0);
}
x_449 = lean_nat_add(x_443, x_447);
lean_dec(x_447);
lean_dec(x_443);
if (lean_is_scalar(x_448)) {
 x_450 = lean_alloc_ctor(1, 1, 0);
} else {
 x_450 = x_448;
}
lean_ctor_set(x_450, 0, x_449);
if (lean_is_scalar(x_446)) {
 x_451 = lean_alloc_ctor(0, 1, 0);
} else {
 x_451 = x_446;
}
lean_ctor_set(x_451, 0, x_450);
return x_451;
}
}
else
{
lean_dec(x_443);
return x_444;
}
}
}
else
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_441;
}
}
}
else
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_452 = lean_ctor_get(x_435, 0);
lean_inc(x_452);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 x_453 = x_435;
} else {
 lean_dec_ref(x_435);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 1, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_452);
return x_454;
}
}
}
else
{
lean_object* x_455; 
lean_dec_ref(x_422);
x_455 = l_Lean_Meta_Structural_isInstHMulNat___redArg(x_421, x_7);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 x_457 = x_455;
} else {
 lean_dec_ref(x_455);
 x_457 = lean_box(0);
}
x_458 = lean_unbox(x_456);
lean_dec(x_456);
if (x_458 == 0)
{
lean_object* x_459; lean_object* x_460; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_459 = lean_box(0);
if (lean_is_scalar(x_457)) {
 x_460 = lean_alloc_ctor(0, 1, 0);
} else {
 x_460 = x_457;
}
lean_ctor_set(x_460, 0, x_459);
return x_460;
}
else
{
lean_object* x_461; 
lean_dec(x_457);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_461 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_420, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
if (lean_obj_tag(x_462) == 0)
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_461;
}
else
{
lean_object* x_463; lean_object* x_464; 
lean_dec_ref(x_461);
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
lean_dec_ref(x_462);
x_464 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
if (lean_obj_tag(x_465) == 0)
{
lean_dec(x_463);
return x_464;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 x_466 = x_464;
} else {
 lean_dec_ref(x_464);
 x_466 = lean_box(0);
}
x_467 = lean_ctor_get(x_465, 0);
lean_inc(x_467);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 x_468 = x_465;
} else {
 lean_dec_ref(x_465);
 x_468 = lean_box(0);
}
x_469 = lean_nat_mul(x_463, x_467);
lean_dec(x_467);
lean_dec(x_463);
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(1, 1, 0);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_469);
if (lean_is_scalar(x_466)) {
 x_471 = lean_alloc_ctor(0, 1, 0);
} else {
 x_471 = x_466;
}
lean_ctor_set(x_471, 0, x_470);
return x_471;
}
}
else
{
lean_dec(x_463);
return x_464;
}
}
}
else
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_461;
}
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_472 = lean_ctor_get(x_455, 0);
lean_inc(x_472);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 x_473 = x_455;
} else {
 lean_dec_ref(x_455);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 1, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_472);
return x_474;
}
}
}
else
{
lean_object* x_475; 
lean_dec_ref(x_422);
x_475 = l_Lean_Meta_Structural_isInstHSubNat___redArg(x_421, x_7);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; uint8_t x_478; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 x_477 = x_475;
} else {
 lean_dec_ref(x_475);
 x_477 = lean_box(0);
}
x_478 = lean_unbox(x_476);
lean_dec(x_476);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_479 = lean_box(0);
if (lean_is_scalar(x_477)) {
 x_480 = lean_alloc_ctor(0, 1, 0);
} else {
 x_480 = x_477;
}
lean_ctor_set(x_480, 0, x_479);
return x_480;
}
else
{
lean_object* x_481; 
lean_dec(x_477);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_481 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_420, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_481) == 0)
{
lean_object* x_482; 
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
if (lean_obj_tag(x_482) == 0)
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_481;
}
else
{
lean_object* x_483; lean_object* x_484; 
lean_dec_ref(x_481);
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
lean_dec_ref(x_482);
x_484 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
if (lean_obj_tag(x_485) == 0)
{
lean_dec(x_483);
return x_484;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; 
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 x_486 = x_484;
} else {
 lean_dec_ref(x_484);
 x_486 = lean_box(0);
}
x_487 = lean_ctor_get(x_485, 0);
lean_inc(x_487);
if (lean_is_exclusive(x_485)) {
 lean_ctor_release(x_485, 0);
 x_488 = x_485;
} else {
 lean_dec_ref(x_485);
 x_488 = lean_box(0);
}
x_489 = lean_nat_sub(x_483, x_487);
lean_dec(x_487);
lean_dec(x_483);
if (lean_is_scalar(x_488)) {
 x_490 = lean_alloc_ctor(1, 1, 0);
} else {
 x_490 = x_488;
}
lean_ctor_set(x_490, 0, x_489);
if (lean_is_scalar(x_486)) {
 x_491 = lean_alloc_ctor(0, 1, 0);
} else {
 x_491 = x_486;
}
lean_ctor_set(x_491, 0, x_490);
return x_491;
}
}
else
{
lean_dec(x_483);
return x_484;
}
}
}
else
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_481;
}
}
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_492 = lean_ctor_get(x_475, 0);
lean_inc(x_492);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 x_493 = x_475;
} else {
 lean_dec_ref(x_475);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 1, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_492);
return x_494;
}
}
}
else
{
lean_object* x_495; 
lean_dec_ref(x_422);
x_495 = l_Lean_Meta_Structural_isInstHDivNat___redArg(x_421, x_7);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; uint8_t x_498; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 x_497 = x_495;
} else {
 lean_dec_ref(x_495);
 x_497 = lean_box(0);
}
x_498 = lean_unbox(x_496);
lean_dec(x_496);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_499 = lean_box(0);
if (lean_is_scalar(x_497)) {
 x_500 = lean_alloc_ctor(0, 1, 0);
} else {
 x_500 = x_497;
}
lean_ctor_set(x_500, 0, x_499);
return x_500;
}
else
{
lean_object* x_501; 
lean_dec(x_497);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_501 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_420, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
if (lean_obj_tag(x_502) == 0)
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_501;
}
else
{
lean_object* x_503; lean_object* x_504; 
lean_dec_ref(x_501);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
lean_dec_ref(x_502);
x_504 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
if (lean_obj_tag(x_505) == 0)
{
lean_dec(x_503);
return x_504;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 x_506 = x_504;
} else {
 lean_dec_ref(x_504);
 x_506 = lean_box(0);
}
x_507 = lean_ctor_get(x_505, 0);
lean_inc(x_507);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 x_508 = x_505;
} else {
 lean_dec_ref(x_505);
 x_508 = lean_box(0);
}
x_509 = lean_nat_div(x_503, x_507);
lean_dec(x_507);
lean_dec(x_503);
if (lean_is_scalar(x_508)) {
 x_510 = lean_alloc_ctor(1, 1, 0);
} else {
 x_510 = x_508;
}
lean_ctor_set(x_510, 0, x_509);
if (lean_is_scalar(x_506)) {
 x_511 = lean_alloc_ctor(0, 1, 0);
} else {
 x_511 = x_506;
}
lean_ctor_set(x_511, 0, x_510);
return x_511;
}
}
else
{
lean_dec(x_503);
return x_504;
}
}
}
else
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_501;
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_512 = lean_ctor_get(x_495, 0);
lean_inc(x_512);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 x_513 = x_495;
} else {
 lean_dec_ref(x_495);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 1, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_512);
return x_514;
}
}
}
else
{
lean_object* x_515; 
lean_dec_ref(x_422);
x_515 = l_Lean_Meta_Structural_isInstHModNat___redArg(x_421, x_7);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 x_517 = x_515;
} else {
 lean_dec_ref(x_515);
 x_517 = lean_box(0);
}
x_518 = lean_unbox(x_516);
lean_dec(x_516);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_519 = lean_box(0);
if (lean_is_scalar(x_517)) {
 x_520 = lean_alloc_ctor(0, 1, 0);
} else {
 x_520 = x_517;
}
lean_ctor_set(x_520, 0, x_519);
return x_520;
}
else
{
lean_object* x_521; 
lean_dec(x_517);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_521 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_420, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
if (lean_obj_tag(x_522) == 0)
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_521;
}
else
{
lean_object* x_523; lean_object* x_524; 
lean_dec_ref(x_521);
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
lean_dec_ref(x_522);
x_524 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
if (lean_obj_tag(x_525) == 0)
{
lean_dec(x_523);
return x_524;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 x_526 = x_524;
} else {
 lean_dec_ref(x_524);
 x_526 = lean_box(0);
}
x_527 = lean_ctor_get(x_525, 0);
lean_inc(x_527);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 x_528 = x_525;
} else {
 lean_dec_ref(x_525);
 x_528 = lean_box(0);
}
x_529 = lean_nat_mod(x_523, x_527);
lean_dec(x_527);
lean_dec(x_523);
if (lean_is_scalar(x_528)) {
 x_530 = lean_alloc_ctor(1, 1, 0);
} else {
 x_530 = x_528;
}
lean_ctor_set(x_530, 0, x_529);
if (lean_is_scalar(x_526)) {
 x_531 = lean_alloc_ctor(0, 1, 0);
} else {
 x_531 = x_526;
}
lean_ctor_set(x_531, 0, x_530);
return x_531;
}
}
else
{
lean_dec(x_523);
return x_524;
}
}
}
else
{
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_521;
}
}
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_532 = lean_ctor_get(x_515, 0);
lean_inc(x_532);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 x_533 = x_515;
} else {
 lean_dec_ref(x_515);
 x_533 = lean_box(0);
}
if (lean_is_scalar(x_533)) {
 x_534 = lean_alloc_ctor(1, 1, 0);
} else {
 x_534 = x_533;
}
lean_ctor_set(x_534, 0, x_532);
return x_534;
}
}
}
else
{
lean_object* x_535; 
lean_dec_ref(x_422);
x_535 = l_Lean_Meta_Structural_isInstHPowNat___redArg(x_421, x_7);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; uint8_t x_538; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 x_537 = x_535;
} else {
 lean_dec_ref(x_535);
 x_537 = lean_box(0);
}
x_538 = lean_unbox(x_536);
lean_dec(x_536);
if (x_538 == 0)
{
lean_object* x_539; lean_object* x_540; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_539 = lean_box(0);
if (lean_is_scalar(x_537)) {
 x_540 = lean_alloc_ctor(0, 1, 0);
} else {
 x_540 = x_537;
}
lean_ctor_set(x_540, 0, x_539);
return x_540;
}
else
{
lean_object* x_541; 
lean_dec(x_537);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_541 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
if (lean_obj_tag(x_542) == 0)
{
lean_dec_ref(x_420);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_541;
}
else
{
lean_object* x_543; lean_object* x_544; 
lean_dec_ref(x_541);
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
lean_dec_ref(x_542);
lean_inc(x_543);
x_544 = l_Lean_Meta_Grind_Arith_checkExp(x_543, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 x_546 = x_544;
} else {
 lean_dec_ref(x_544);
 x_546 = lean_box(0);
}
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_547; lean_object* x_548; 
lean_dec(x_543);
lean_dec_ref(x_420);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_547 = lean_box(0);
if (lean_is_scalar(x_546)) {
 x_548 = lean_alloc_ctor(0, 1, 0);
} else {
 x_548 = x_546;
}
lean_ctor_set(x_548, 0, x_547);
return x_548;
}
else
{
lean_object* x_549; 
lean_dec(x_546);
lean_dec_ref(x_545);
x_549 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_420, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_549, 0);
lean_inc(x_550);
if (lean_obj_tag(x_550) == 0)
{
lean_dec(x_543);
return x_549;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 x_551 = x_549;
} else {
 lean_dec_ref(x_549);
 x_551 = lean_box(0);
}
x_552 = lean_ctor_get(x_550, 0);
lean_inc(x_552);
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 x_553 = x_550;
} else {
 lean_dec_ref(x_550);
 x_553 = lean_box(0);
}
x_554 = lean_nat_pow(x_552, x_543);
lean_dec(x_543);
lean_dec(x_552);
if (lean_is_scalar(x_553)) {
 x_555 = lean_alloc_ctor(1, 1, 0);
} else {
 x_555 = x_553;
}
lean_ctor_set(x_555, 0, x_554);
if (lean_is_scalar(x_551)) {
 x_556 = lean_alloc_ctor(0, 1, 0);
} else {
 x_556 = x_551;
}
lean_ctor_set(x_556, 0, x_555);
return x_556;
}
}
else
{
lean_dec(x_543);
return x_549;
}
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_543);
lean_dec_ref(x_420);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_557 = lean_ctor_get(x_544, 0);
lean_inc(x_557);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 x_558 = x_544;
} else {
 lean_dec_ref(x_544);
 x_558 = lean_box(0);
}
if (lean_is_scalar(x_558)) {
 x_559 = lean_alloc_ctor(1, 1, 0);
} else {
 x_559 = x_558;
}
lean_ctor_set(x_559, 0, x_557);
return x_559;
}
}
}
else
{
lean_dec_ref(x_420);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_541;
}
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec_ref(x_420);
lean_dec_ref(x_401);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_560 = lean_ctor_get(x_535, 0);
lean_inc(x_560);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 x_561 = x_535;
} else {
 lean_dec_ref(x_535);
 x_561 = lean_box(0);
}
if (lean_is_scalar(x_561)) {
 x_562 = lean_alloc_ctor(1, 1, 0);
} else {
 x_562 = x_561;
}
lean_ctor_set(x_562, 0, x_560);
return x_562;
}
}
}
}
}
}
else
{
lean_object* x_563; 
lean_dec_ref(x_412);
lean_dec_ref(x_410);
lean_dec_ref(x_402);
lean_dec_ref(x_401);
x_563 = l_Lean_Meta_getNatValue_x3f(x_1, x_6, x_7, x_8, x_9);
lean_dec_ref(x_1);
if (lean_obj_tag(x_563) == 0)
{
lean_object* x_564; 
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
if (lean_obj_tag(x_564) == 1)
{
lean_dec_ref(x_564);
return x_563;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_564);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 x_565 = x_563;
} else {
 lean_dec_ref(x_563);
 x_565 = lean_box(0);
}
x_566 = lean_box(0);
if (lean_is_scalar(x_565)) {
 x_567 = lean_alloc_ctor(0, 1, 0);
} else {
 x_567 = x_565;
}
lean_ctor_set(x_567, 0, x_566);
return x_567;
}
}
else
{
return x_563;
}
}
}
}
}
else
{
lean_object* x_568; 
lean_dec_ref(x_402);
lean_dec_ref(x_1);
x_568 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
if (lean_obj_tag(x_569) == 0)
{
return x_568;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 x_570 = x_568;
} else {
 lean_dec_ref(x_568);
 x_570 = lean_box(0);
}
x_571 = lean_ctor_get(x_569, 0);
lean_inc(x_571);
if (lean_is_exclusive(x_569)) {
 lean_ctor_release(x_569, 0);
 x_572 = x_569;
} else {
 lean_dec_ref(x_569);
 x_572 = lean_box(0);
}
x_573 = lean_unsigned_to_nat(1u);
x_574 = lean_nat_add(x_571, x_573);
lean_dec(x_571);
if (lean_is_scalar(x_572)) {
 x_575 = lean_alloc_ctor(1, 1, 0);
} else {
 x_575 = x_572;
}
lean_ctor_set(x_575, 0, x_574);
if (lean_is_scalar(x_570)) {
 x_576 = lean_alloc_ctor(0, 1, 0);
} else {
 x_576 = x_570;
}
lean_ctor_set(x_576, 0, x_575);
return x_576;
}
}
else
{
return x_568;
}
}
}
else
{
lean_object* x_577; 
lean_dec_ref(x_402);
lean_dec_ref(x_1);
x_577 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 x_579 = x_577;
} else {
 lean_dec_ref(x_577);
 x_579 = lean_box(0);
}
if (lean_obj_tag(x_578) == 0)
{
lean_object* x_580; lean_object* x_581; 
x_580 = lean_box(0);
if (lean_is_scalar(x_579)) {
 x_581 = lean_alloc_ctor(0, 1, 0);
} else {
 x_581 = x_579;
}
lean_ctor_set(x_581, 0, x_580);
return x_581;
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_582 = lean_ctor_get(x_578, 0);
lean_inc(x_582);
if (lean_is_exclusive(x_578)) {
 lean_ctor_release(x_578, 0);
 x_583 = x_578;
} else {
 lean_dec_ref(x_578);
 x_583 = lean_box(0);
}
x_584 = l_Int_toNat(x_582);
lean_dec(x_582);
if (lean_is_scalar(x_583)) {
 x_585 = lean_alloc_ctor(1, 1, 0);
} else {
 x_585 = x_583;
}
lean_ctor_set(x_585, 0, x_584);
if (lean_is_scalar(x_579)) {
 x_586 = lean_alloc_ctor(0, 1, 0);
} else {
 x_586 = x_579;
}
lean_ctor_set(x_586, 0, x_585);
return x_586;
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_577, 0);
lean_inc(x_587);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 x_588 = x_577;
} else {
 lean_dec_ref(x_577);
 x_588 = lean_box(0);
}
if (lean_is_scalar(x_588)) {
 x_589 = lean_alloc_ctor(1, 1, 0);
} else {
 x_589 = x_588;
}
lean_ctor_set(x_589, 0, x_587);
return x_589;
}
}
}
else
{
lean_object* x_590; 
lean_dec_ref(x_402);
lean_dec_ref(x_1);
x_590 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_401, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_592 = x_590;
} else {
 lean_dec_ref(x_590);
 x_592 = lean_box(0);
}
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_593; lean_object* x_594; 
x_593 = lean_box(0);
if (lean_is_scalar(x_592)) {
 x_594 = lean_alloc_ctor(0, 1, 0);
} else {
 x_594 = x_592;
}
lean_ctor_set(x_594, 0, x_593);
return x_594;
}
else
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_595 = lean_ctor_get(x_591, 0);
lean_inc(x_595);
if (lean_is_exclusive(x_591)) {
 lean_ctor_release(x_591, 0);
 x_596 = x_591;
} else {
 lean_dec_ref(x_591);
 x_596 = lean_box(0);
}
x_597 = lean_nat_abs(x_595);
lean_dec(x_595);
if (lean_is_scalar(x_596)) {
 x_598 = lean_alloc_ctor(1, 1, 0);
} else {
 x_598 = x_596;
}
lean_ctor_set(x_598, 0, x_597);
if (lean_is_scalar(x_592)) {
 x_599 = lean_alloc_ctor(0, 1, 0);
} else {
 x_599 = x_592;
}
lean_ctor_set(x_599, 0, x_598);
return x_599;
}
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_590, 0);
lean_inc(x_600);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_601 = x_590;
} else {
 lean_dec_ref(x_590);
 x_601 = lean_box(0);
}
if (lean_is_scalar(x_601)) {
 x_602 = lean_alloc_ctor(1, 1, 0);
} else {
 x_602 = x_601;
}
lean_ctor_set(x_602, 0, x_600);
return x_602;
}
}
}
}
else
{
lean_object* x_603; lean_object* x_604; 
lean_dec_ref(x_397);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_603 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31;
x_604 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_604, 0, x_603);
return x_604;
}
}
}
else
{
uint8_t x_605; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_605 = !lean_is_exclusive(x_15);
if (x_605 == 0)
{
return x_15;
}
else
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_ctor_get(x_15, 0);
lean_inc(x_606);
lean_dec(x_15);
x_607 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_607, 0, x_606);
return x_607;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalNat_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_evalNat_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_evalInt_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_evalInt_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_EvalNum(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_checkExp___closed__0 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__0);
l_Lean_Meta_Grind_Arith_checkExp___closed__1 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__1);
l_Lean_Meta_Grind_Arith_checkExp___closed__2 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__2);
l_Lean_Meta_Grind_Arith_checkExp___closed__3 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__3);
l_Lean_Meta_Grind_Arith_checkExp___closed__4 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__4);
l_Lean_Meta_Grind_Arith_checkExp___closed__5 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__5);
l_Lean_Meta_Grind_Arith_checkExp___closed__6 = _init_l_Lean_Meta_Grind_Arith_checkExp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_checkExp___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__8);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__9);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__10);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__11);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__12);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__13);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__14);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__15);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__16);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__17);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__18);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__19);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__20);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__21);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__22);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__23);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__24);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__25);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__26);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__27);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__28);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__29);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__30);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalNatCore___closed__31);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__0);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__1);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__2);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__3);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__5);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__4);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__6);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__8);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__7);
l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_Arith_EvalNum_0__Lean_Meta_Grind_Arith_evalIntCore___closed__9);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
