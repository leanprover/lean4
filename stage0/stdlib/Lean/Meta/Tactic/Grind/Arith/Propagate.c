// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Propagate
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind import Lean.Meta.Tactic.Grind.PropagatorAttr
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatXOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatXOr___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateNatAnd___closed__6;
static lean_object* l_Lean_Meta_Grind_propagateNatOr___closed__5;
static lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatAnd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Nat_shiftRight___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatAnd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___closed__5;
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatAnd___regBuiltin_Lean_Meta_Grind_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8____boxed(lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatBinOp___closed__2;
lean_object* l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatOr___closed__4;
static lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___closed__0;
static lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___closed__3;
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatXOr___regBuiltin_Lean_Meta_Grind_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatAnd___closed__5;
static lean_object* l_Lean_Meta_Grind_propagateNatOr___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatXOr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatXOr___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
static lean_object* l_Lean_Meta_Grind_propagateNatBinOp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatOr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatOr___regBuiltin_Lean_Meta_Grind_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8____boxed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatOr___closed__0;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatXOr___closed__5;
static lean_object* l_Lean_Meta_Grind_propagateNatOr___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateNatAnd___closed__3;
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatAnd___closed__4;
static lean_object* l_Lean_Meta_Grind_propagateNatXOr___closed__1;
static lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___closed__4;
static lean_object* l_Lean_Meta_Grind_propagateNatOr___closed__3;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatBinOp___closed__0;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatXOr___regBuiltin_Lean_Meta_Grind_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
static lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___closed__2;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatXOr___closed__0;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Nat_xor___boxed(lean_object*, lean_object*);
lean_object* l_Nat_lor___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatAnd___closed__0;
lean_object* l_Nat_land___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatXOr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatBinOp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatAnd___closed__1;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___closed__3;
lean_object* l_Nat_shiftLeft___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatAnd___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatAnd___regBuiltin_Lean_Meta_Grind_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatOr___regBuiltin_Lean_Meta_Grind_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateNatAnd___closed__7;
extern lean_object* l_Lean_eagerReflBoolTrue;
static lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___closed__4;
static lean_object* _init_l_Lean_Meta_Grind_propagateNatBinOp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatBinOp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateNatBinOp___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatBinOp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_eagerReflBoolTrue;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatBinOp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = l_Lean_Expr_isAppOfArity(x_4, x_1, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_18 = l_Lean_Expr_getAppNumArgs(x_4);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_18, x_19);
lean_dec(x_18);
lean_inc(x_20);
x_21 = l_Lean_Expr_getRevArg_x21(x_4, x_20);
x_22 = l_Lean_Meta_Grind_propagateNatBinOp___closed__1;
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
lean_dec_ref(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_nat_sub(x_20, x_19);
lean_dec(x_20);
x_27 = l_Lean_Expr_getRevArg_x21(x_4, x_26);
x_28 = l_Lean_Expr_isConstOf(x_27, x_22);
lean_dec_ref(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_st_ref_get(x_5);
x_32 = l_Lean_Expr_getRevArg_x21(x_4, x_19);
lean_inc_ref(x_32);
x_33 = l_Lean_Meta_Grind_Goal_getRoot(x_31, x_32, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_35 = l_Lean_Meta_getNatValue_x3f(x_34, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_35, 0);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = lean_st_ref_get(x_5);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_Expr_getRevArg_x21(x_4, x_40);
lean_inc_ref(x_41);
x_42 = l_Lean_Meta_Grind_Goal_getRoot(x_39, x_41, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_44 = l_Lean_Meta_getNatValue_x3f(x_43, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = lean_ctor_get(x_44, 0);
if (lean_obj_tag(x_46) == 1)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_44);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
x_48 = lean_apply_2(x_3, x_38, x_47);
x_49 = l_Lean_mkNatLit(x_48);
x_50 = l_Lean_Meta_Grind_shareCommon___redArg(x_49, x_8);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_51);
x_53 = lean_grind_internalize(x_51, x_40, x_52, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
lean_dec_ref(x_53);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
lean_inc_ref(x_32);
x_54 = lean_grind_mk_eq_proof(x_32, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_7);
lean_inc(x_5);
lean_inc(x_43);
lean_inc_ref(x_41);
x_56 = lean_grind_mk_eq_proof(x_41, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_box(0);
x_59 = l_Lean_mkConst(x_2, x_58);
x_60 = l_Lean_Meta_Grind_propagateNatBinOp___closed__2;
lean_inc(x_51);
x_61 = l_Lean_mkApp8(x_59, x_32, x_41, x_34, x_43, x_51, x_55, x_57, x_60);
x_62 = 0;
x_63 = l_Lean_Meta_Grind_pushEqCore___redArg(x_4, x_51, x_61, x_62, x_5, x_7, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
lean_dec(x_5);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_55);
lean_dec(x_51);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_64 = !lean_is_exclusive(x_56);
if (x_64 == 0)
{
return x_56;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_56, 0);
lean_inc(x_65);
lean_dec(x_56);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_51);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_54);
if (x_67 == 0)
{
return x_54;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_54, 0);
lean_inc(x_68);
lean_dec(x_54);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
lean_dec(x_51);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_53;
}
}
else
{
uint8_t x_70; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_70 = !lean_is_exclusive(x_50);
if (x_70 == 0)
{
return x_50;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_50, 0);
lean_inc(x_71);
lean_dec(x_50);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; 
lean_dec(x_46);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_38);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_73 = lean_box(0);
lean_ctor_set(x_44, 0, x_73);
return x_44;
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_44, 0);
lean_inc(x_74);
lean_dec(x_44);
if (lean_obj_tag(x_74) == 1)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_apply_2(x_3, x_38, x_75);
x_77 = l_Lean_mkNatLit(x_76);
x_78 = l_Lean_Meta_Grind_shareCommon___redArg(x_77, x_8);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_79);
x_81 = lean_grind_internalize(x_79, x_40, x_80, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_dec_ref(x_81);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
lean_inc_ref(x_32);
x_82 = lean_grind_mk_eq_proof(x_32, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_7);
lean_inc(x_5);
lean_inc(x_43);
lean_inc_ref(x_41);
x_84 = lean_grind_mk_eq_proof(x_41, x_43, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_box(0);
x_87 = l_Lean_mkConst(x_2, x_86);
x_88 = l_Lean_Meta_Grind_propagateNatBinOp___closed__2;
lean_inc(x_79);
x_89 = l_Lean_mkApp8(x_87, x_32, x_41, x_34, x_43, x_79, x_83, x_85, x_88);
x_90 = 0;
x_91 = l_Lean_Meta_Grind_pushEqCore___redArg(x_4, x_79, x_89, x_90, x_5, x_7, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
lean_dec(x_5);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_83);
lean_dec(x_79);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_93 = x_84;
} else {
 lean_dec_ref(x_84);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 1, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_92);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_79);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_95 = lean_ctor_get(x_82, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_96 = x_82;
} else {
 lean_dec_ref(x_82);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_95);
return x_97;
}
}
else
{
lean_dec(x_79);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_81;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_98 = lean_ctor_get(x_78, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_99 = x_78;
} else {
 lean_dec_ref(x_78);
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
lean_object* x_101; lean_object* x_102; 
lean_dec(x_74);
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_38);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_43);
lean_dec_ref(x_41);
lean_dec(x_38);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_44);
if (x_103 == 0)
{
return x_44;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_44, 0);
lean_inc(x_104);
lean_dec(x_44);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec_ref(x_41);
lean_dec(x_38);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_106 = !lean_is_exclusive(x_42);
if (x_106 == 0)
{
return x_42;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_42, 0);
lean_inc(x_107);
lean_dec(x_42);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_109 = lean_box(0);
lean_ctor_set(x_35, 0, x_109);
return x_35;
}
}
else
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_35, 0);
lean_inc(x_110);
lean_dec(x_35);
if (lean_obj_tag(x_110) == 1)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_st_ref_get(x_5);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_Lean_Expr_getRevArg_x21(x_4, x_113);
lean_inc_ref(x_114);
x_115 = l_Lean_Meta_Grind_Goal_getRoot(x_112, x_114, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_117 = l_Lean_Meta_getNatValue_x3f(x_116, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_obj_tag(x_118) == 1)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_119);
x_120 = lean_ctor_get(x_118, 0);
lean_inc(x_120);
lean_dec_ref(x_118);
x_121 = lean_apply_2(x_3, x_111, x_120);
x_122 = l_Lean_mkNatLit(x_121);
x_123 = l_Lean_Meta_Grind_shareCommon___redArg(x_122, x_8);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = lean_box(0);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_124);
x_126 = lean_grind_internalize(x_124, x_113, x_125, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
lean_dec_ref(x_126);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
lean_inc_ref(x_32);
x_127 = lean_grind_mk_eq_proof(x_32, x_34, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_7);
lean_inc(x_5);
lean_inc(x_116);
lean_inc_ref(x_114);
x_129 = lean_grind_mk_eq_proof(x_114, x_116, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; uint8_t x_135; lean_object* x_136; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = lean_box(0);
x_132 = l_Lean_mkConst(x_2, x_131);
x_133 = l_Lean_Meta_Grind_propagateNatBinOp___closed__2;
lean_inc(x_124);
x_134 = l_Lean_mkApp8(x_132, x_32, x_114, x_34, x_116, x_124, x_128, x_130, x_133);
x_135 = 0;
x_136 = l_Lean_Meta_Grind_pushEqCore___redArg(x_4, x_124, x_134, x_135, x_5, x_7, x_9, x_10, x_11, x_12);
lean_dec_ref(x_7);
lean_dec(x_5);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_128);
lean_dec(x_124);
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_137 = lean_ctor_get(x_129, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_138 = x_129;
} else {
 lean_dec_ref(x_129);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 1, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_137);
return x_139;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_124);
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_140 = lean_ctor_get(x_127, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_141 = x_127;
} else {
 lean_dec_ref(x_127);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 1, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
return x_142;
}
}
else
{
lean_dec(x_124);
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_126;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_143 = lean_ctor_get(x_123, 0);
lean_inc(x_143);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 x_144 = x_123;
} else {
 lean_dec_ref(x_123);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_143);
return x_145;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_118);
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_111);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_146 = lean_box(0);
if (lean_is_scalar(x_119)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_119;
}
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_116);
lean_dec_ref(x_114);
lean_dec(x_111);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_117, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 x_149 = x_117;
} else {
 lean_dec_ref(x_117);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_114);
lean_dec(x_111);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_151 = lean_ctor_get(x_115, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 x_152 = x_115;
} else {
 lean_dec_ref(x_115);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_110);
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_155, 0, x_154);
return x_155;
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_34);
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_156 = !lean_is_exclusive(x_35);
if (x_156 == 0)
{
return x_35;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_35, 0);
lean_inc(x_157);
lean_dec(x_35);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec_ref(x_32);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_159 = !lean_is_exclusive(x_33);
if (x_159 == 0)
{
return x_33;
}
else
{
lean_object* x_160; lean_object* x_161; 
x_160 = lean_ctor_get(x_33, 0);
lean_inc(x_160);
lean_dec(x_33);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
return x_161;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatBinOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Meta_Grind_propagateNatBinOp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatAnd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_land___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatAnd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAnd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatAnd___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAnd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatAnd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_propagateNatAnd___closed__2;
x_2 = l_Lean_Meta_Grind_propagateNatAnd___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatAnd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatAnd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatAnd___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("and_congr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatAnd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_propagateNatAnd___closed__6;
x_2 = l_Lean_Meta_Grind_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatAnd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_propagateNatAnd___closed__0;
x_12 = l_Lean_Meta_Grind_propagateNatAnd___closed__3;
x_13 = l_Lean_Meta_Grind_propagateNatAnd___closed__7;
x_14 = l_Lean_Meta_Grind_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatAnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateNatAnd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatAnd___regBuiltin_Lean_Meta_Grind_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_propagateNatAnd___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNatAnd___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatAnd___regBuiltin_Lean_Meta_Grind_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateNatAnd___regBuiltin_Lean_Meta_Grind_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatOr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_lor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatOr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HOr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatOr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hOr", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatOr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_propagateNatOr___closed__2;
x_2 = l_Lean_Meta_Grind_propagateNatOr___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatOr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("or_congr", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatOr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_propagateNatOr___closed__4;
x_2 = l_Lean_Meta_Grind_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatOr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_propagateNatOr___closed__0;
x_12 = l_Lean_Meta_Grind_propagateNatOr___closed__3;
x_13 = l_Lean_Meta_Grind_propagateNatOr___closed__5;
x_14 = l_Lean_Meta_Grind_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateNatOr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatOr___regBuiltin_Lean_Meta_Grind_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_propagateNatOr___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNatOr___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatOr___regBuiltin_Lean_Meta_Grind_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateNatOr___regBuiltin_Lean_Meta_Grind_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatXOr___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_xor___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatXOr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HXor", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatXOr___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hXor", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatXOr___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_propagateNatXOr___closed__2;
x_2 = l_Lean_Meta_Grind_propagateNatXOr___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatXOr___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("xor_congr", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatXOr___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_propagateNatXOr___closed__4;
x_2 = l_Lean_Meta_Grind_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatXOr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_propagateNatXOr___closed__0;
x_12 = l_Lean_Meta_Grind_propagateNatXOr___closed__3;
x_13 = l_Lean_Meta_Grind_propagateNatXOr___closed__5;
x_14 = l_Lean_Meta_Grind_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatXOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateNatXOr(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatXOr___regBuiltin_Lean_Meta_Grind_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_propagateNatXOr___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNatXOr___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatXOr___regBuiltin_Lean_Meta_Grind_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateNatXOr___regBuiltin_Lean_Meta_Grind_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_shiftLeft___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HShiftLeft", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hShiftLeft", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_propagateNatShiftLeft___closed__2;
x_2 = l_Lean_Meta_Grind_propagateNatShiftLeft___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shiftLeft_congr", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_propagateNatShiftLeft___closed__4;
x_2 = l_Lean_Meta_Grind_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_propagateNatShiftLeft___closed__0;
x_12 = l_Lean_Meta_Grind_propagateNatShiftLeft___closed__3;
x_13 = l_Lean_Meta_Grind_propagateNatShiftLeft___closed__5;
x_14 = l_Lean_Meta_Grind_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateNatShiftLeft(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_propagateNatShiftLeft___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNatShiftLeft___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_shiftRight___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HShiftRight", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hShiftRight", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_propagateNatShiftRight___closed__2;
x_2 = l_Lean_Meta_Grind_propagateNatShiftRight___closed__1;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("shiftRight_congr", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_propagateNatShiftRight___closed__4;
x_2 = l_Lean_Meta_Grind_propagateNatBinOp___closed__0;
x_3 = l_Lean_Meta_Grind_propagateNatAnd___closed__5;
x_4 = l_Lean_Meta_Grind_propagateNatAnd___closed__4;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftRight(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Meta_Grind_propagateNatShiftRight___closed__0;
x_12 = l_Lean_Meta_Grind_propagateNatShiftRight___closed__3;
x_13 = l_Lean_Meta_Grind_propagateNatShiftRight___closed__5;
x_14 = l_Lean_Meta_Grind_propagateNatBinOp(x_12, x_13, x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateNatShiftRight(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_propagateNatShiftRight___closed__3;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateNatShiftRight___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinUpwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Propagate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_propagateNatBinOp___closed__0 = _init_l_Lean_Meta_Grind_propagateNatBinOp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatBinOp___closed__0);
l_Lean_Meta_Grind_propagateNatBinOp___closed__1 = _init_l_Lean_Meta_Grind_propagateNatBinOp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatBinOp___closed__1);
l_Lean_Meta_Grind_propagateNatBinOp___closed__2 = _init_l_Lean_Meta_Grind_propagateNatBinOp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatBinOp___closed__2);
l_Lean_Meta_Grind_propagateNatAnd___closed__0 = _init_l_Lean_Meta_Grind_propagateNatAnd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatAnd___closed__0);
l_Lean_Meta_Grind_propagateNatAnd___closed__1 = _init_l_Lean_Meta_Grind_propagateNatAnd___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatAnd___closed__1);
l_Lean_Meta_Grind_propagateNatAnd___closed__2 = _init_l_Lean_Meta_Grind_propagateNatAnd___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatAnd___closed__2);
l_Lean_Meta_Grind_propagateNatAnd___closed__3 = _init_l_Lean_Meta_Grind_propagateNatAnd___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatAnd___closed__3);
l_Lean_Meta_Grind_propagateNatAnd___closed__4 = _init_l_Lean_Meta_Grind_propagateNatAnd___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatAnd___closed__4);
l_Lean_Meta_Grind_propagateNatAnd___closed__5 = _init_l_Lean_Meta_Grind_propagateNatAnd___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatAnd___closed__5);
l_Lean_Meta_Grind_propagateNatAnd___closed__6 = _init_l_Lean_Meta_Grind_propagateNatAnd___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatAnd___closed__6);
l_Lean_Meta_Grind_propagateNatAnd___closed__7 = _init_l_Lean_Meta_Grind_propagateNatAnd___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatAnd___closed__7);
if (builtin) {res = l_Lean_Meta_Grind_propagateNatAnd___regBuiltin_Lean_Meta_Grind_propagateNatAnd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1291761156____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateNatOr___closed__0 = _init_l_Lean_Meta_Grind_propagateNatOr___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatOr___closed__0);
l_Lean_Meta_Grind_propagateNatOr___closed__1 = _init_l_Lean_Meta_Grind_propagateNatOr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatOr___closed__1);
l_Lean_Meta_Grind_propagateNatOr___closed__2 = _init_l_Lean_Meta_Grind_propagateNatOr___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatOr___closed__2);
l_Lean_Meta_Grind_propagateNatOr___closed__3 = _init_l_Lean_Meta_Grind_propagateNatOr___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatOr___closed__3);
l_Lean_Meta_Grind_propagateNatOr___closed__4 = _init_l_Lean_Meta_Grind_propagateNatOr___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatOr___closed__4);
l_Lean_Meta_Grind_propagateNatOr___closed__5 = _init_l_Lean_Meta_Grind_propagateNatOr___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatOr___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_propagateNatOr___regBuiltin_Lean_Meta_Grind_propagateNatOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_2834229635____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateNatXOr___closed__0 = _init_l_Lean_Meta_Grind_propagateNatXOr___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatXOr___closed__0);
l_Lean_Meta_Grind_propagateNatXOr___closed__1 = _init_l_Lean_Meta_Grind_propagateNatXOr___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatXOr___closed__1);
l_Lean_Meta_Grind_propagateNatXOr___closed__2 = _init_l_Lean_Meta_Grind_propagateNatXOr___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatXOr___closed__2);
l_Lean_Meta_Grind_propagateNatXOr___closed__3 = _init_l_Lean_Meta_Grind_propagateNatXOr___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatXOr___closed__3);
l_Lean_Meta_Grind_propagateNatXOr___closed__4 = _init_l_Lean_Meta_Grind_propagateNatXOr___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatXOr___closed__4);
l_Lean_Meta_Grind_propagateNatXOr___closed__5 = _init_l_Lean_Meta_Grind_propagateNatXOr___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatXOr___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_propagateNatXOr___regBuiltin_Lean_Meta_Grind_propagateNatXOr_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3633575148____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateNatShiftLeft___closed__0 = _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftLeft___closed__0);
l_Lean_Meta_Grind_propagateNatShiftLeft___closed__1 = _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftLeft___closed__1);
l_Lean_Meta_Grind_propagateNatShiftLeft___closed__2 = _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftLeft___closed__2);
l_Lean_Meta_Grind_propagateNatShiftLeft___closed__3 = _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftLeft___closed__3);
l_Lean_Meta_Grind_propagateNatShiftLeft___closed__4 = _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftLeft___closed__4);
l_Lean_Meta_Grind_propagateNatShiftLeft___closed__5 = _init_l_Lean_Meta_Grind_propagateNatShiftLeft___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftLeft___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_propagateNatShiftLeft___regBuiltin_Lean_Meta_Grind_propagateNatShiftLeft_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_3253038636____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_propagateNatShiftRight___closed__0 = _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftRight___closed__0);
l_Lean_Meta_Grind_propagateNatShiftRight___closed__1 = _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftRight___closed__1);
l_Lean_Meta_Grind_propagateNatShiftRight___closed__2 = _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftRight___closed__2);
l_Lean_Meta_Grind_propagateNatShiftRight___closed__3 = _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftRight___closed__3);
l_Lean_Meta_Grind_propagateNatShiftRight___closed__4 = _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftRight___closed__4);
l_Lean_Meta_Grind_propagateNatShiftRight___closed__5 = _init_l_Lean_Meta_Grind_propagateNatShiftRight___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateNatShiftRight___closed__5);
if (builtin) {res = l_Lean_Meta_Grind_propagateNatShiftRight___regBuiltin_Lean_Meta_Grind_propagateNatShiftRight_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Propagate_1805815810____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
