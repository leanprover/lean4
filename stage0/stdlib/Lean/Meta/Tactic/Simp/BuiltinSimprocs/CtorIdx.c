// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.CtorIdx
// Imports: public import Lean.Meta.Tactic.Simp.Simproc import Init.Simproc import Lean.Meta.Constructions.CtorIdx import Lean.Meta.CtorRecognizer
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
LEAN_EXPORT lean_object* l_reduceCtorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
lean_object* l_Array_back_x21___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
static lean_object* l_reduceCtorIdx___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9____boxed(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_reduceCtorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
lean_object* l_isCtorIdx_x3f___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_2);
x_12 = lean_array_set(x_3, x_4, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_2 = x_10;
x_3 = x_12;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = l_Lean_Expr_constName_x3f(x_2);
lean_dec_ref(x_2);
if (lean_obj_tag(x_16) == 1)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l_isCtorIdx_x3f___redArg(x_17, x_8);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 1)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 2);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_3);
x_25 = lean_nat_add(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_25, x_26);
lean_dec(x_25);
x_28 = lean_nat_dec_eq(x_24, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_29 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_free_object(x_18);
x_30 = l_Array_back_x21___redArg(x_1, x_3);
lean_dec_ref(x_3);
x_31 = l_Lean_Meta_isConstructorApp_x3f(x_30, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_33) == 1)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_35, 2);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_mkNatLit(x_36);
lean_ctor_set_tag(x_33, 0);
lean_ctor_set(x_33, 0, x_37);
return x_31;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_mkNatLit(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_31, 0, x_41);
return x_31;
}
}
else
{
lean_object* x_42; 
lean_dec(x_33);
x_42 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
lean_ctor_set(x_31, 0, x_42);
return x_31;
}
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_31, 0);
lean_inc(x_43);
lean_dec(x_31);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_44, 2);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_mkNatLit(x_46);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 1, 0);
} else {
 x_48 = x_45;
 lean_ctor_set_tag(x_48, 0);
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_43);
x_50 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_31);
if (x_52 == 0)
{
return x_31;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_31, 0);
lean_inc(x_53);
lean_dec(x_31);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_20);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_55 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
lean_ctor_set(x_18, 0, x_55);
return x_18;
}
}
else
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_18, 0);
lean_inc(x_56);
lean_dec(x_18);
if (lean_obj_tag(x_56) == 1)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec_ref(x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 2);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_array_get_size(x_3);
x_61 = lean_nat_add(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_61, x_62);
lean_dec(x_61);
x_64 = lean_nat_dec_eq(x_60, x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_65 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Array_back_x21___redArg(x_1, x_3);
lean_dec_ref(x_3);
x_68 = l_Lean_Meta_isConstructorApp_x3f(x_67, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
if (lean_obj_tag(x_69) == 1)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_71, 2);
lean_inc(x_73);
lean_dec(x_71);
x_74 = l_Lean_mkNatLit(x_73);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(0, 1, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 0);
}
lean_ctor_set(x_75, 0, x_74);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 1, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_69);
x_77 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
if (lean_is_scalar(x_70)) {
 x_78 = lean_alloc_ctor(0, 1, 0);
} else {
 x_78 = x_70;
}
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_68, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_80 = x_68;
} else {
 lean_dec_ref(x_68);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_82 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_84 = !lean_is_exclusive(x_18);
if (x_84 == 0)
{
return x_18;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_18, 0);
lean_inc(x_85);
lean_dec(x_18);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_87 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0;
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_reduceCtorIdx___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_reduceCtorIdx(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = l_Lean_instInhabitedExpr;
x_11 = l_reduceCtorIdx___closed__0;
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_12);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_12, x_14);
lean_dec(x_12);
x_16 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(x_10, x_1, x_13, x_15, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_reduceCtorIdx___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_reduceCtorIdx(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("reduceCtorIdx", 13, 13);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
x_3 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_;
x_4 = lean_alloc_closure((void*)(l_reduceCtorIdx___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinDSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Constructions_CtorIdx(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0 = _init_l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_Expr_withAppAux___at___00reduceCtorIdx_spec__0___redArg___closed__0);
l_reduceCtorIdx___closed__0 = _init_l_reduceCtorIdx___closed__0();
lean_mark_persistent(l_reduceCtorIdx___closed__0);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__0_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__1_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__2_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_);
l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_ = _init_l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5___closed__3_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_0____regBuiltin_reduceCtorIdx_declare__5_00___x40_Lean_Meta_Tactic_Simp_BuiltinSimprocs_CtorIdx_4044519369____hygCtx___hyg_9_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
