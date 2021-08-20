// Lean compiler output
// Module: Lean.Meta.ReduceEval
// Imports: Init Lean.Meta.Offset
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
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__10;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_instReduceEvalOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3;
lean_object* l_Lean_Meta_reduceEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7;
lean_object* l_Lean_Meta_instReduceEvalNat_match__1(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReduceEvalOption___rarg___closed__6;
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__1;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instReduceEvalString_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReduceEvalOption___rarg___closed__3;
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__3;
static lean_object* l_Lean_Meta_instReduceEvalName___closed__1;
lean_object* l_Lean_Meta_instReduceEvalNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instReduceEvalOption___rarg___closed__5;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6;
lean_object* l_Lean_Meta_instReduceEvalString_match__1(lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4;
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__8;
lean_object* l_Lean_Meta_instReduceEvalOption(lean_object*);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2;
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object*);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__9;
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1;
lean_object* l_Lean_Meta_instReduceEvalOption___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instReduceEvalString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__4;
static lean_object* l_Lean_Meta_instReduceEvalOption___rarg___closed__2;
static lean_object* l_Lean_Meta_instReduceEvalOption___rarg___closed__1;
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__2;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_reduceEval(lean_object*);
static lean_object* l_Lean_Meta_instReduceEvalOption___rarg___closed__4;
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_throwError___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___spec__1(lean_object*);
lean_object* l_Lean_Meta_instReduceEvalOption_match__1(lean_object*);
lean_object* l_Lean_Meta_instReduceEvalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instReduceEvalName;
lean_object* l_Lean_Meta_reduceEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get_uint8(x_9, 5);
x_12 = 1;
x_13 = l_Lean_Meta_TransparencyMode_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_ctor_set_uint8(x_9, 5, x_12);
x_23 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
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
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
uint8_t x_28; 
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
}
else
{
uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; 
x_32 = lean_ctor_get_uint8(x_9, 0);
x_33 = lean_ctor_get_uint8(x_9, 1);
x_34 = lean_ctor_get_uint8(x_9, 2);
x_35 = lean_ctor_get_uint8(x_9, 3);
x_36 = lean_ctor_get_uint8(x_9, 4);
x_37 = lean_ctor_get_uint8(x_9, 5);
x_38 = lean_ctor_get_uint8(x_9, 6);
x_39 = lean_ctor_get_uint8(x_9, 7);
x_40 = lean_ctor_get_uint8(x_9, 8);
x_41 = lean_ctor_get_uint8(x_9, 9);
x_42 = lean_ctor_get_uint8(x_9, 10);
x_43 = lean_ctor_get_uint8(x_9, 11);
lean_dec(x_9);
x_44 = 1;
x_45 = l_Lean_Meta_TransparencyMode_lt(x_37, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_46, 0, x_32);
lean_ctor_set_uint8(x_46, 1, x_33);
lean_ctor_set_uint8(x_46, 2, x_34);
lean_ctor_set_uint8(x_46, 3, x_35);
lean_ctor_set_uint8(x_46, 4, x_36);
lean_ctor_set_uint8(x_46, 5, x_37);
lean_ctor_set_uint8(x_46, 6, x_38);
lean_ctor_set_uint8(x_46, 7, x_39);
lean_ctor_set_uint8(x_46, 8, x_40);
lean_ctor_set_uint8(x_46, 9, x_41);
lean_ctor_set_uint8(x_46, 10, x_42);
lean_ctor_set_uint8(x_46, 11, x_43);
lean_ctor_set(x_3, 0, x_46);
x_47 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
if (lean_is_scalar(x_50)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_50;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_54 = x_47;
} else {
 lean_dec_ref(x_47);
 x_54 = lean_box(0);
}
if (lean_is_scalar(x_54)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_54;
}
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_56, 0, x_32);
lean_ctor_set_uint8(x_56, 1, x_33);
lean_ctor_set_uint8(x_56, 2, x_34);
lean_ctor_set_uint8(x_56, 3, x_35);
lean_ctor_set_uint8(x_56, 4, x_36);
lean_ctor_set_uint8(x_56, 5, x_44);
lean_ctor_set_uint8(x_56, 6, x_38);
lean_ctor_set_uint8(x_56, 7, x_39);
lean_ctor_set_uint8(x_56, 8, x_40);
lean_ctor_set_uint8(x_56, 9, x_41);
lean_ctor_set_uint8(x_56, 10, x_42);
lean_ctor_set_uint8(x_56, 11, x_43);
lean_ctor_set(x_3, 0, x_56);
x_57 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_60 = x_57;
} else {
 lean_dec_ref(x_57);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_64 = x_57;
} else {
 lean_dec_ref(x_57);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
x_68 = lean_ctor_get(x_3, 2);
x_69 = lean_ctor_get(x_3, 3);
x_70 = lean_ctor_get(x_3, 4);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
x_71 = lean_ctor_get_uint8(x_66, 0);
x_72 = lean_ctor_get_uint8(x_66, 1);
x_73 = lean_ctor_get_uint8(x_66, 2);
x_74 = lean_ctor_get_uint8(x_66, 3);
x_75 = lean_ctor_get_uint8(x_66, 4);
x_76 = lean_ctor_get_uint8(x_66, 5);
x_77 = lean_ctor_get_uint8(x_66, 6);
x_78 = lean_ctor_get_uint8(x_66, 7);
x_79 = lean_ctor_get_uint8(x_66, 8);
x_80 = lean_ctor_get_uint8(x_66, 9);
x_81 = lean_ctor_get_uint8(x_66, 10);
x_82 = lean_ctor_get_uint8(x_66, 11);
if (lean_is_exclusive(x_66)) {
 x_83 = x_66;
} else {
 lean_dec_ref(x_66);
 x_83 = lean_box(0);
}
x_84 = 1;
x_85 = l_Lean_Meta_TransparencyMode_lt(x_76, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_scalar(x_83)) {
 x_86 = lean_alloc_ctor(0, 0, 12);
} else {
 x_86 = x_83;
}
lean_ctor_set_uint8(x_86, 0, x_71);
lean_ctor_set_uint8(x_86, 1, x_72);
lean_ctor_set_uint8(x_86, 2, x_73);
lean_ctor_set_uint8(x_86, 3, x_74);
lean_ctor_set_uint8(x_86, 4, x_75);
lean_ctor_set_uint8(x_86, 5, x_76);
lean_ctor_set_uint8(x_86, 6, x_77);
lean_ctor_set_uint8(x_86, 7, x_78);
lean_ctor_set_uint8(x_86, 8, x_79);
lean_ctor_set_uint8(x_86, 9, x_80);
lean_ctor_set_uint8(x_86, 10, x_81);
lean_ctor_set_uint8(x_86, 11, x_82);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_67);
lean_ctor_set(x_87, 2, x_68);
lean_ctor_set(x_87, 3, x_69);
lean_ctor_set(x_87, 4, x_70);
x_88 = lean_apply_6(x_1, x_2, x_87, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_95 = x_88;
} else {
 lean_dec_ref(x_88);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
if (lean_is_scalar(x_83)) {
 x_97 = lean_alloc_ctor(0, 0, 12);
} else {
 x_97 = x_83;
}
lean_ctor_set_uint8(x_97, 0, x_71);
lean_ctor_set_uint8(x_97, 1, x_72);
lean_ctor_set_uint8(x_97, 2, x_73);
lean_ctor_set_uint8(x_97, 3, x_74);
lean_ctor_set_uint8(x_97, 4, x_75);
lean_ctor_set_uint8(x_97, 5, x_84);
lean_ctor_set_uint8(x_97, 6, x_77);
lean_ctor_set_uint8(x_97, 7, x_78);
lean_ctor_set_uint8(x_97, 8, x_79);
lean_ctor_set_uint8(x_97, 9, x_80);
lean_ctor_set_uint8(x_97, 10, x_81);
lean_ctor_set_uint8(x_97, 11, x_82);
x_98 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_67);
lean_ctor_set(x_98, 2, x_68);
lean_ctor_set(x_98, 3, x_69);
lean_ctor_set(x_98, 4, x_70);
x_99 = lean_apply_6(x_1, x_2, x_98, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_106 = x_99;
} else {
 lean_dec_ref(x_99);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
}
lean_object* l_Lean_Meta_reduceEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceEval___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 3);
x_8 = l_Lean_addMessageContextFull___at_Lean_Meta_instAddMessageContextMetaM___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_throwError___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___spec__1___rarg___boxed), 6, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceEval: failed to evaluate argument");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = l_Lean_indentExpr(x_1);
x_8 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__2;
x_9 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__4;
x_11 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_throwError___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___spec__1___rarg(x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_throwError___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
lean_object* l_Lean_Meta_instReduceEvalNat_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_instReduceEvalNat_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalNat_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instReduceEvalNat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_8);
x_10 = l_Lean_Meta_evalNat(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_8, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_10, 0);
lean_dec(x_15);
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
lean_ctor_set(x_10, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_dec(x_10);
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
return x_7;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* l_Lean_Meta_instReduceEvalOption_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Meta_instReduceEvalOption_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption_match__1___rarg), 3, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Option");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instReduceEvalOption___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("none");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instReduceEvalOption___rarg___closed__2;
x_2 = l_Lean_Meta_instReduceEvalOption___rarg___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("some");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_instReduceEvalOption___rarg___closed__2;
x_2 = l_Lean_Meta_instReduceEvalOption___rarg___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_instReduceEvalOption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = lean_whnf(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_getAppFn(x_10);
if (lean_obj_tag(x_12) == 4)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Lean_Expr_getAppNumArgsAux(x_10, x_14);
x_16 = l_Lean_Meta_instReduceEvalOption___rarg___closed__4;
x_17 = lean_name_eq(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_free_object(x_8);
x_18 = l_Lean_Meta_instReduceEvalOption___rarg___closed__6;
x_19 = lean_name_eq(x_13, x_18);
lean_dec(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_10, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_eq(x_15, x_21);
lean_dec(x_15);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_10, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_25 = l_Lean_Meta_reduceEval___rarg(x_1, x_24, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_eq(x_15, x_14);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_free_object(x_8);
x_38 = l_Lean_Meta_instReduceEvalOption___rarg___closed__6;
x_39 = lean_name_eq(x_13, x_38);
lean_dec(x_13);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_15);
lean_dec(x_1);
x_40 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_10, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_dec_eq(x_15, x_41);
lean_dec(x_15);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_1);
x_43 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_10, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = l_Lean_Expr_appArg_x21(x_10);
lean_dec(x_10);
x_45 = l_Lean_Meta_reduceEval___rarg(x_1, x_44, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_45, 0, x_48);
return x_45;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_45, 0);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_45);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_45);
if (x_53 == 0)
{
return x_45;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_45, 0);
x_55 = lean_ctor_get(x_45, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_8, 0, x_57);
return x_8;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_12);
lean_free_object(x_8);
lean_dec(x_1);
x_58 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_10, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_8, 0);
x_60 = lean_ctor_get(x_8, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_8);
x_61 = l_Lean_Expr_getAppFn(x_59);
if (lean_obj_tag(x_61) == 4)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Lean_Expr_getAppNumArgsAux(x_59, x_63);
x_65 = l_Lean_Meta_instReduceEvalOption___rarg___closed__4;
x_66 = lean_name_eq(x_62, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = l_Lean_Meta_instReduceEvalOption___rarg___closed__6;
x_68 = lean_name_eq(x_62, x_67);
lean_dec(x_62);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_64);
lean_dec(x_1);
x_69 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_59, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_69;
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_dec_eq(x_64, x_70);
lean_dec(x_64);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_1);
x_72 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_59, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = l_Lean_Expr_appArg_x21(x_59);
lean_dec(x_59);
x_74 = l_Lean_Meta_reduceEval___rarg(x_1, x_73, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_77 = x_74;
} else {
 lean_dec_ref(x_74);
 x_77 = lean_box(0);
}
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_75);
if (lean_is_scalar(x_77)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_77;
}
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_76);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_74, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_82 = x_74;
} else {
 lean_dec_ref(x_74);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
else
{
uint8_t x_84; 
x_84 = lean_nat_dec_eq(x_64, x_63);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = l_Lean_Meta_instReduceEvalOption___rarg___closed__6;
x_86 = lean_name_eq(x_62, x_85);
lean_dec(x_62);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_64);
lean_dec(x_1);
x_87 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_59, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_87;
}
else
{
lean_object* x_88; uint8_t x_89; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_dec_eq(x_64, x_88);
lean_dec(x_64);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_1);
x_90 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_59, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = l_Lean_Expr_appArg_x21(x_59);
lean_dec(x_59);
x_92 = l_Lean_Meta_reduceEval___rarg(x_1, x_91, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_93);
if (lean_is_scalar(x_95)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_95;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_94);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_100 = x_92;
} else {
 lean_dec_ref(x_92);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_64);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_60);
return x_103;
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_61);
lean_dec(x_1);
x_104 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_59, x_3, x_4, x_5, x_6, x_60);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_8);
if (x_105 == 0)
{
return x_8;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_8, 0);
x_107 = lean_ctor_get(x_8, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_8);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
lean_object* l_Lean_Meta_instReduceEvalOption(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalOption___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instReduceEvalString_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_3, x_1);
return x_5;
}
else
{
uint64_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_box_uint64(x_6);
x_9 = lean_apply_2(x_2, x_7, x_8);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = lean_apply_1(x_3, x_1);
return x_10;
}
}
}
lean_object* l_Lean_Meta_instReduceEvalString_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instReduceEvalString_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_instReduceEvalString(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 9)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
lean_dec(x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_7, 0);
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_7);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_2);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_ctor_get_uint8(x_8, 5);
x_11 = 1;
x_12 = l_Lean_Meta_TransparencyMode_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_14);
x_16 = l_Lean_Meta_evalNat(x_14, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_14, x_2, x_3, x_4, x_5, x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
return x_19;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_19);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_16, 0);
lean_dec(x_25);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_26);
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_ctor_get(x_17, 0);
lean_inc(x_28);
lean_dec(x_17);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_14);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; 
lean_ctor_set_uint8(x_8, 5, x_11);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_38 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_39);
x_41 = l_Lean_Meta_evalNat(x_39, x_2, x_3, x_4, x_5, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_39, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_39);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_41, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_42, 0);
lean_inc(x_51);
lean_dec(x_42);
lean_ctor_set(x_41, 0, x_51);
return x_41;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_dec(x_41);
x_53 = lean_ctor_get(x_42, 0);
lean_inc(x_53);
lean_dec(x_42);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_39);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_41);
if (x_55 == 0)
{
return x_41;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_41, 0);
x_57 = lean_ctor_get(x_41, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_41);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_59 = !lean_is_exclusive(x_38);
if (x_59 == 0)
{
return x_38;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_38, 0);
x_61 = lean_ctor_get(x_38, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_38);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
else
{
uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; 
x_63 = lean_ctor_get_uint8(x_8, 0);
x_64 = lean_ctor_get_uint8(x_8, 1);
x_65 = lean_ctor_get_uint8(x_8, 2);
x_66 = lean_ctor_get_uint8(x_8, 3);
x_67 = lean_ctor_get_uint8(x_8, 4);
x_68 = lean_ctor_get_uint8(x_8, 5);
x_69 = lean_ctor_get_uint8(x_8, 6);
x_70 = lean_ctor_get_uint8(x_8, 7);
x_71 = lean_ctor_get_uint8(x_8, 8);
x_72 = lean_ctor_get_uint8(x_8, 9);
x_73 = lean_ctor_get_uint8(x_8, 10);
x_74 = lean_ctor_get_uint8(x_8, 11);
lean_dec(x_8);
x_75 = 1;
x_76 = l_Lean_Meta_TransparencyMode_lt(x_68, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_77, 0, x_63);
lean_ctor_set_uint8(x_77, 1, x_64);
lean_ctor_set_uint8(x_77, 2, x_65);
lean_ctor_set_uint8(x_77, 3, x_66);
lean_ctor_set_uint8(x_77, 4, x_67);
lean_ctor_set_uint8(x_77, 5, x_68);
lean_ctor_set_uint8(x_77, 6, x_69);
lean_ctor_set_uint8(x_77, 7, x_70);
lean_ctor_set_uint8(x_77, 8, x_71);
lean_ctor_set_uint8(x_77, 9, x_72);
lean_ctor_set_uint8(x_77, 10, x_73);
lean_ctor_set_uint8(x_77, 11, x_74);
lean_ctor_set(x_2, 0, x_77);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_78 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_79);
x_81 = l_Lean_Meta_evalNat(x_79, x_2, x_3, x_4, x_5, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_79, x_2, x_3, x_4, x_5, x_83);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = lean_ctor_get(x_81, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_90 = x_81;
} else {
 lean_dec_ref(x_81);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_82, 0);
lean_inc(x_91);
lean_dec(x_82);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_79);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = lean_ctor_get(x_81, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_81, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_95 = x_81;
} else {
 lean_dec_ref(x_81);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_97 = lean_ctor_get(x_78, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_78, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_99 = x_78;
} else {
 lean_dec_ref(x_78);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 2, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_101, 0, x_63);
lean_ctor_set_uint8(x_101, 1, x_64);
lean_ctor_set_uint8(x_101, 2, x_65);
lean_ctor_set_uint8(x_101, 3, x_66);
lean_ctor_set_uint8(x_101, 4, x_67);
lean_ctor_set_uint8(x_101, 5, x_75);
lean_ctor_set_uint8(x_101, 6, x_69);
lean_ctor_set_uint8(x_101, 7, x_70);
lean_ctor_set_uint8(x_101, 8, x_71);
lean_ctor_set_uint8(x_101, 9, x_72);
lean_ctor_set_uint8(x_101, 10, x_73);
lean_ctor_set_uint8(x_101, 11, x_74);
lean_ctor_set(x_2, 0, x_101);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_102 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_103);
x_105 = l_Lean_Meta_evalNat(x_103, x_2, x_3, x_4, x_5, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_103, x_2, x_3, x_4, x_5, x_107);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_103);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = lean_ctor_get(x_105, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_114 = x_105;
} else {
 lean_dec_ref(x_105);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_106, 0);
lean_inc(x_115);
lean_dec(x_106);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_113);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_103);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = lean_ctor_get(x_105, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_105, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_119 = x_105;
} else {
 lean_dec_ref(x_105);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_121 = lean_ctor_get(x_102, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_102, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_123 = x_102;
} else {
 lean_dec_ref(x_102);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; lean_object* x_142; uint8_t x_143; uint8_t x_144; 
x_125 = lean_ctor_get(x_2, 0);
x_126 = lean_ctor_get(x_2, 1);
x_127 = lean_ctor_get(x_2, 2);
x_128 = lean_ctor_get(x_2, 3);
x_129 = lean_ctor_get(x_2, 4);
lean_inc(x_129);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_2);
x_130 = lean_ctor_get_uint8(x_125, 0);
x_131 = lean_ctor_get_uint8(x_125, 1);
x_132 = lean_ctor_get_uint8(x_125, 2);
x_133 = lean_ctor_get_uint8(x_125, 3);
x_134 = lean_ctor_get_uint8(x_125, 4);
x_135 = lean_ctor_get_uint8(x_125, 5);
x_136 = lean_ctor_get_uint8(x_125, 6);
x_137 = lean_ctor_get_uint8(x_125, 7);
x_138 = lean_ctor_get_uint8(x_125, 8);
x_139 = lean_ctor_get_uint8(x_125, 9);
x_140 = lean_ctor_get_uint8(x_125, 10);
x_141 = lean_ctor_get_uint8(x_125, 11);
if (lean_is_exclusive(x_125)) {
 x_142 = x_125;
} else {
 lean_dec_ref(x_125);
 x_142 = lean_box(0);
}
x_143 = 1;
x_144 = l_Lean_Meta_TransparencyMode_lt(x_135, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(0, 0, 12);
} else {
 x_145 = x_142;
}
lean_ctor_set_uint8(x_145, 0, x_130);
lean_ctor_set_uint8(x_145, 1, x_131);
lean_ctor_set_uint8(x_145, 2, x_132);
lean_ctor_set_uint8(x_145, 3, x_133);
lean_ctor_set_uint8(x_145, 4, x_134);
lean_ctor_set_uint8(x_145, 5, x_135);
lean_ctor_set_uint8(x_145, 6, x_136);
lean_ctor_set_uint8(x_145, 7, x_137);
lean_ctor_set_uint8(x_145, 8, x_138);
lean_ctor_set_uint8(x_145, 9, x_139);
lean_ctor_set_uint8(x_145, 10, x_140);
lean_ctor_set_uint8(x_145, 11, x_141);
x_146 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_126);
lean_ctor_set(x_146, 2, x_127);
lean_ctor_set(x_146, 3, x_128);
lean_ctor_set(x_146, 4, x_129);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_146);
x_147 = lean_whnf(x_1, x_146, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_146);
lean_inc(x_148);
x_150 = l_Lean_Meta_evalNat(x_148, x_146, x_3, x_4, x_5, x_149);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_148, x_146, x_3, x_4, x_5, x_152);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_146);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_158 = lean_ctor_get(x_150, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_159 = x_150;
} else {
 lean_dec_ref(x_150);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_151, 0);
lean_inc(x_160);
lean_dec(x_151);
if (lean_is_scalar(x_159)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_159;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_158);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_162 = lean_ctor_get(x_150, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_150, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_164 = x_150;
} else {
 lean_dec_ref(x_150);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_146);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_166 = lean_ctor_get(x_147, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_147, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_168 = x_147;
} else {
 lean_dec_ref(x_147);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
if (lean_is_scalar(x_142)) {
 x_170 = lean_alloc_ctor(0, 0, 12);
} else {
 x_170 = x_142;
}
lean_ctor_set_uint8(x_170, 0, x_130);
lean_ctor_set_uint8(x_170, 1, x_131);
lean_ctor_set_uint8(x_170, 2, x_132);
lean_ctor_set_uint8(x_170, 3, x_133);
lean_ctor_set_uint8(x_170, 4, x_134);
lean_ctor_set_uint8(x_170, 5, x_143);
lean_ctor_set_uint8(x_170, 6, x_136);
lean_ctor_set_uint8(x_170, 7, x_137);
lean_ctor_set_uint8(x_170, 8, x_138);
lean_ctor_set_uint8(x_170, 9, x_139);
lean_ctor_set_uint8(x_170, 10, x_140);
lean_ctor_set_uint8(x_170, 11, x_141);
x_171 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_126);
lean_ctor_set(x_171, 2, x_127);
lean_ctor_set(x_171, 3, x_128);
lean_ctor_set(x_171, 4, x_129);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_171);
x_172 = lean_whnf(x_1, x_171, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 1);
lean_inc(x_174);
lean_dec(x_172);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_171);
lean_inc(x_173);
x_175 = l_Lean_Meta_evalNat(x_173, x_171, x_3, x_4, x_5, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_173, x_171, x_3, x_4, x_5, x_177);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_171);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_181 = x_178;
} else {
 lean_dec_ref(x_178);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = lean_ctor_get(x_175, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_184 = x_175;
} else {
 lean_dec_ref(x_175);
 x_184 = lean_box(0);
}
x_185 = lean_ctor_get(x_176, 0);
lean_inc(x_185);
lean_dec(x_176);
if (lean_is_scalar(x_184)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_184;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_183);
return x_186;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_187 = lean_ctor_get(x_175, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_175, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_189 = x_175;
} else {
 lean_dec_ref(x_175);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_171);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_191 = lean_ctor_get(x_172, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_172, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_193 = x_172;
} else {
 lean_dec_ref(x_172);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
}
}
}
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_17; 
x_17 = !lean_is_exclusive(x_2);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_2, 0);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_20 = lean_ctor_get_uint8(x_18, 5);
x_21 = 1;
x_22 = l_Lean_Meta_TransparencyMode_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_23 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 9)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_27;
goto block_16;
}
else
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_23);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
lean_ctor_set(x_23, 0, x_30);
x_7 = x_23;
goto block_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_25, 0);
lean_inc(x_32);
lean_dec(x_25);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_7 = x_33;
goto block_16;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_24);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
x_35 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_34);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_35;
goto block_16;
}
}
else
{
uint8_t x_36; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
x_7 = x_23;
goto block_16;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_7 = x_39;
goto block_16;
}
}
}
else
{
lean_object* x_40; 
lean_ctor_set_uint8(x_18, 5, x_21);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_40 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 9)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_43);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_44;
goto block_16;
}
else
{
uint8_t x_45; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_40);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_40, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_42, 0);
lean_inc(x_47);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_47);
x_7 = x_40;
goto block_16;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
x_7 = x_50;
goto block_16;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_dec(x_40);
x_52 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_52;
goto block_16;
}
}
else
{
uint8_t x_53; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_40);
if (x_53 == 0)
{
x_7 = x_40;
goto block_16;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_40, 0);
x_55 = lean_ctor_get(x_40, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_40);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_7 = x_56;
goto block_16;
}
}
}
}
else
{
uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; 
x_57 = lean_ctor_get_uint8(x_18, 0);
x_58 = lean_ctor_get_uint8(x_18, 1);
x_59 = lean_ctor_get_uint8(x_18, 2);
x_60 = lean_ctor_get_uint8(x_18, 3);
x_61 = lean_ctor_get_uint8(x_18, 4);
x_62 = lean_ctor_get_uint8(x_18, 5);
x_63 = lean_ctor_get_uint8(x_18, 6);
x_64 = lean_ctor_get_uint8(x_18, 7);
x_65 = lean_ctor_get_uint8(x_18, 8);
x_66 = lean_ctor_get_uint8(x_18, 9);
x_67 = lean_ctor_get_uint8(x_18, 10);
x_68 = lean_ctor_get_uint8(x_18, 11);
lean_dec(x_18);
x_69 = 1;
x_70 = l_Lean_Meta_TransparencyMode_lt(x_62, x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_71, 0, x_57);
lean_ctor_set_uint8(x_71, 1, x_58);
lean_ctor_set_uint8(x_71, 2, x_59);
lean_ctor_set_uint8(x_71, 3, x_60);
lean_ctor_set_uint8(x_71, 4, x_61);
lean_ctor_set_uint8(x_71, 5, x_62);
lean_ctor_set_uint8(x_71, 6, x_63);
lean_ctor_set_uint8(x_71, 7, x_64);
lean_ctor_set_uint8(x_71, 8, x_65);
lean_ctor_set_uint8(x_71, 9, x_66);
lean_ctor_set_uint8(x_71, 10, x_67);
lean_ctor_set_uint8(x_71, 11, x_68);
lean_ctor_set(x_2, 0, x_71);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_72 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 9)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_74);
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_76 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_75);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_76;
goto block_16;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_78 = x_72;
} else {
 lean_dec_ref(x_72);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_77);
x_7 = x_80;
goto block_16;
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_73);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec(x_72);
x_82 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_81);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_82;
goto block_16;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_83 = lean_ctor_get(x_72, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_85 = x_72;
} else {
 lean_dec_ref(x_72);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
x_7 = x_86;
goto block_16;
}
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_87, 0, x_57);
lean_ctor_set_uint8(x_87, 1, x_58);
lean_ctor_set_uint8(x_87, 2, x_59);
lean_ctor_set_uint8(x_87, 3, x_60);
lean_ctor_set_uint8(x_87, 4, x_61);
lean_ctor_set_uint8(x_87, 5, x_69);
lean_ctor_set_uint8(x_87, 6, x_63);
lean_ctor_set_uint8(x_87, 7, x_64);
lean_ctor_set_uint8(x_87, 8, x_65);
lean_ctor_set_uint8(x_87, 9, x_66);
lean_ctor_set_uint8(x_87, 10, x_67);
lean_ctor_set_uint8(x_87, 11, x_68);
lean_ctor_set(x_2, 0, x_87);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_88 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 9)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_90);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_dec(x_88);
x_92 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_92;
goto block_16;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_94 = x_88;
} else {
 lean_dec_ref(x_88);
 x_94 = lean_box(0);
}
x_95 = lean_ctor_get(x_90, 0);
lean_inc(x_95);
lean_dec(x_90);
if (lean_is_scalar(x_94)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_94;
}
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_93);
x_7 = x_96;
goto block_16;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_89);
x_97 = lean_ctor_get(x_88, 1);
lean_inc(x_97);
lean_dec(x_88);
x_98 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_2, x_3, x_4, x_5, x_97);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_98;
goto block_16;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_88, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_88, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_101 = x_88;
} else {
 lean_dec_ref(x_88);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
x_7 = x_102;
goto block_16;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; uint8_t x_121; uint8_t x_122; 
x_103 = lean_ctor_get(x_2, 0);
x_104 = lean_ctor_get(x_2, 1);
x_105 = lean_ctor_get(x_2, 2);
x_106 = lean_ctor_get(x_2, 3);
x_107 = lean_ctor_get(x_2, 4);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_2);
x_108 = lean_ctor_get_uint8(x_103, 0);
x_109 = lean_ctor_get_uint8(x_103, 1);
x_110 = lean_ctor_get_uint8(x_103, 2);
x_111 = lean_ctor_get_uint8(x_103, 3);
x_112 = lean_ctor_get_uint8(x_103, 4);
x_113 = lean_ctor_get_uint8(x_103, 5);
x_114 = lean_ctor_get_uint8(x_103, 6);
x_115 = lean_ctor_get_uint8(x_103, 7);
x_116 = lean_ctor_get_uint8(x_103, 8);
x_117 = lean_ctor_get_uint8(x_103, 9);
x_118 = lean_ctor_get_uint8(x_103, 10);
x_119 = lean_ctor_get_uint8(x_103, 11);
if (lean_is_exclusive(x_103)) {
 x_120 = x_103;
} else {
 lean_dec_ref(x_103);
 x_120 = lean_box(0);
}
x_121 = 1;
x_122 = l_Lean_Meta_TransparencyMode_lt(x_113, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
if (lean_is_scalar(x_120)) {
 x_123 = lean_alloc_ctor(0, 0, 12);
} else {
 x_123 = x_120;
}
lean_ctor_set_uint8(x_123, 0, x_108);
lean_ctor_set_uint8(x_123, 1, x_109);
lean_ctor_set_uint8(x_123, 2, x_110);
lean_ctor_set_uint8(x_123, 3, x_111);
lean_ctor_set_uint8(x_123, 4, x_112);
lean_ctor_set_uint8(x_123, 5, x_113);
lean_ctor_set_uint8(x_123, 6, x_114);
lean_ctor_set_uint8(x_123, 7, x_115);
lean_ctor_set_uint8(x_123, 8, x_116);
lean_ctor_set_uint8(x_123, 9, x_117);
lean_ctor_set_uint8(x_123, 10, x_118);
lean_ctor_set_uint8(x_123, 11, x_119);
x_124 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_104);
lean_ctor_set(x_124, 2, x_105);
lean_ctor_set(x_124, 3, x_106);
lean_ctor_set(x_124, 4, x_107);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_124);
lean_inc(x_1);
x_125 = lean_whnf(x_1, x_124, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
if (lean_obj_tag(x_126) == 9)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec(x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_124, x_3, x_4, x_5, x_128);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_124);
x_7 = x_129;
goto block_16;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_131 = x_125;
} else {
 lean_dec_ref(x_125);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_127, 0);
lean_inc(x_132);
lean_dec(x_127);
if (lean_is_scalar(x_131)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_131;
}
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_130);
x_7 = x_133;
goto block_16;
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_126);
x_134 = lean_ctor_get(x_125, 1);
lean_inc(x_134);
lean_dec(x_125);
x_135 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_124, x_3, x_4, x_5, x_134);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_124);
x_7 = x_135;
goto block_16;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_136 = lean_ctor_get(x_125, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_125, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_138 = x_125;
} else {
 lean_dec_ref(x_125);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
x_7 = x_139;
goto block_16;
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
if (lean_is_scalar(x_120)) {
 x_140 = lean_alloc_ctor(0, 0, 12);
} else {
 x_140 = x_120;
}
lean_ctor_set_uint8(x_140, 0, x_108);
lean_ctor_set_uint8(x_140, 1, x_109);
lean_ctor_set_uint8(x_140, 2, x_110);
lean_ctor_set_uint8(x_140, 3, x_111);
lean_ctor_set_uint8(x_140, 4, x_112);
lean_ctor_set_uint8(x_140, 5, x_121);
lean_ctor_set_uint8(x_140, 6, x_114);
lean_ctor_set_uint8(x_140, 7, x_115);
lean_ctor_set_uint8(x_140, 8, x_116);
lean_ctor_set_uint8(x_140, 9, x_117);
lean_ctor_set_uint8(x_140, 10, x_118);
lean_ctor_set_uint8(x_140, 11, x_119);
x_141 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_104);
lean_ctor_set(x_141, 2, x_105);
lean_ctor_set(x_141, 3, x_106);
lean_ctor_set(x_141, 4, x_107);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_141);
lean_inc(x_1);
x_142 = lean_whnf(x_1, x_141, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 9)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
lean_dec(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_144);
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_141, x_3, x_4, x_5, x_145);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_141);
x_7 = x_146;
goto block_16;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_141);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_148 = x_142;
} else {
 lean_dec_ref(x_142);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_144, 0);
lean_inc(x_149);
lean_dec(x_144);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
x_7 = x_150;
goto block_16;
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_143);
x_151 = lean_ctor_get(x_142, 1);
lean_inc(x_151);
lean_dec(x_142);
x_152 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_1, x_141, x_3, x_4, x_5, x_151);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_141);
x_7 = x_152;
goto block_16;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_141);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_ctor_get(x_142, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_142, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_155 = x_142;
} else {
 lean_dec_ref(x_142);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
x_7 = x_156;
goto block_16;
}
}
}
block_16:
{
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
return x_7;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Name");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2;
x_2 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("num");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4;
x_2 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("str");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4;
x_2 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("anonymous");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4;
x_2 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_whnf(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_getAppFn(x_9);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_49; lean_object* x_83; uint8_t x_84; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux(x_9, x_13);
x_83 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__10;
x_84 = lean_name_eq(x_12, x_83);
if (x_84 == 0)
{
lean_object* x_85; 
lean_free_object(x_7);
x_85 = lean_box(0);
x_49 = x_85;
goto block_82;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_eq(x_14, x_13);
if (x_86 == 0)
{
lean_object* x_87; 
lean_free_object(x_7);
x_87 = lean_box(0);
x_49 = x_87;
goto block_82;
}
else
{
lean_object* x_88; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = lean_box(0);
lean_ctor_set(x_7, 0, x_88);
return x_7;
}
}
block_48:
{
lean_object* x_16; uint8_t x_17; 
lean_dec(x_15);
x_16 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6;
x_17 = lean_name_eq(x_12, x_16);
lean_dec(x_12);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
x_18 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_9, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(3u);
x_20 = lean_nat_dec_eq(x_14, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
x_21 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_9, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_nat_sub(x_14, x_13);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_22, x_23);
lean_dec(x_22);
x_25 = l_Lean_Expr_getRevArg_x21(x_9, x_24);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_26 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_25, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_nat_sub(x_14, x_23);
lean_dec(x_14);
x_30 = lean_nat_sub(x_29, x_23);
lean_dec(x_29);
x_31 = l_Lean_Expr_getRevArg_x21(x_9, x_30);
lean_dec(x_9);
x_32 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__1(x_31, x_2, x_3, x_4, x_5, x_28);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_name_mk_numeral(x_27, x_34);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_name_mk_numeral(x_27, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_27);
x_40 = !lean_is_exclusive(x_32);
if (x_40 == 0)
{
return x_32;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_32, 0);
x_42 = lean_ctor_get(x_32, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_32);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_26);
if (x_44 == 0)
{
return x_26;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_26, 0);
x_46 = lean_ctor_get(x_26, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_26);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
block_82:
{
lean_object* x_50; uint8_t x_51; 
lean_dec(x_49);
x_50 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__8;
x_51 = lean_name_eq(x_12, x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_box(0);
x_15 = x_52;
goto block_48;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_dec_eq(x_14, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_box(0);
x_15 = x_55;
goto block_48;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_12);
x_56 = lean_nat_sub(x_14, x_13);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_56, x_57);
lean_dec(x_56);
x_59 = l_Lean_Expr_getRevArg_x21(x_9, x_58);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_60 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_59, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_nat_sub(x_14, x_57);
lean_dec(x_14);
x_64 = lean_nat_sub(x_63, x_57);
lean_dec(x_63);
x_65 = l_Lean_Expr_getRevArg_x21(x_9, x_64);
lean_dec(x_9);
x_66 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__2(x_65, x_2, x_3, x_4, x_5, x_62);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_name_mk_string(x_61, x_68);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_66, 0);
x_71 = lean_ctor_get(x_66, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_66);
x_72 = lean_name_mk_string(x_61, x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_61);
x_74 = !lean_is_exclusive(x_66);
if (x_74 == 0)
{
return x_66;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_66, 0);
x_76 = lean_ctor_get(x_66, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_66);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_60);
if (x_78 == 0)
{
return x_60;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_60, 0);
x_80 = lean_ctor_get(x_60, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_60);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_11);
lean_free_object(x_7);
x_89 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_9, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_7, 0);
x_91 = lean_ctor_get(x_7, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_7);
x_92 = l_Lean_Expr_getAppFn(x_90);
if (lean_obj_tag(x_92) == 4)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_128; lean_object* x_160; uint8_t x_161; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = lean_unsigned_to_nat(0u);
x_95 = l_Lean_Expr_getAppNumArgsAux(x_90, x_94);
x_160 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__10;
x_161 = lean_name_eq(x_93, x_160);
if (x_161 == 0)
{
lean_object* x_162; 
x_162 = lean_box(0);
x_128 = x_162;
goto block_159;
}
else
{
uint8_t x_163; 
x_163 = lean_nat_dec_eq(x_95, x_94);
if (x_163 == 0)
{
lean_object* x_164; 
x_164 = lean_box(0);
x_128 = x_164;
goto block_159;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_91);
return x_166;
}
}
block_127:
{
lean_object* x_97; uint8_t x_98; 
lean_dec(x_96);
x_97 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6;
x_98 = lean_name_eq(x_93, x_97);
lean_dec(x_93);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_95);
x_99 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_90, x_2, x_3, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_99;
}
else
{
lean_object* x_100; uint8_t x_101; 
x_100 = lean_unsigned_to_nat(3u);
x_101 = lean_nat_dec_eq(x_95, x_100);
if (x_101 == 0)
{
lean_object* x_102; 
lean_dec(x_95);
x_102 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_90, x_2, x_3, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_102;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_nat_sub(x_95, x_94);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_103, x_104);
lean_dec(x_103);
x_106 = l_Lean_Expr_getRevArg_x21(x_90, x_105);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_107 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_106, x_2, x_3, x_4, x_5, x_91);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = lean_nat_sub(x_95, x_104);
lean_dec(x_95);
x_111 = lean_nat_sub(x_110, x_104);
lean_dec(x_110);
x_112 = l_Lean_Expr_getRevArg_x21(x_90, x_111);
lean_dec(x_90);
x_113 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__1(x_112, x_2, x_3, x_4, x_5, x_109);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = lean_name_mk_numeral(x_108, x_114);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_108);
x_119 = lean_ctor_get(x_113, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_113, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_121 = x_113;
} else {
 lean_dec_ref(x_113);
 x_121 = lean_box(0);
}
if (lean_is_scalar(x_121)) {
 x_122 = lean_alloc_ctor(1, 2, 0);
} else {
 x_122 = x_121;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_95);
lean_dec(x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_123 = lean_ctor_get(x_107, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_107, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_125 = x_107;
} else {
 lean_dec_ref(x_107);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
}
block_159:
{
lean_object* x_129; uint8_t x_130; 
lean_dec(x_128);
x_129 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__8;
x_130 = lean_name_eq(x_93, x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_box(0);
x_96 = x_131;
goto block_127;
}
else
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_unsigned_to_nat(3u);
x_133 = lean_nat_dec_eq(x_95, x_132);
if (x_133 == 0)
{
lean_object* x_134; 
x_134 = lean_box(0);
x_96 = x_134;
goto block_127;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_93);
x_135 = lean_nat_sub(x_95, x_94);
x_136 = lean_unsigned_to_nat(1u);
x_137 = lean_nat_sub(x_135, x_136);
lean_dec(x_135);
x_138 = l_Lean_Expr_getRevArg_x21(x_90, x_137);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_139 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_138, x_2, x_3, x_4, x_5, x_91);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_nat_sub(x_95, x_136);
lean_dec(x_95);
x_143 = lean_nat_sub(x_142, x_136);
lean_dec(x_142);
x_144 = l_Lean_Expr_getRevArg_x21(x_90, x_143);
lean_dec(x_90);
x_145 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__2(x_144, x_2, x_3, x_4, x_5, x_141);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_name_mk_string(x_140, x_146);
if (lean_is_scalar(x_148)) {
 x_150 = lean_alloc_ctor(0, 2, 0);
} else {
 x_150 = x_148;
}
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_147);
return x_150;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_140);
x_151 = lean_ctor_get(x_145, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_153 = x_145;
} else {
 lean_dec_ref(x_145);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_95);
lean_dec(x_90);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_ctor_get(x_139, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_139, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_157 = x_139;
} else {
 lean_dec_ref(x_139);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
}
}
}
else
{
lean_object* x_167; 
lean_dec(x_92);
x_167 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg(x_90, x_2, x_3, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_7);
if (x_168 == 0)
{
return x_7;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_7, 0);
x_170 = lean_ctor_get(x_7, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_7);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instReduceEvalName() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instReduceEvalName___closed__1;
return x_1;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Offset(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_ReduceEval(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__1 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__1();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__1);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__2 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__2();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__2);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__3 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__3();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__3);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__4 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__4();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___rarg___closed__4);
l_Lean_Meta_instReduceEvalOption___rarg___closed__1 = _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__1();
lean_mark_persistent(l_Lean_Meta_instReduceEvalOption___rarg___closed__1);
l_Lean_Meta_instReduceEvalOption___rarg___closed__2 = _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__2();
lean_mark_persistent(l_Lean_Meta_instReduceEvalOption___rarg___closed__2);
l_Lean_Meta_instReduceEvalOption___rarg___closed__3 = _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__3();
lean_mark_persistent(l_Lean_Meta_instReduceEvalOption___rarg___closed__3);
l_Lean_Meta_instReduceEvalOption___rarg___closed__4 = _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__4();
lean_mark_persistent(l_Lean_Meta_instReduceEvalOption___rarg___closed__4);
l_Lean_Meta_instReduceEvalOption___rarg___closed__5 = _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__5();
lean_mark_persistent(l_Lean_Meta_instReduceEvalOption___rarg___closed__5);
l_Lean_Meta_instReduceEvalOption___rarg___closed__6 = _init_l_Lean_Meta_instReduceEvalOption___rarg___closed__6();
lean_mark_persistent(l_Lean_Meta_instReduceEvalOption___rarg___closed__6);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__5);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__6);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__7);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__8 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__8();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__8);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__9 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__9();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__9);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__10 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__10();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__10);
l_Lean_Meta_instReduceEvalName___closed__1 = _init_l_Lean_Meta_instReduceEvalName___closed__1();
lean_mark_persistent(l_Lean_Meta_instReduceEvalName___closed__1);
l_Lean_Meta_instReduceEvalName = _init_l_Lean_Meta_instReduceEvalName();
lean_mark_persistent(l_Lean_Meta_instReduceEvalName);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
