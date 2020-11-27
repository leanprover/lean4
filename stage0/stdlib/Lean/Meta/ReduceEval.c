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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_instReduceEvalOption_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3;
lean_object* l_Lean_Meta_reduceEval___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instReduceEvalNat_match__1(lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instReduceEvalString_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__4;
lean_object* l_Lean_Meta_instReduceEvalName___closed__1;
lean_object* l_Lean_Meta_instReduceEvalNat_match__1___rarg(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instReduceEvalString_match__1(lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4;
lean_object* l_Lean_Meta_instReduceEvalOption(lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2;
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Meta_0__Lean_quoteName___closed__2;
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__1;
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__2;
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1;
lean_object* l_Lean_Meta_instReduceEvalOption___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instReduceEvalString(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
extern lean_object* l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_match__1(lean_object*);
lean_object* lean_name_mk_numeral(lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_reduceEval(lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instReduceEvalOption_match__1(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1017____spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; 
x_32 = lean_ctor_get_uint8(x_9, 0);
x_33 = lean_ctor_get_uint8(x_9, 1);
x_34 = lean_ctor_get_uint8(x_9, 2);
x_35 = lean_ctor_get_uint8(x_9, 3);
x_36 = lean_ctor_get_uint8(x_9, 4);
x_37 = lean_ctor_get_uint8(x_9, 5);
x_38 = lean_ctor_get_uint8(x_9, 6);
x_39 = lean_ctor_get_uint8(x_9, 7);
lean_dec(x_9);
x_40 = 1;
x_41 = l_Lean_Meta_TransparencyMode_lt(x_37, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_42, 0, x_32);
lean_ctor_set_uint8(x_42, 1, x_33);
lean_ctor_set_uint8(x_42, 2, x_34);
lean_ctor_set_uint8(x_42, 3, x_35);
lean_ctor_set_uint8(x_42, 4, x_36);
lean_ctor_set_uint8(x_42, 5, x_37);
lean_ctor_set_uint8(x_42, 6, x_38);
lean_ctor_set_uint8(x_42, 7, x_39);
lean_ctor_set(x_3, 0, x_42);
x_43 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_50 = x_43;
} else {
 lean_dec_ref(x_43);
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
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_52, 0, x_32);
lean_ctor_set_uint8(x_52, 1, x_33);
lean_ctor_set_uint8(x_52, 2, x_34);
lean_ctor_set_uint8(x_52, 3, x_35);
lean_ctor_set_uint8(x_52, 4, x_36);
lean_ctor_set_uint8(x_52, 5, x_40);
lean_ctor_set_uint8(x_52, 6, x_38);
lean_ctor_set_uint8(x_52, 7, x_39);
lean_ctor_set(x_3, 0, x_52);
x_53 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; 
x_62 = lean_ctor_get(x_3, 0);
x_63 = lean_ctor_get(x_3, 1);
x_64 = lean_ctor_get(x_3, 2);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_3);
x_65 = lean_ctor_get_uint8(x_62, 0);
x_66 = lean_ctor_get_uint8(x_62, 1);
x_67 = lean_ctor_get_uint8(x_62, 2);
x_68 = lean_ctor_get_uint8(x_62, 3);
x_69 = lean_ctor_get_uint8(x_62, 4);
x_70 = lean_ctor_get_uint8(x_62, 5);
x_71 = lean_ctor_get_uint8(x_62, 6);
x_72 = lean_ctor_get_uint8(x_62, 7);
if (lean_is_exclusive(x_62)) {
 x_73 = x_62;
} else {
 lean_dec_ref(x_62);
 x_73 = lean_box(0);
}
x_74 = 1;
x_75 = l_Lean_Meta_TransparencyMode_lt(x_70, x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 0, 8);
} else {
 x_76 = x_73;
}
lean_ctor_set_uint8(x_76, 0, x_65);
lean_ctor_set_uint8(x_76, 1, x_66);
lean_ctor_set_uint8(x_76, 2, x_67);
lean_ctor_set_uint8(x_76, 3, x_68);
lean_ctor_set_uint8(x_76, 4, x_69);
lean_ctor_set_uint8(x_76, 5, x_70);
lean_ctor_set_uint8(x_76, 6, x_71);
lean_ctor_set_uint8(x_76, 7, x_72);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_63);
lean_ctor_set(x_77, 2, x_64);
x_78 = lean_apply_6(x_1, x_2, x_77, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_85 = x_78;
} else {
 lean_dec_ref(x_78);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
if (lean_is_scalar(x_73)) {
 x_87 = lean_alloc_ctor(0, 0, 8);
} else {
 x_87 = x_73;
}
lean_ctor_set_uint8(x_87, 0, x_65);
lean_ctor_set_uint8(x_87, 1, x_66);
lean_ctor_set_uint8(x_87, 2, x_67);
lean_ctor_set_uint8(x_87, 3, x_68);
lean_ctor_set_uint8(x_87, 4, x_69);
lean_ctor_set_uint8(x_87, 5, x_74);
lean_ctor_set_uint8(x_87, 6, x_71);
lean_ctor_set_uint8(x_87, 7, x_72);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_63);
lean_ctor_set(x_88, 2, x_64);
x_89 = lean_apply_6(x_1, x_2, x_88, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
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
lean_object* l_Lean_Meta_reduceEval(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_reduceEval___rarg), 7, 0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reduceEval: failed to evaluate argument");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = l_Lean_indentExpr(x_1);
x_9 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__2;
x_10 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = l_Array_foldlMUnsafe_fold___at_Lean_withNestedTraces___spec__5___closed__1;
x_12 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_throwError___at_Lean_Meta_initFn____x40_Lean_Meta_Basic___hyg_1017____spec__1(x_12, lean_box(0), x_3, x_4, x_5, x_6, x_7);
return x_13;
}
}
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
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
x_7 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_13 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_8, lean_box(0), x_2, x_3, x_4, x_5, x_12);
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
lean_object* l_Lean_Meta_instReduceEvalOption___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
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
x_16 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3;
x_17 = lean_name_eq(x_13, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_free_object(x_8);
x_18 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
x_19 = lean_name_eq(x_13, x_18);
lean_dec(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_1);
x_20 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_10, lean_box(0), x_3, x_4, x_5, x_6, x_11);
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
x_23 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_10, lean_box(0), x_3, x_4, x_5, x_6, x_11);
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
x_38 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
x_39 = lean_name_eq(x_13, x_38);
lean_dec(x_13);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_15);
lean_dec(x_1);
x_40 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_10, lean_box(0), x_3, x_4, x_5, x_6, x_11);
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
x_43 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_10, lean_box(0), x_3, x_4, x_5, x_6, x_11);
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
x_58 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_10, lean_box(0), x_3, x_4, x_5, x_6, x_11);
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
x_65 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__3;
x_66 = lean_name_eq(x_62, x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
x_68 = lean_name_eq(x_62, x_67);
lean_dec(x_62);
if (x_68 == 0)
{
lean_object* x_69; 
lean_dec(x_64);
lean_dec(x_1);
x_69 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_59, lean_box(0), x_3, x_4, x_5, x_6, x_60);
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
x_72 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_59, lean_box(0), x_3, x_4, x_5, x_6, x_60);
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
x_85 = l___private_Init_Meta_0__Lean_quoteOption___rarg___closed__6;
x_86 = lean_name_eq(x_62, x_85);
lean_dec(x_62);
if (x_86 == 0)
{
lean_object* x_87; 
lean_dec(x_64);
lean_dec(x_1);
x_87 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_59, lean_box(0), x_3, x_4, x_5, x_6, x_60);
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
x_90 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_59, lean_box(0), x_3, x_4, x_5, x_6, x_60);
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
x_104 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_59, lean_box(0), x_3, x_4, x_5, x_6, x_60);
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
x_7 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_11 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_10);
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
x_19 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_18);
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
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName_match__1___rarg), 3, 0);
return x_2;
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
x_13 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_19 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_14, lean_box(0), x_2, x_3, x_4, x_5, x_18);
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
x_38 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_44 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_39, lean_box(0), x_2, x_3, x_4, x_5, x_43);
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
uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; 
x_63 = lean_ctor_get_uint8(x_8, 0);
x_64 = lean_ctor_get_uint8(x_8, 1);
x_65 = lean_ctor_get_uint8(x_8, 2);
x_66 = lean_ctor_get_uint8(x_8, 3);
x_67 = lean_ctor_get_uint8(x_8, 4);
x_68 = lean_ctor_get_uint8(x_8, 5);
x_69 = lean_ctor_get_uint8(x_8, 6);
x_70 = lean_ctor_get_uint8(x_8, 7);
lean_dec(x_8);
x_71 = 1;
x_72 = l_Lean_Meta_TransparencyMode_lt(x_68, x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_73, 0, x_63);
lean_ctor_set_uint8(x_73, 1, x_64);
lean_ctor_set_uint8(x_73, 2, x_65);
lean_ctor_set_uint8(x_73, 3, x_66);
lean_ctor_set_uint8(x_73, 4, x_67);
lean_ctor_set_uint8(x_73, 5, x_68);
lean_ctor_set_uint8(x_73, 6, x_69);
lean_ctor_set_uint8(x_73, 7, x_70);
lean_ctor_set(x_2, 0, x_73);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_74 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_75);
x_77 = l_Lean_Meta_evalNat(x_75, x_2, x_3, x_4, x_5, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_75, lean_box(0), x_2, x_3, x_4, x_5, x_79);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(1, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_75);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
x_87 = lean_ctor_get(x_78, 0);
lean_inc(x_87);
lean_dec(x_78);
if (lean_is_scalar(x_86)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_86;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_75);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_89 = lean_ctor_get(x_77, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_77, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_91 = x_77;
} else {
 lean_dec_ref(x_77);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 2, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_93 = lean_ctor_get(x_74, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_74, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_95 = x_74;
} else {
 lean_dec_ref(x_74);
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
lean_object* x_97; lean_object* x_98; 
x_97 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_97, 0, x_63);
lean_ctor_set_uint8(x_97, 1, x_64);
lean_ctor_set_uint8(x_97, 2, x_65);
lean_ctor_set_uint8(x_97, 3, x_66);
lean_ctor_set_uint8(x_97, 4, x_67);
lean_ctor_set_uint8(x_97, 5, x_71);
lean_ctor_set_uint8(x_97, 6, x_69);
lean_ctor_set_uint8(x_97, 7, x_70);
lean_ctor_set(x_2, 0, x_97);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_98 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_99);
x_101 = l_Lean_Meta_evalNat(x_99, x_2, x_3, x_4, x_5, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_99, lean_box(0), x_2, x_3, x_4, x_5, x_103);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_99);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_109 = lean_ctor_get(x_101, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_110 = x_101;
} else {
 lean_dec_ref(x_101);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_102, 0);
lean_inc(x_111);
lean_dec(x_102);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_99);
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_113 = lean_ctor_get(x_101, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_101, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_115 = x_101;
} else {
 lean_dec_ref(x_101);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_117 = lean_ctor_get(x_98, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_98, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_119 = x_98;
} else {
 lean_dec_ref(x_98);
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
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; uint8_t x_134; 
x_121 = lean_ctor_get(x_2, 0);
x_122 = lean_ctor_get(x_2, 1);
x_123 = lean_ctor_get(x_2, 2);
lean_inc(x_123);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_2);
x_124 = lean_ctor_get_uint8(x_121, 0);
x_125 = lean_ctor_get_uint8(x_121, 1);
x_126 = lean_ctor_get_uint8(x_121, 2);
x_127 = lean_ctor_get_uint8(x_121, 3);
x_128 = lean_ctor_get_uint8(x_121, 4);
x_129 = lean_ctor_get_uint8(x_121, 5);
x_130 = lean_ctor_get_uint8(x_121, 6);
x_131 = lean_ctor_get_uint8(x_121, 7);
if (lean_is_exclusive(x_121)) {
 x_132 = x_121;
} else {
 lean_dec_ref(x_121);
 x_132 = lean_box(0);
}
x_133 = 1;
x_134 = l_Lean_Meta_TransparencyMode_lt(x_129, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
if (lean_is_scalar(x_132)) {
 x_135 = lean_alloc_ctor(0, 0, 8);
} else {
 x_135 = x_132;
}
lean_ctor_set_uint8(x_135, 0, x_124);
lean_ctor_set_uint8(x_135, 1, x_125);
lean_ctor_set_uint8(x_135, 2, x_126);
lean_ctor_set_uint8(x_135, 3, x_127);
lean_ctor_set_uint8(x_135, 4, x_128);
lean_ctor_set_uint8(x_135, 5, x_129);
lean_ctor_set_uint8(x_135, 6, x_130);
lean_ctor_set_uint8(x_135, 7, x_131);
x_136 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_122);
lean_ctor_set(x_136, 2, x_123);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_136);
x_137 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_136, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_136);
lean_inc(x_138);
x_140 = l_Lean_Meta_evalNat(x_138, x_136, x_3, x_4, x_5, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_138, lean_box(0), x_136, x_3, x_4, x_5, x_142);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_136);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
if (lean_is_scalar(x_146)) {
 x_147 = lean_alloc_ctor(1, 2, 0);
} else {
 x_147 = x_146;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_145);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_148 = lean_ctor_get(x_140, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_149 = x_140;
} else {
 lean_dec_ref(x_140);
 x_149 = lean_box(0);
}
x_150 = lean_ctor_get(x_141, 0);
lean_inc(x_150);
lean_dec(x_141);
if (lean_is_scalar(x_149)) {
 x_151 = lean_alloc_ctor(0, 2, 0);
} else {
 x_151 = x_149;
}
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_148);
return x_151;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_152 = lean_ctor_get(x_140, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_140, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_154 = x_140;
} else {
 lean_dec_ref(x_140);
 x_154 = lean_box(0);
}
if (lean_is_scalar(x_154)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_154;
}
lean_ctor_set(x_155, 0, x_152);
lean_ctor_set(x_155, 1, x_153);
return x_155;
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_136);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_156 = lean_ctor_get(x_137, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_137, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_158 = x_137;
} else {
 lean_dec_ref(x_137);
 x_158 = lean_box(0);
}
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
if (lean_is_scalar(x_132)) {
 x_160 = lean_alloc_ctor(0, 0, 8);
} else {
 x_160 = x_132;
}
lean_ctor_set_uint8(x_160, 0, x_124);
lean_ctor_set_uint8(x_160, 1, x_125);
lean_ctor_set_uint8(x_160, 2, x_126);
lean_ctor_set_uint8(x_160, 3, x_127);
lean_ctor_set_uint8(x_160, 4, x_128);
lean_ctor_set_uint8(x_160, 5, x_133);
lean_ctor_set_uint8(x_160, 6, x_130);
lean_ctor_set_uint8(x_160, 7, x_131);
x_161 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_122);
lean_ctor_set(x_161, 2, x_123);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_161);
x_162 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_161, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_161);
lean_inc(x_163);
x_165 = l_Lean_Meta_evalNat(x_163, x_161, x_3, x_4, x_5, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec(x_165);
x_168 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_163, lean_box(0), x_161, x_3, x_4, x_5, x_167);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_161);
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_171 = x_168;
} else {
 lean_dec_ref(x_168);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_173 = lean_ctor_get(x_165, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_174 = x_165;
} else {
 lean_dec_ref(x_165);
 x_174 = lean_box(0);
}
x_175 = lean_ctor_get(x_166, 0);
lean_inc(x_175);
lean_dec(x_166);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_177 = lean_ctor_get(x_165, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_165, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_179 = x_165;
} else {
 lean_dec_ref(x_165);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_161);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_181 = lean_ctor_get(x_162, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_162, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_183 = x_162;
} else {
 lean_dec_ref(x_162);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
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
x_23 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_27 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_26);
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
x_35 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_34);
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
x_40 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
x_44 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_43);
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
x_52 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_51);
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
uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; 
x_57 = lean_ctor_get_uint8(x_18, 0);
x_58 = lean_ctor_get_uint8(x_18, 1);
x_59 = lean_ctor_get_uint8(x_18, 2);
x_60 = lean_ctor_get_uint8(x_18, 3);
x_61 = lean_ctor_get_uint8(x_18, 4);
x_62 = lean_ctor_get_uint8(x_18, 5);
x_63 = lean_ctor_get_uint8(x_18, 6);
x_64 = lean_ctor_get_uint8(x_18, 7);
lean_dec(x_18);
x_65 = 1;
x_66 = l_Lean_Meta_TransparencyMode_lt(x_62, x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_67, 0, x_57);
lean_ctor_set_uint8(x_67, 1, x_58);
lean_ctor_set_uint8(x_67, 2, x_59);
lean_ctor_set_uint8(x_67, 3, x_60);
lean_ctor_set_uint8(x_67, 4, x_61);
lean_ctor_set_uint8(x_67, 5, x_62);
lean_ctor_set_uint8(x_67, 6, x_63);
lean_ctor_set_uint8(x_67, 7, x_64);
lean_ctor_set(x_2, 0, x_67);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_68 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 9)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_71);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_72;
goto block_16;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec(x_70);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
x_7 = x_76;
goto block_16;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_69);
x_77 = lean_ctor_get(x_68, 1);
lean_inc(x_77);
lean_dec(x_68);
x_78 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_77);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_78;
goto block_16;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_79 = lean_ctor_get(x_68, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_68, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_81 = x_68;
} else {
 lean_dec_ref(x_68);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
x_7 = x_82;
goto block_16;
}
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_alloc_ctor(0, 0, 8);
lean_ctor_set_uint8(x_83, 0, x_57);
lean_ctor_set_uint8(x_83, 1, x_58);
lean_ctor_set_uint8(x_83, 2, x_59);
lean_ctor_set_uint8(x_83, 3, x_60);
lean_ctor_set_uint8(x_83, 4, x_61);
lean_ctor_set_uint8(x_83, 5, x_65);
lean_ctor_set_uint8(x_83, 6, x_63);
lean_ctor_set_uint8(x_83, 7, x_64);
lean_ctor_set(x_2, 0, x_83);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_84 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 9)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec(x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_86);
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_88 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_87);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_88;
goto block_16;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_90 = x_84;
} else {
 lean_dec_ref(x_84);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
lean_dec(x_86);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
x_7 = x_92;
goto block_16;
}
}
else
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_85);
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
lean_dec(x_84);
x_94 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = x_94;
goto block_16;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_2);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_95 = lean_ctor_get(x_84, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_84, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_97 = x_84;
} else {
 lean_dec_ref(x_84);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
x_7 = x_98;
goto block_16;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; 
x_99 = lean_ctor_get(x_2, 0);
x_100 = lean_ctor_get(x_2, 1);
x_101 = lean_ctor_get(x_2, 2);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_2);
x_102 = lean_ctor_get_uint8(x_99, 0);
x_103 = lean_ctor_get_uint8(x_99, 1);
x_104 = lean_ctor_get_uint8(x_99, 2);
x_105 = lean_ctor_get_uint8(x_99, 3);
x_106 = lean_ctor_get_uint8(x_99, 4);
x_107 = lean_ctor_get_uint8(x_99, 5);
x_108 = lean_ctor_get_uint8(x_99, 6);
x_109 = lean_ctor_get_uint8(x_99, 7);
if (lean_is_exclusive(x_99)) {
 x_110 = x_99;
} else {
 lean_dec_ref(x_99);
 x_110 = lean_box(0);
}
x_111 = 1;
x_112 = l_Lean_Meta_TransparencyMode_lt(x_107, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
if (lean_is_scalar(x_110)) {
 x_113 = lean_alloc_ctor(0, 0, 8);
} else {
 x_113 = x_110;
}
lean_ctor_set_uint8(x_113, 0, x_102);
lean_ctor_set_uint8(x_113, 1, x_103);
lean_ctor_set_uint8(x_113, 2, x_104);
lean_ctor_set_uint8(x_113, 3, x_105);
lean_ctor_set_uint8(x_113, 4, x_106);
lean_ctor_set_uint8(x_113, 5, x_107);
lean_ctor_set_uint8(x_113, 6, x_108);
lean_ctor_set_uint8(x_113, 7, x_109);
x_114 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_100);
lean_ctor_set(x_114, 2, x_101);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_114);
lean_inc(x_1);
x_115 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_114, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
if (lean_obj_tag(x_116) == 9)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_114, x_3, x_4, x_5, x_118);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_114);
x_7 = x_119;
goto block_16;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_114);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_121 = x_115;
} else {
 lean_dec_ref(x_115);
 x_121 = lean_box(0);
}
x_122 = lean_ctor_get(x_117, 0);
lean_inc(x_122);
lean_dec(x_117);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
x_7 = x_123;
goto block_16;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_116);
x_124 = lean_ctor_get(x_115, 1);
lean_inc(x_124);
lean_dec(x_115);
x_125 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_114, x_3, x_4, x_5, x_124);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_114);
x_7 = x_125;
goto block_16;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_114);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_126 = lean_ctor_get(x_115, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_115, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_128 = x_115;
} else {
 lean_dec_ref(x_115);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
x_7 = x_129;
goto block_16;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
if (lean_is_scalar(x_110)) {
 x_130 = lean_alloc_ctor(0, 0, 8);
} else {
 x_130 = x_110;
}
lean_ctor_set_uint8(x_130, 0, x_102);
lean_ctor_set_uint8(x_130, 1, x_103);
lean_ctor_set_uint8(x_130, 2, x_104);
lean_ctor_set_uint8(x_130, 3, x_105);
lean_ctor_set_uint8(x_130, 4, x_106);
lean_ctor_set_uint8(x_130, 5, x_111);
lean_ctor_set_uint8(x_130, 6, x_108);
lean_ctor_set_uint8(x_130, 7, x_109);
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_100);
lean_ctor_set(x_131, 2, x_101);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_131);
lean_inc(x_1);
x_132 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_131, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
if (lean_obj_tag(x_133) == 9)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec(x_133);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_134);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_136 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_131, x_3, x_4, x_5, x_135);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_131);
x_7 = x_136;
goto block_16;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_131);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_138 = x_132;
} else {
 lean_dec_ref(x_132);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_134, 0);
lean_inc(x_139);
lean_dec(x_134);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
x_7 = x_140;
goto block_16;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_133);
x_141 = lean_ctor_get(x_132, 1);
lean_inc(x_141);
lean_dec(x_132);
x_142 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_1, lean_box(0), x_131, x_3, x_4, x_5, x_141);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_131);
x_7 = x_142;
goto block_16;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_131);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_143 = lean_ctor_get(x_132, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_132, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_145 = x_132;
} else {
 lean_dec_ref(x_132);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
x_7 = x_146;
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
x_1 = lean_mk_string("str");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteName___closed__2;
x_2 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("num");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Meta_0__Lean_quoteName___closed__2;
x_2 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3;
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
x_7 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux_process___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_78; uint8_t x_79; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Lean_Expr_getAppNumArgsAux(x_9, x_13);
x_78 = l___private_Init_Meta_0__Lean_quoteName___closed__4;
x_79 = lean_name_eq(x_12, x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_free_object(x_7);
x_80 = lean_box(0);
x_15 = x_80;
goto block_77;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_eq(x_14, x_13);
if (x_81 == 0)
{
lean_object* x_82; 
lean_free_object(x_7);
x_82 = lean_box(0);
x_15 = x_82;
goto block_77;
}
else
{
lean_object* x_83; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_box(0);
lean_ctor_set(x_7, 0, x_83);
return x_7;
}
}
block_77:
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_15);
x_16 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2;
x_17 = lean_name_eq(x_12, x_16);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_dec_eq(x_14, x_18);
if (x_17 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4;
x_21 = lean_name_eq(x_12, x_20);
lean_dec(x_12);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_14);
x_22 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_9, lean_box(0), x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
else
{
if (x_19 == 0)
{
lean_object* x_23; 
lean_dec(x_14);
x_23 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_9, lean_box(0), x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_nat_sub(x_14, x_13);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = l_Lean_Expr_getRevArg_x21(x_9, x_26);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_28 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_27, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_nat_sub(x_14, x_25);
lean_dec(x_14);
x_32 = lean_nat_sub(x_31, x_25);
lean_dec(x_31);
x_33 = l_Lean_Expr_getRevArg_x21(x_9, x_32);
lean_dec(x_9);
x_34 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__1(x_33, x_2, x_3, x_4, x_5, x_30);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_name_mk_numeral(x_29, x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_name_mk_numeral(x_29, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
lean_dec(x_29);
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_28);
if (x_46 == 0)
{
return x_28;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_28, 0);
x_48 = lean_ctor_get(x_28, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_28);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
}
else
{
lean_dec(x_12);
if (x_19 == 0)
{
lean_object* x_50; 
lean_dec(x_14);
x_50 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_9, lean_box(0), x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_51 = lean_nat_sub(x_14, x_13);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_51, x_52);
lean_dec(x_51);
x_54 = l_Lean_Expr_getRevArg_x21(x_9, x_53);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_55 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_54, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_nat_sub(x_14, x_52);
lean_dec(x_14);
x_59 = lean_nat_sub(x_58, x_52);
lean_dec(x_58);
x_60 = l_Lean_Expr_getRevArg_x21(x_9, x_59);
lean_dec(x_9);
x_61 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__2(x_60, x_2, x_3, x_4, x_5, x_57);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_name_mk_string(x_56, x_63);
lean_ctor_set(x_61, 0, x_64);
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_61, 0);
x_66 = lean_ctor_get(x_61, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_61);
x_67 = lean_name_mk_string(x_56, x_65);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_56);
x_69 = !lean_is_exclusive(x_61);
if (x_69 == 0)
{
return x_61;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_61, 0);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_61);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_55);
if (x_73 == 0)
{
return x_55;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_55, 0);
x_75 = lean_ctor_get(x_55, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_55);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
}
}
else
{
lean_object* x_84; 
lean_dec(x_11);
lean_free_object(x_7);
x_84 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_9, lean_box(0), x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_7, 0);
x_86 = lean_ctor_get(x_7, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_7);
x_87 = l_Lean_Expr_getAppFn(x_85);
if (lean_obj_tag(x_87) == 4)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_150; uint8_t x_151; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_Expr_getAppNumArgsAux(x_85, x_89);
x_150 = l___private_Init_Meta_0__Lean_quoteName___closed__4;
x_151 = lean_name_eq(x_88, x_150);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = lean_box(0);
x_91 = x_152;
goto block_149;
}
else
{
uint8_t x_153; 
x_153 = lean_nat_dec_eq(x_90, x_89);
if (x_153 == 0)
{
lean_object* x_154; 
x_154 = lean_box(0);
x_91 = x_154;
goto block_149;
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_box(0);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_86);
return x_156;
}
}
block_149:
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_91);
x_92 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2;
x_93 = lean_name_eq(x_88, x_92);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_nat_dec_eq(x_90, x_94);
if (x_93 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4;
x_97 = lean_name_eq(x_88, x_96);
lean_dec(x_88);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_90);
x_98 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_85, lean_box(0), x_2, x_3, x_4, x_5, x_86);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_98;
}
else
{
if (x_95 == 0)
{
lean_object* x_99; 
lean_dec(x_90);
x_99 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_85, lean_box(0), x_2, x_3, x_4, x_5, x_86);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_nat_sub(x_90, x_89);
x_101 = lean_unsigned_to_nat(1u);
x_102 = lean_nat_sub(x_100, x_101);
lean_dec(x_100);
x_103 = l_Lean_Expr_getRevArg_x21(x_85, x_102);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_104 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_103, x_2, x_3, x_4, x_5, x_86);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_nat_sub(x_90, x_101);
lean_dec(x_90);
x_108 = lean_nat_sub(x_107, x_101);
lean_dec(x_107);
x_109 = l_Lean_Expr_getRevArg_x21(x_85, x_108);
lean_dec(x_85);
x_110 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__1(x_109, x_2, x_3, x_4, x_5, x_106);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_113 = x_110;
} else {
 lean_dec_ref(x_110);
 x_113 = lean_box(0);
}
x_114 = lean_name_mk_numeral(x_105, x_111);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_105);
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_118 = x_110;
} else {
 lean_dec_ref(x_110);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_90);
lean_dec(x_85);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_120 = lean_ctor_get(x_104, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_104, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_122 = x_104;
} else {
 lean_dec_ref(x_104);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
else
{
lean_dec(x_88);
if (x_95 == 0)
{
lean_object* x_124; 
lean_dec(x_90);
x_124 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_85, lean_box(0), x_2, x_3, x_4, x_5, x_86);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_nat_sub(x_90, x_89);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_sub(x_125, x_126);
lean_dec(x_125);
x_128 = l_Lean_Expr_getRevArg_x21(x_85, x_127);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_129 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName(x_128, x_2, x_3, x_4, x_5, x_86);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_nat_sub(x_90, x_126);
lean_dec(x_90);
x_133 = lean_nat_sub(x_132, x_126);
lean_dec(x_132);
x_134 = l_Lean_Expr_getRevArg_x21(x_85, x_133);
lean_dec(x_85);
x_135 = l_Lean_Meta_reduceEval___at___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___spec__2(x_134, x_2, x_3, x_4, x_5, x_131);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = lean_name_mk_string(x_130, x_136);
if (lean_is_scalar(x_138)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_138;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_130);
x_141 = lean_ctor_get(x_135, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_143 = x_135;
} else {
 lean_dec_ref(x_135);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_90);
lean_dec(x_85);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_ctor_get(x_129, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_129, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_147 = x_129;
} else {
 lean_dec_ref(x_129);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
}
}
else
{
lean_object* x_157; 
lean_dec(x_87);
x_157 = l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval(x_85, lean_box(0), x_2, x_3, x_4, x_5, x_86);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_157;
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = !lean_is_exclusive(x_7);
if (x_158 == 0)
{
return x_7;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_7, 0);
x_160 = lean_ctor_get(x_7, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_7);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
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
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__1 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__1();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__1);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__2 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__2();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_throwFailedToEval___closed__2);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__1);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__2);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__3);
l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4 = _init_l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4();
lean_mark_persistent(l___private_Lean_Meta_ReduceEval_0__Lean_Meta_evalName___closed__4);
l_Lean_Meta_instReduceEvalName___closed__1 = _init_l_Lean_Meta_instReduceEvalName___closed__1();
lean_mark_persistent(l_Lean_Meta_instReduceEvalName___closed__1);
l_Lean_Meta_instReduceEvalName = _init_l_Lean_Meta_instReduceEvalName();
lean_mark_persistent(l_Lean_Meta_instReduceEvalName);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
