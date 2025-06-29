// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Proj
// Imports: Lean.ProjFns Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Internalize
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
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Goal_getRoot(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__0;
lean_object* l_Lean_Meta_Grind_isCongrRoot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__3;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__2;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__4;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__1;
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateProjEq___closed__5;
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_get_projection_info(lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_get_projection_info(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_get_projection_info(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(x_1, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateProjEq___closed__2;
x_2 = l_Lean_Meta_Grind_propagateProjEq___closed__1;
x_3 = l_Lean_Meta_Grind_propagateProjEq___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateProjEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateProjEq___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateProjEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_11) == 4)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(x_12, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_23 = lean_ctor_get(x_13, 1);
x_24 = lean_ctor_get(x_13, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_21, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 2);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_26, x_28);
x_30 = l_Lean_Expr_getAppNumArgs(x_1);
x_31 = lean_nat_dec_eq(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_13, 0, x_32);
return x_13;
}
else
{
lean_object* x_33; 
lean_free_object(x_13);
lean_inc(x_1);
x_33 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_1, x_2, x_8, x_9, x_23);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
uint8_t x_36; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_33, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_33, 0, x_38);
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_33, 1);
lean_inc(x_42);
lean_dec(x_33);
x_43 = lean_st_ref_get(x_2, x_42);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_47);
x_48 = l_Lean_Meta_Grind_Goal_getRoot(x_45, x_47, x_8, x_9, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_124; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_124 = l_Lean_Expr_isAppOf(x_49, x_25);
lean_dec(x_25);
if (x_124 == 0)
{
lean_object* x_125; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_125 = lean_box(0);
lean_ctor_set(x_43, 1, x_50);
lean_ctor_set(x_43, 0, x_125);
return x_43;
}
else
{
uint8_t x_126; 
lean_free_object(x_43);
x_126 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_47, x_49);
lean_dec(x_47);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_127 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_49);
x_128 = l_Lean_Expr_app___override(x_127, x_49);
x_129 = l_Lean_Meta_Grind_shareCommon___redArg(x_128, x_5, x_50);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_130);
x_136 = lean_grind_internalize(x_130, x_133, x_135, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; 
x_137 = lean_ctor_get(x_136, 1);
lean_inc(x_137);
lean_dec(x_136);
x_81 = x_130;
x_82 = x_2;
x_83 = x_3;
x_84 = x_4;
x_85 = x_5;
x_86 = x_6;
x_87 = x_7;
x_88 = x_8;
x_89 = x_9;
x_90 = x_137;
goto block_123;
}
else
{
lean_dec(x_130);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_136;
}
}
else
{
x_81 = x_1;
x_82 = x_2;
x_83 = x_3;
x_84 = x_4;
x_85 = x_5;
x_86 = x_6;
x_87 = x_7;
x_88 = x_8;
x_89 = x_9;
x_90 = x_50;
goto block_123;
}
}
block_80:
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_62 = lean_nat_add(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_63 = l_Lean_Expr_getAppNumArgs(x_49);
x_64 = lean_nat_dec_lt(x_62, x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_49);
x_65 = lean_box(0);
if (lean_is_scalar(x_51)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_51;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_61);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_51);
x_67 = lean_nat_sub(x_63, x_62);
lean_dec(x_62);
lean_dec(x_63);
x_68 = lean_nat_sub(x_67, x_28);
lean_dec(x_67);
x_69 = l_Lean_Expr_getRevArg_x21(x_49, x_68);
lean_dec(x_49);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_69);
x_70 = l_Lean_Meta_mkEqRefl(x_69, x_57, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_box(0);
x_74 = lean_unbox(x_73);
x_75 = l_Lean_Meta_Grind_pushEqCore(x_52, x_69, x_71, x_74, x_53, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_72);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
return x_75;
}
else
{
uint8_t x_76; 
lean_dec(x_69);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
x_76 = !lean_is_exclusive(x_70);
if (x_76 == 0)
{
return x_70;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_70, 0);
x_78 = lean_ctor_get(x_70, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_70);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
block_123:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_91 = l_Lean_Meta_Grind_propagateProjEq___closed__3;
x_92 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_91, x_88, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_52 = x_81;
x_53 = x_82;
x_54 = x_83;
x_55 = x_84;
x_56 = x_85;
x_57 = x_86;
x_58 = x_87;
x_59 = x_88;
x_60 = x_89;
x_61 = x_95;
goto block_80;
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_92, 1);
x_98 = lean_ctor_get(x_92, 0);
lean_dec(x_98);
x_99 = l_Lean_Meta_Grind_updateLastTag(x_82, x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_97);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_99, 1);
x_102 = lean_ctor_get(x_99, 0);
lean_dec(x_102);
x_103 = l_Lean_Meta_Grind_propagateProjEq___closed__5;
lean_inc(x_81);
x_104 = l_Lean_MessageData_ofExpr(x_81);
lean_ctor_set_tag(x_99, 7);
lean_ctor_set(x_99, 1, x_104);
lean_ctor_set(x_99, 0, x_103);
lean_ctor_set_tag(x_92, 7);
lean_ctor_set(x_92, 1, x_103);
lean_ctor_set(x_92, 0, x_99);
x_105 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_91, x_92, x_86, x_87, x_88, x_89, x_101);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_52 = x_81;
x_53 = x_82;
x_54 = x_83;
x_55 = x_84;
x_56 = x_85;
x_57 = x_86;
x_58 = x_87;
x_59 = x_88;
x_60 = x_89;
x_61 = x_106;
goto block_80;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_107 = lean_ctor_get(x_99, 1);
lean_inc(x_107);
lean_dec(x_99);
x_108 = l_Lean_Meta_Grind_propagateProjEq___closed__5;
lean_inc(x_81);
x_109 = l_Lean_MessageData_ofExpr(x_81);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
lean_ctor_set_tag(x_92, 7);
lean_ctor_set(x_92, 1, x_108);
lean_ctor_set(x_92, 0, x_110);
x_111 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_91, x_92, x_86, x_87, x_88, x_89, x_107);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_52 = x_81;
x_53 = x_82;
x_54 = x_83;
x_55 = x_84;
x_56 = x_85;
x_57 = x_86;
x_58 = x_87;
x_59 = x_88;
x_60 = x_89;
x_61 = x_112;
goto block_80;
}
}
else
{
lean_free_object(x_92);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_27);
lean_dec(x_26);
return x_99;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_92, 1);
lean_inc(x_113);
lean_dec(x_92);
x_114 = l_Lean_Meta_Grind_updateLastTag(x_82, x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_116 = x_114;
} else {
 lean_dec_ref(x_114);
 x_116 = lean_box(0);
}
x_117 = l_Lean_Meta_Grind_propagateProjEq___closed__5;
lean_inc(x_81);
x_118 = l_Lean_MessageData_ofExpr(x_81);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(7, 2, 0);
} else {
 x_119 = x_116;
 lean_ctor_set_tag(x_119, 7);
}
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_117);
x_121 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_91, x_120, x_86, x_87, x_88, x_89, x_115);
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_52 = x_81;
x_53 = x_82;
x_54 = x_83;
x_55 = x_84;
x_56 = x_85;
x_57 = x_86;
x_58 = x_87;
x_59 = x_88;
x_60 = x_89;
x_61 = x_122;
goto block_80;
}
else
{
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_27);
lean_dec(x_26);
return x_114;
}
}
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_47);
lean_free_object(x_43);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_48);
if (x_138 == 0)
{
return x_48;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_48, 0);
x_140 = lean_ctor_get(x_48, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_48);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_43, 0);
x_143 = lean_ctor_get(x_43, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_43);
x_144 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_144);
x_145 = l_Lean_Meta_Grind_Goal_getRoot(x_142, x_144, x_8, x_9, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_205; 
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
x_205 = l_Lean_Expr_isAppOf(x_146, x_25);
lean_dec(x_25);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = lean_box(0);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_147);
return x_207;
}
else
{
uint8_t x_208; 
x_208 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_144, x_146);
lean_dec(x_144);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_209 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_146);
x_210 = l_Lean_Expr_app___override(x_209, x_146);
x_211 = l_Lean_Meta_Grind_shareCommon___redArg(x_210, x_5, x_147);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_213);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_212);
x_218 = lean_grind_internalize(x_212, x_215, x_217, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_216);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; 
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_178 = x_212;
x_179 = x_2;
x_180 = x_3;
x_181 = x_4;
x_182 = x_5;
x_183 = x_6;
x_184 = x_7;
x_185 = x_8;
x_186 = x_9;
x_187 = x_219;
goto block_204;
}
else
{
lean_dec(x_212);
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_218;
}
}
else
{
x_178 = x_1;
x_179 = x_2;
x_180 = x_3;
x_181 = x_4;
x_182 = x_5;
x_183 = x_6;
x_184 = x_7;
x_185 = x_8;
x_186 = x_9;
x_187 = x_147;
goto block_204;
}
}
block_177:
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_159 = lean_nat_add(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
x_160 = l_Lean_Expr_getAppNumArgs(x_146);
x_161 = lean_nat_dec_lt(x_159, x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_146);
x_162 = lean_box(0);
if (lean_is_scalar(x_148)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_148;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_158);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_148);
x_164 = lean_nat_sub(x_160, x_159);
lean_dec(x_159);
lean_dec(x_160);
x_165 = lean_nat_sub(x_164, x_28);
lean_dec(x_164);
x_166 = l_Lean_Expr_getRevArg_x21(x_146, x_165);
lean_dec(x_146);
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_166);
x_167 = l_Lean_Meta_mkEqRefl(x_166, x_154, x_155, x_156, x_157, x_158);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_box(0);
x_171 = lean_unbox(x_170);
x_172 = l_Lean_Meta_Grind_pushEqCore(x_149, x_166, x_168, x_171, x_150, x_151, x_152, x_153, x_154, x_155, x_156, x_157, x_169);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_166);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
lean_dec(x_149);
x_173 = lean_ctor_get(x_167, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_167, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_175 = x_167;
} else {
 lean_dec_ref(x_167);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
}
block_204:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
x_188 = l_Lean_Meta_Grind_propagateProjEq___closed__3;
x_189 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_188, x_185, x_187);
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_unbox(x_190);
lean_dec(x_190);
if (x_191 == 0)
{
lean_object* x_192; 
x_192 = lean_ctor_get(x_189, 1);
lean_inc(x_192);
lean_dec(x_189);
x_149 = x_178;
x_150 = x_179;
x_151 = x_180;
x_152 = x_181;
x_153 = x_182;
x_154 = x_183;
x_155 = x_184;
x_156 = x_185;
x_157 = x_186;
x_158 = x_192;
goto block_177;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_189, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_194 = x_189;
} else {
 lean_dec_ref(x_189);
 x_194 = lean_box(0);
}
x_195 = l_Lean_Meta_Grind_updateLastTag(x_179, x_180, x_181, x_182, x_183, x_184, x_185, x_186, x_193);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
x_198 = l_Lean_Meta_Grind_propagateProjEq___closed__5;
lean_inc(x_178);
x_199 = l_Lean_MessageData_ofExpr(x_178);
if (lean_is_scalar(x_197)) {
 x_200 = lean_alloc_ctor(7, 2, 0);
} else {
 x_200 = x_197;
 lean_ctor_set_tag(x_200, 7);
}
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
if (lean_is_scalar(x_194)) {
 x_201 = lean_alloc_ctor(7, 2, 0);
} else {
 x_201 = x_194;
 lean_ctor_set_tag(x_201, 7);
}
lean_ctor_set(x_201, 0, x_200);
lean_ctor_set(x_201, 1, x_198);
x_202 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_188, x_201, x_183, x_184, x_185, x_186, x_196);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_149 = x_178;
x_150 = x_179;
x_151 = x_180;
x_152 = x_181;
x_153 = x_182;
x_154 = x_183;
x_155 = x_184;
x_156 = x_185;
x_157 = x_186;
x_158 = x_203;
goto block_177;
}
else
{
lean_dec(x_194);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_148);
lean_dec(x_146);
lean_dec(x_27);
lean_dec(x_26);
return x_195;
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_144);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_145, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_145, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_222 = x_145;
} else {
 lean_dec_ref(x_145);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_224 = !lean_is_exclusive(x_33);
if (x_224 == 0)
{
return x_33;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_33, 0);
x_226 = lean_ctor_get(x_33, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_33);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_228 = lean_ctor_get(x_13, 1);
lean_inc(x_228);
lean_dec(x_13);
x_229 = lean_ctor_get(x_21, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_21, 1);
lean_inc(x_230);
x_231 = lean_ctor_get(x_21, 2);
lean_inc(x_231);
lean_dec(x_21);
x_232 = lean_unsigned_to_nat(1u);
x_233 = lean_nat_add(x_230, x_232);
x_234 = l_Lean_Expr_getAppNumArgs(x_1);
x_235 = lean_nat_dec_eq(x_233, x_234);
lean_dec(x_234);
lean_dec(x_233);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_236 = lean_box(0);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_228);
return x_237;
}
else
{
lean_object* x_238; 
lean_inc(x_1);
x_238 = l_Lean_Meta_Grind_isCongrRoot___redArg(x_1, x_2, x_8, x_9, x_228);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_238, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_242 = x_238;
} else {
 lean_dec_ref(x_238);
 x_242 = lean_box(0);
}
x_243 = lean_box(0);
if (lean_is_scalar(x_242)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_242;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_241);
return x_244;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_245 = lean_ctor_get(x_238, 1);
lean_inc(x_245);
lean_dec(x_238);
x_246 = lean_st_ref_get(x_2, x_245);
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_250);
x_251 = l_Lean_Meta_Grind_Goal_getRoot(x_247, x_250, x_8, x_9, x_248);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_311; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_254 = x_251;
} else {
 lean_dec_ref(x_251);
 x_254 = lean_box(0);
}
x_311 = l_Lean_Expr_isAppOf(x_252, x_229);
lean_dec(x_229);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; 
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_312 = lean_box(0);
if (lean_is_scalar(x_249)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_249;
}
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_253);
return x_313;
}
else
{
uint8_t x_314; 
lean_dec(x_249);
x_314 = l_Lean_Meta_Grind_isSameExpr_unsafe__1(x_250, x_252);
lean_dec(x_250);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_315 = l_Lean_Expr_appFn_x21(x_1);
lean_inc(x_252);
x_316 = l_Lean_Expr_app___override(x_315, x_252);
x_317 = l_Lean_Meta_Grind_shareCommon___redArg(x_316, x_5, x_253);
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_319);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_318);
x_324 = lean_grind_internalize(x_318, x_321, x_323, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_322);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; 
x_325 = lean_ctor_get(x_324, 1);
lean_inc(x_325);
lean_dec(x_324);
x_284 = x_318;
x_285 = x_2;
x_286 = x_3;
x_287 = x_4;
x_288 = x_5;
x_289 = x_6;
x_290 = x_7;
x_291 = x_8;
x_292 = x_9;
x_293 = x_325;
goto block_310;
}
else
{
lean_dec(x_318);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_324;
}
}
else
{
x_284 = x_1;
x_285 = x_2;
x_286 = x_3;
x_287 = x_4;
x_288 = x_5;
x_289 = x_6;
x_290 = x_7;
x_291 = x_8;
x_292 = x_9;
x_293 = x_253;
goto block_310;
}
}
block_283:
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; 
x_265 = lean_nat_add(x_230, x_231);
lean_dec(x_231);
lean_dec(x_230);
x_266 = l_Lean_Expr_getAppNumArgs(x_252);
x_267 = lean_nat_dec_lt(x_265, x_266);
if (x_267 == 0)
{
lean_object* x_268; lean_object* x_269; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_252);
x_268 = lean_box(0);
if (lean_is_scalar(x_254)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_254;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_264);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_254);
x_270 = lean_nat_sub(x_266, x_265);
lean_dec(x_265);
lean_dec(x_266);
x_271 = lean_nat_sub(x_270, x_232);
lean_dec(x_270);
x_272 = l_Lean_Expr_getRevArg_x21(x_252, x_271);
lean_dec(x_252);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_272);
x_273 = l_Lean_Meta_mkEqRefl(x_272, x_260, x_261, x_262, x_263, x_264);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec(x_273);
x_276 = lean_box(0);
x_277 = lean_unbox(x_276);
x_278 = l_Lean_Meta_Grind_pushEqCore(x_255, x_272, x_274, x_277, x_256, x_257, x_258, x_259, x_260, x_261, x_262, x_263, x_275);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_272);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
x_279 = lean_ctor_get(x_273, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_273, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_281 = x_273;
} else {
 lean_dec_ref(x_273);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
block_310:
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; 
x_294 = l_Lean_Meta_Grind_propagateProjEq___closed__3;
x_295 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_294, x_291, x_293);
x_296 = lean_ctor_get(x_295, 0);
lean_inc(x_296);
x_297 = lean_unbox(x_296);
lean_dec(x_296);
if (x_297 == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_295, 1);
lean_inc(x_298);
lean_dec(x_295);
x_255 = x_284;
x_256 = x_285;
x_257 = x_286;
x_258 = x_287;
x_259 = x_288;
x_260 = x_289;
x_261 = x_290;
x_262 = x_291;
x_263 = x_292;
x_264 = x_298;
goto block_283;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_295, 1);
lean_inc(x_299);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_300 = x_295;
} else {
 lean_dec_ref(x_295);
 x_300 = lean_box(0);
}
x_301 = l_Lean_Meta_Grind_updateLastTag(x_285, x_286, x_287, x_288, x_289, x_290, x_291, x_292, x_299);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_303 = x_301;
} else {
 lean_dec_ref(x_301);
 x_303 = lean_box(0);
}
x_304 = l_Lean_Meta_Grind_propagateProjEq___closed__5;
lean_inc(x_284);
x_305 = l_Lean_MessageData_ofExpr(x_284);
if (lean_is_scalar(x_303)) {
 x_306 = lean_alloc_ctor(7, 2, 0);
} else {
 x_306 = x_303;
 lean_ctor_set_tag(x_306, 7);
}
lean_ctor_set(x_306, 0, x_304);
lean_ctor_set(x_306, 1, x_305);
if (lean_is_scalar(x_300)) {
 x_307 = lean_alloc_ctor(7, 2, 0);
} else {
 x_307 = x_300;
 lean_ctor_set_tag(x_307, 7);
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_304);
x_308 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_294, x_307, x_289, x_290, x_291, x_292, x_302);
x_309 = lean_ctor_get(x_308, 1);
lean_inc(x_309);
lean_dec(x_308);
x_255 = x_284;
x_256 = x_285;
x_257 = x_286;
x_258 = x_287;
x_259 = x_288;
x_260 = x_289;
x_261 = x_290;
x_262 = x_291;
x_263 = x_292;
x_264 = x_309;
goto block_283;
}
else
{
lean_dec(x_300);
lean_dec(x_292);
lean_dec(x_291);
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_287);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_dec(x_254);
lean_dec(x_252);
lean_dec(x_231);
lean_dec(x_230);
return x_301;
}
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_326 = lean_ctor_get(x_251, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_251, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_328 = x_251;
} else {
 lean_dec_ref(x_251);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_330 = lean_ctor_get(x_238, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_238, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_238)) {
 lean_ctor_release(x_238, 0);
 lean_ctor_release(x_238, 1);
 x_332 = x_238;
} else {
 lean_dec_ref(x_238);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_334 = lean_box(0);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_10);
return x_335;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getProjectionFnInfo_x3f___at___Lean_Meta_Grind_propagateProjEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* initialize_Lean_ProjFns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Proj(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ProjFns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_propagateProjEq___closed__0 = _init_l_Lean_Meta_Grind_propagateProjEq___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateProjEq___closed__0);
l_Lean_Meta_Grind_propagateProjEq___closed__1 = _init_l_Lean_Meta_Grind_propagateProjEq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateProjEq___closed__1);
l_Lean_Meta_Grind_propagateProjEq___closed__2 = _init_l_Lean_Meta_Grind_propagateProjEq___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateProjEq___closed__2);
l_Lean_Meta_Grind_propagateProjEq___closed__3 = _init_l_Lean_Meta_Grind_propagateProjEq___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateProjEq___closed__3);
l_Lean_Meta_Grind_propagateProjEq___closed__4 = _init_l_Lean_Meta_Grind_propagateProjEq___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateProjEq___closed__4);
l_Lean_Meta_Grind_propagateProjEq___closed__5 = _init_l_Lean_Meta_Grind_propagateProjEq___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateProjEq___closed__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
