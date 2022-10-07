// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.SimpValue
// Imports: Init Lean.Compiler.LCNF.Simp.SimpM
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constructorApp_x3f(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Compiler_implementedByAttr;
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at_Lean_Expr_getRevArg_x21___spec__1(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__3;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_findExpr(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__2;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__4;
extern lean_object* l_Lean_instInhabitedName;
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Init.Util", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("getElem!", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("index out of bounds", 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__2;
x_3 = lean_unsigned_to_nat(77u);
x_4 = lean_unsigned_to_nat(36u);
x_5 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 11)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_Simp_findCtor(x_11, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_8, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = 0;
x_21 = l_Lean_Expr_constructorApp_x3f(x_19, x_13, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_10);
x_22 = lean_box(0);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
uint8_t x_23; 
lean_free_object(x_15);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_27, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_25, 3);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_nat_add(x_30, x_10);
lean_dec(x_10);
lean_dec(x_30);
x_32 = lean_array_get_size(x_26);
x_33 = lean_nat_dec_lt(x_31, x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_31);
lean_dec(x_26);
x_34 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__4;
x_35 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_34);
lean_ctor_set(x_21, 0, x_35);
lean_ctor_set(x_27, 0, x_21);
return x_27;
}
else
{
lean_object* x_36; 
x_36 = lean_array_fget(x_26, x_31);
lean_dec(x_31);
lean_dec(x_26);
lean_ctor_set(x_21, 0, x_36);
lean_ctor_set(x_27, 0, x_21);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_27, 1);
lean_inc(x_37);
lean_dec(x_27);
x_38 = lean_ctor_get(x_25, 3);
lean_inc(x_38);
lean_dec(x_25);
x_39 = lean_nat_add(x_38, x_10);
lean_dec(x_10);
lean_dec(x_38);
x_40 = lean_array_get_size(x_26);
x_41 = lean_nat_dec_lt(x_39, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_26);
x_42 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__4;
x_43 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_42);
lean_ctor_set(x_21, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_array_fget(x_26, x_39);
lean_dec(x_39);
lean_dec(x_26);
lean_ctor_set(x_21, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_37);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
lean_dec(x_21);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_18);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_52 = x_50;
} else {
 lean_dec_ref(x_50);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_48, 3);
lean_inc(x_53);
lean_dec(x_48);
x_54 = lean_nat_add(x_53, x_10);
lean_dec(x_10);
lean_dec(x_53);
x_55 = lean_array_get_size(x_49);
x_56 = lean_nat_dec_lt(x_54, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_54);
lean_dec(x_49);
x_57 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__4;
x_58 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_57);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
if (lean_is_scalar(x_52)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_52;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_51);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_array_fget(x_49, x_54);
lean_dec(x_54);
lean_dec(x_49);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_52)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_52;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_51);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_15);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = 0;
x_68 = l_Lean_Expr_constructorApp_x3f(x_66, x_13, x_67);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_10);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_65);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_72 = x_68;
} else {
 lean_dec_ref(x_68);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_65);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_73, 3);
lean_inc(x_78);
lean_dec(x_73);
x_79 = lean_nat_add(x_78, x_10);
lean_dec(x_10);
lean_dec(x_78);
x_80 = lean_array_get_size(x_74);
x_81 = lean_nat_dec_lt(x_79, x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_79);
lean_dec(x_74);
x_82 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__4;
x_83 = l_panic___at_Lean_Expr_getRevArg_x21___spec__1(x_82);
if (lean_is_scalar(x_72)) {
 x_84 = lean_alloc_ctor(1, 1, 0);
} else {
 x_84 = x_72;
}
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_77)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_77;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_76);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_array_fget(x_74, x_79);
lean_dec(x_79);
lean_dec(x_74);
if (lean_is_scalar(x_72)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_72;
}
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_77)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_77;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_76);
return x_88;
}
}
}
}
else
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_1);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_9);
return x_90;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpProj_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Expr_isApp(x_1);
if (x_10 == 0)
{
lean_object* x_141; 
x_141 = lean_box(0);
x_11 = x_141;
x_12 = x_9;
goto block_140;
}
else
{
lean_object* x_142; 
x_142 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__2;
x_11 = x_142;
x_12 = x_9;
goto block_140;
}
block_140:
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = l_Lean_Expr_getAppFn(x_1);
x_18 = l_Lean_Expr_isFVar(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_free_object(x_11);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; uint8_t x_23; 
x_21 = 1;
x_22 = l_Lean_Compiler_LCNF_Simp_findExpr(x_17, x_21, x_5, x_6, x_7, x_8, x_12);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = l_Lean_Expr_isApp(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_isConst(x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_free_object(x_11);
lean_dec(x_1);
x_28 = lean_box(0);
lean_ctor_set(x_22, 0, x_28);
return x_22;
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_free_object(x_22);
x_29 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_25);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_32);
x_34 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_33);
x_35 = lean_mk_array(x_33, x_34);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_sub(x_33, x_36);
lean_dec(x_33);
x_38 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_35, x_37);
x_39 = l_Lean_mkAppN(x_24, x_38);
lean_ctor_set(x_11, 0, x_39);
lean_ctor_set(x_29, 0, x_11);
return x_29;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_41);
x_43 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_42);
x_44 = lean_mk_array(x_42, x_43);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_42, x_45);
lean_dec(x_42);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_44, x_46);
x_48 = l_Lean_mkAppN(x_24, x_47);
lean_ctor_set(x_11, 0, x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_11);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
}
}
else
{
lean_object* x_50; uint8_t x_51; 
lean_free_object(x_22);
x_50 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_25);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_52 = lean_ctor_get(x_50, 0);
lean_dec(x_52);
x_53 = lean_unsigned_to_nat(0u);
x_54 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_53);
x_55 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_54);
x_56 = lean_mk_array(x_54, x_55);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_54, x_57);
lean_dec(x_54);
x_59 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_56, x_58);
x_60 = l_Lean_mkAppN(x_24, x_59);
lean_ctor_set(x_11, 0, x_60);
lean_ctor_set(x_50, 0, x_11);
return x_50;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_dec(x_50);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_62);
x_64 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_63);
x_65 = lean_mk_array(x_63, x_64);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_sub(x_63, x_66);
lean_dec(x_63);
x_68 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_65, x_67);
x_69 = l_Lean_mkAppN(x_24, x_68);
lean_ctor_set(x_11, 0, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_11);
lean_ctor_set(x_70, 1, x_61);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_ctor_get(x_22, 0);
x_72 = lean_ctor_get(x_22, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_22);
x_73 = l_Lean_Expr_isApp(x_71);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Expr_isConst(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec(x_71);
lean_free_object(x_11);
lean_dec(x_1);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_77 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_72);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_79 = x_77;
} else {
 lean_dec_ref(x_77);
 x_79 = lean_box(0);
}
x_80 = lean_unsigned_to_nat(0u);
x_81 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_80);
x_82 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_81);
x_83 = lean_mk_array(x_81, x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_sub(x_81, x_84);
lean_dec(x_81);
x_86 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_83, x_85);
x_87 = l_Lean_mkAppN(x_71, x_86);
lean_ctor_set(x_11, 0, x_87);
if (lean_is_scalar(x_79)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_79;
}
lean_ctor_set(x_88, 0, x_11);
lean_ctor_set(x_88, 1, x_78);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_89 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_72);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_unsigned_to_nat(0u);
x_93 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_92);
x_94 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_93);
x_95 = lean_mk_array(x_93, x_94);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_sub(x_93, x_96);
lean_dec(x_93);
x_98 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_95, x_97);
x_99 = l_Lean_mkAppN(x_71, x_98);
lean_ctor_set(x_11, 0, x_99);
if (lean_is_scalar(x_91)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_91;
}
lean_ctor_set(x_100, 0, x_11);
lean_ctor_set(x_100, 1, x_90);
return x_100;
}
}
}
}
else
{
lean_object* x_101; uint8_t x_102; 
lean_dec(x_11);
x_101 = l_Lean_Expr_getAppFn(x_1);
x_102 = l_Lean_Expr_isFVar(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_101);
lean_dec(x_1);
x_103 = lean_box(0);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_12);
return x_104;
}
else
{
uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = 1;
x_106 = l_Lean_Compiler_LCNF_Simp_findExpr(x_101, x_105, x_5, x_6, x_7, x_8, x_12);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = l_Lean_Expr_isApp(x_107);
if (x_110 == 0)
{
uint8_t x_111; 
x_111 = l_Lean_Expr_isConst(x_107);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_107);
lean_dec(x_1);
x_112 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_109);
x_114 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_108);
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
x_117 = lean_unsigned_to_nat(0u);
x_118 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_117);
x_119 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_118);
x_120 = lean_mk_array(x_118, x_119);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_sub(x_118, x_121);
lean_dec(x_118);
x_123 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_120, x_122);
x_124 = l_Lean_mkAppN(x_107, x_123);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
if (lean_is_scalar(x_116)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_116;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_115);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_109);
x_127 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_108);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_129 = x_127;
} else {
 lean_dec_ref(x_127);
 x_129 = lean_box(0);
}
x_130 = lean_unsigned_to_nat(0u);
x_131 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_130);
x_132 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_131);
x_133 = lean_mk_array(x_131, x_132);
x_134 = lean_unsigned_to_nat(1u);
x_135 = lean_nat_sub(x_131, x_134);
lean_dec(x_131);
x_136 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_133, x_135);
x_137 = l_Lean_mkAppN(x_107, x_136);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
if (lean_is_scalar(x_129)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_129;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_128);
return x_139;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscrCore_x3f(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
lean_dec(x_11);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 1);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_25 = x_11;
} else {
 lean_dec_ref(x_11);
 x_25 = lean_box(0);
}
if (lean_is_scalar(x_25)) {
 x_26 = lean_alloc_ctor(1, 1, 0);
} else {
 x_26 = x_25;
}
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_implementedByAttr;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get_uint8(x_10, 2);
if (x_11 == 0)
{
lean_object* x_95; 
x_95 = lean_box(0);
x_12 = x_95;
x_13 = x_9;
goto block_94;
}
else
{
lean_object* x_96; 
x_96 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__2;
x_12 = x_96;
x_13 = x_9;
goto block_94;
}
block_94:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_12);
x_16 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_8, x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_instInhabitedName;
x_25 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
x_26 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_24, x_25, x_23, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_dec(x_18);
lean_dec(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
uint8_t x_28; 
lean_free_object(x_19);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = l_Lean_Expr_const___override(x_29, x_18);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_34);
x_36 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_35);
x_37 = lean_mk_array(x_35, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_35, x_38);
lean_dec(x_35);
x_40 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_37, x_39);
x_41 = l_Lean_mkAppN(x_33, x_40);
lean_ctor_set(x_26, 0, x_41);
lean_ctor_set(x_30, 0, x_26);
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_dec(x_30);
x_43 = l_Lean_Expr_const___override(x_29, x_18);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_44);
x_46 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_45);
x_47 = lean_mk_array(x_45, x_46);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_sub(x_45, x_48);
lean_dec(x_45);
x_50 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_47, x_49);
x_51 = l_Lean_mkAppN(x_43, x_50);
lean_ctor_set(x_26, 0, x_51);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_26);
lean_ctor_set(x_52, 1, x_42);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_53 = lean_ctor_get(x_26, 0);
lean_inc(x_53);
lean_dec(x_26);
x_54 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
x_57 = l_Lean_Expr_const___override(x_53, x_18);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_58);
x_60 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_59);
x_61 = lean_mk_array(x_59, x_60);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_59, x_62);
lean_dec(x_59);
x_64 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_61, x_63);
x_65 = l_Lean_mkAppN(x_57, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
if (lean_is_scalar(x_56)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_56;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_55);
return x_67;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_19, 0);
x_69 = lean_ctor_get(x_19, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_19);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_instInhabitedName;
x_72 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1;
x_73 = l_Lean_ParametricAttribute_getParam_x3f___rarg(x_71, x_72, x_70, x_17);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_18);
lean_dec(x_1);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_69);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_77 = x_73;
} else {
 lean_dec_ref(x_73);
 x_77 = lean_box(0);
}
x_78 = l_Lean_Compiler_LCNF_Simp_markSimplified___rarg(x_3, x_4, x_5, x_6, x_7, x_8, x_69);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = l_Lean_Expr_const___override(x_76, x_18);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_1, x_82);
x_84 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1;
lean_inc(x_83);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_sub(x_83, x_86);
lean_dec(x_83);
x_88 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_85, x_87);
x_89 = l_Lean_mkAppN(x_81, x_88);
if (lean_is_scalar(x_77)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_77;
}
lean_ctor_set(x_90, 0, x_89);
if (lean_is_scalar(x_80)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_80;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_79);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
lean_dec(x_16);
lean_dec(x_1);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_13);
return x_93;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = l_Lean_Compiler_LCNF_Simp_simpProj_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Simp_simpCtorDiscr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_16, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 0);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_16, 0, x_24);
return x_16;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_16, 1);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_ctor_get(x_17, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_27 = x_17;
} else {
 lean_dec_ref(x_17);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 1, 0);
} else {
 x_28 = x_27;
}
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_13, 0);
lean_dec(x_35);
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_13, 0, x_38);
return x_13;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_13, 1);
lean_inc(x_39);
lean_dec(x_13);
x_40 = lean_ctor_get(x_14, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_41 = x_14;
} else {
 lean_dec_ref(x_14);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_10, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_10;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_11, 0);
lean_inc(x_47);
lean_dec(x_11);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_10, 0, x_48);
return x_10;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_dec(x_10);
x_50 = lean_ctor_get(x_11, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_51 = x_11;
} else {
 lean_dec_ref(x_11);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__2);
l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__3);
l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpProj_x3f___closed__4);
l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__1);
l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_simpAppApp_x3f___closed__2);
l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_applyImplementedBy_x3f___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
