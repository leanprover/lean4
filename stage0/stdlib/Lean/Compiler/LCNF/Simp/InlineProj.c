// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.InlineProj
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
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1;
lean_object* l_Lean_Compiler_LCNF_LetExpr_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2;
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedArg;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM;
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadReaderT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_instMonadOptionT___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Simp_instMonadSimpM;
x_2 = l_ReaderT_instMonadReaderT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1;
x_2 = l_OptionT_instMonadOptionT___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2;
x_2 = l_Lean_instInhabitedFVarId;
x_3 = l_instInhabited___rarg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3;
x_12 = lean_panic_fn(x_11, x_1);
x_13 = lean_apply_9(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Simp.InlineProj", 34);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean.Compiler.LCNF.Simp.inlineProjInst?.visit", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("unreachable code has been reached", 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2;
x_3 = lean_unsigned_to_nat(57u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1;
x_2 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2;
x_3 = lean_unsigned_to_nat(59u);
x_4 = lean_unsigned_to_nat(34u);
x_5 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Compiler_LCNF_findLetDecl_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
lean_dec(x_13);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
switch (lean_obj_tag(x_21)) {
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_2);
x_1 = x_24;
x_2 = x_25;
x_11 = x_22;
goto _start;
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_ctor_get(x_21, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 2);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_st_ref_get(x_10, x_27);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_28);
x_36 = lean_environment_find(x_35, x_28);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_free_object(x_31);
x_37 = l_Lean_Compiler_LCNF_getDecl_x3f(x_28, x_7, x_8, x_9, x_10, x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_37, 0, x_41);
return x_37;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_37, 1);
x_47 = lean_ctor_get(x_37, 0);
lean_dec(x_47);
x_48 = lean_ctor_get(x_38, 0);
lean_inc(x_48);
lean_dec(x_38);
x_49 = l_Lean_Compiler_LCNF_Decl_getArity(x_48);
x_50 = lean_array_get_size(x_30);
x_51 = lean_nat_dec_eq(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec(x_48);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_box(0);
lean_ctor_set(x_37, 0, x_52);
return x_37;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
lean_free_object(x_37);
lean_inc(x_29);
lean_inc(x_48);
x_53 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_48, x_29);
x_54 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_48, x_29);
x_55 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_56 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_53, x_54, x_30, x_55, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_46);
lean_dec(x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_58);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_56);
if (x_60 == 0)
{
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 0);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_56);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_37, 1);
lean_inc(x_64);
lean_dec(x_37);
x_65 = lean_ctor_get(x_38, 0);
lean_inc(x_65);
lean_dec(x_38);
x_66 = l_Lean_Compiler_LCNF_Decl_getArity(x_65);
x_67 = lean_array_get_size(x_30);
x_68 = lean_nat_dec_eq(x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
lean_inc(x_29);
lean_inc(x_65);
x_71 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_65, x_29);
x_72 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_65, x_29);
x_73 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_74 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_71, x_72, x_30, x_73, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_64);
lean_dec(x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_75, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = lean_ctor_get(x_74, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_80 = x_74;
} else {
 lean_dec_ref(x_74);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_36);
if (x_82 == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_36, 0);
if (lean_obj_tag(x_83) == 6)
{
lean_dec(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_free_object(x_36);
lean_dec(x_83);
lean_free_object(x_31);
lean_dec(x_30);
x_84 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_85 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_ctor_get(x_2, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 1);
lean_inc(x_88);
lean_dec(x_2);
x_89 = lean_ctor_get(x_86, 3);
lean_inc(x_89);
lean_dec(x_86);
x_90 = lean_nat_add(x_89, x_87);
lean_dec(x_87);
lean_dec(x_89);
x_91 = lean_array_get_size(x_30);
x_92 = lean_nat_dec_lt(x_90, x_91);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
lean_dec(x_90);
lean_dec(x_30);
x_93 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_94 = l___private_Init_Util_0__outOfBounds___rarg(x_93);
if (lean_obj_tag(x_94) == 1)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_List_isEmpty___rarg(x_88);
if (x_96 == 0)
{
lean_free_object(x_36);
lean_free_object(x_31);
x_1 = x_95;
x_2 = x_88;
x_11 = x_34;
goto _start;
}
else
{
lean_dec(x_88);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_36, 0, x_95);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_94);
lean_dec(x_88);
lean_free_object(x_36);
lean_free_object(x_31);
x_98 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_99 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_98, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
return x_99;
}
}
else
{
lean_object* x_100; 
x_100 = lean_array_fget(x_30, x_90);
lean_dec(x_90);
lean_dec(x_30);
if (lean_obj_tag(x_100) == 1)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec(x_100);
x_102 = l_List_isEmpty___rarg(x_88);
if (x_102 == 0)
{
lean_free_object(x_36);
lean_free_object(x_31);
x_1 = x_101;
x_2 = x_88;
x_11 = x_34;
goto _start;
}
else
{
lean_dec(x_88);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_36, 0, x_101);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_100);
lean_dec(x_88);
lean_free_object(x_36);
lean_free_object(x_31);
x_104 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_105 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
return x_105;
}
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_free_object(x_36);
lean_dec(x_83);
lean_free_object(x_31);
x_106 = l_Lean_Compiler_LCNF_getDecl_x3f(x_28, x_7, x_8, x_9, x_10, x_34);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_106);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_106, 0);
lean_dec(x_109);
x_110 = lean_box(0);
lean_ctor_set(x_106, 0, x_110);
return x_106;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_106);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_115 = lean_ctor_get(x_106, 1);
x_116 = lean_ctor_get(x_106, 0);
lean_dec(x_116);
x_117 = lean_ctor_get(x_107, 0);
lean_inc(x_117);
lean_dec(x_107);
x_118 = l_Lean_Compiler_LCNF_Decl_getArity(x_117);
x_119 = lean_array_get_size(x_30);
x_120 = lean_nat_dec_eq(x_118, x_119);
lean_dec(x_119);
lean_dec(x_118);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_117);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_121 = lean_box(0);
lean_ctor_set(x_106, 0, x_121);
return x_106;
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
lean_free_object(x_106);
lean_inc(x_29);
lean_inc(x_117);
x_122 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_117, x_29);
x_123 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_117, x_29);
x_124 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_125 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_122, x_123, x_30, x_124, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_115);
lean_dec(x_122);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_126, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_127);
return x_128;
}
else
{
uint8_t x_129; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_125);
if (x_129 == 0)
{
return x_125;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_125, 0);
x_131 = lean_ctor_get(x_125, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_125);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_106, 1);
lean_inc(x_133);
lean_dec(x_106);
x_134 = lean_ctor_get(x_107, 0);
lean_inc(x_134);
lean_dec(x_107);
x_135 = l_Lean_Compiler_LCNF_Decl_getArity(x_134);
x_136 = lean_array_get_size(x_30);
x_137 = lean_nat_dec_eq(x_135, x_136);
lean_dec(x_136);
lean_dec(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_134);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_138 = lean_box(0);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_133);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; 
lean_inc(x_29);
lean_inc(x_134);
x_140 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_134, x_29);
x_141 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_134, x_29);
x_142 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_143 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_140, x_141, x_30, x_142, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_133);
lean_dec(x_140);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_144, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_145);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_149 = x_143;
} else {
 lean_dec_ref(x_143);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
}
}
}
}
else
{
lean_object* x_151; 
x_151 = lean_ctor_get(x_36, 0);
lean_inc(x_151);
lean_dec(x_36);
if (lean_obj_tag(x_151) == 6)
{
lean_dec(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_151);
lean_free_object(x_31);
lean_dec(x_30);
x_152 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_153 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_152, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; 
x_154 = lean_ctor_get(x_151, 0);
lean_inc(x_154);
lean_dec(x_151);
x_155 = lean_ctor_get(x_2, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 1);
lean_inc(x_156);
lean_dec(x_2);
x_157 = lean_ctor_get(x_154, 3);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_nat_add(x_157, x_155);
lean_dec(x_155);
lean_dec(x_157);
x_159 = lean_array_get_size(x_30);
x_160 = lean_nat_dec_lt(x_158, x_159);
lean_dec(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_158);
lean_dec(x_30);
x_161 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_162 = l___private_Init_Util_0__outOfBounds___rarg(x_161);
if (lean_obj_tag(x_162) == 1)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec(x_162);
x_164 = l_List_isEmpty___rarg(x_156);
if (x_164 == 0)
{
lean_free_object(x_31);
x_1 = x_163;
x_2 = x_156;
x_11 = x_34;
goto _start;
}
else
{
lean_object* x_166; 
lean_dec(x_156);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_31, 0, x_166);
return x_31;
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_162);
lean_dec(x_156);
lean_free_object(x_31);
x_167 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_168 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_167, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
return x_168;
}
}
else
{
lean_object* x_169; 
x_169 = lean_array_fget(x_30, x_158);
lean_dec(x_158);
lean_dec(x_30);
if (lean_obj_tag(x_169) == 1)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec(x_169);
x_171 = l_List_isEmpty___rarg(x_156);
if (x_171 == 0)
{
lean_free_object(x_31);
x_1 = x_170;
x_2 = x_156;
x_11 = x_34;
goto _start;
}
else
{
lean_object* x_173; 
lean_dec(x_156);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_31, 0, x_173);
return x_31;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_169);
lean_dec(x_156);
lean_free_object(x_31);
x_174 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_175 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_174, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
return x_175;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_151);
lean_free_object(x_31);
x_176 = l_Lean_Compiler_LCNF_getDecl_x3f(x_28, x_7, x_8, x_9, x_10, x_34);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_183 = x_176;
} else {
 lean_dec_ref(x_176);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_177, 0);
lean_inc(x_184);
lean_dec(x_177);
x_185 = l_Lean_Compiler_LCNF_Decl_getArity(x_184);
x_186 = lean_array_get_size(x_30);
x_187 = lean_nat_dec_eq(x_185, x_186);
lean_dec(x_186);
lean_dec(x_185);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_184);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_188 = lean_box(0);
if (lean_is_scalar(x_183)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_183;
}
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_182);
return x_189;
}
else
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
lean_dec(x_183);
lean_inc(x_29);
lean_inc(x_184);
x_190 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_184, x_29);
x_191 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_184, x_29);
x_192 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_193 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_190, x_191, x_30, x_192, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_182);
lean_dec(x_190);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_194, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_195);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_197 = lean_ctor_get(x_193, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_193, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_199 = x_193;
} else {
 lean_dec_ref(x_193);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
}
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_201 = lean_ctor_get(x_31, 0);
x_202 = lean_ctor_get(x_31, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_31);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_28);
x_204 = lean_environment_find(x_203, x_28);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = l_Lean_Compiler_LCNF_getDecl_x3f(x_28, x_7, x_8, x_9, x_10, x_202);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = lean_box(0);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_207);
return x_210;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_211 = lean_ctor_get(x_205, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_212 = x_205;
} else {
 lean_dec_ref(x_205);
 x_212 = lean_box(0);
}
x_213 = lean_ctor_get(x_206, 0);
lean_inc(x_213);
lean_dec(x_206);
x_214 = l_Lean_Compiler_LCNF_Decl_getArity(x_213);
x_215 = lean_array_get_size(x_30);
x_216 = lean_nat_dec_eq(x_214, x_215);
lean_dec(x_215);
lean_dec(x_214);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
lean_dec(x_213);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_217 = lean_box(0);
if (lean_is_scalar(x_212)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_212;
}
lean_ctor_set(x_218, 0, x_217);
lean_ctor_set(x_218, 1, x_211);
return x_218;
}
else
{
lean_object* x_219; lean_object* x_220; uint8_t x_221; lean_object* x_222; 
lean_dec(x_212);
lean_inc(x_29);
lean_inc(x_213);
x_219 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_213, x_29);
x_220 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_213, x_29);
x_221 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_222 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_219, x_220, x_30, x_221, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_211);
lean_dec(x_219);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_223, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_224);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_226 = lean_ctor_get(x_222, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_222, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_228 = x_222;
} else {
 lean_dec_ref(x_222);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_204, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_231 = x_204;
} else {
 lean_dec_ref(x_204);
 x_231 = lean_box(0);
}
if (lean_obj_tag(x_230) == 6)
{
lean_dec(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_30);
x_232 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_233 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_232, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_202);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_234 = lean_ctor_get(x_230, 0);
lean_inc(x_234);
lean_dec(x_230);
x_235 = lean_ctor_get(x_2, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_2, 1);
lean_inc(x_236);
lean_dec(x_2);
x_237 = lean_ctor_get(x_234, 3);
lean_inc(x_237);
lean_dec(x_234);
x_238 = lean_nat_add(x_237, x_235);
lean_dec(x_235);
lean_dec(x_237);
x_239 = lean_array_get_size(x_30);
x_240 = lean_nat_dec_lt(x_238, x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_238);
lean_dec(x_30);
x_241 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_242 = l___private_Init_Util_0__outOfBounds___rarg(x_241);
if (lean_obj_tag(x_242) == 1)
{
lean_object* x_243; uint8_t x_244; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_List_isEmpty___rarg(x_236);
if (x_244 == 0)
{
lean_dec(x_231);
x_1 = x_243;
x_2 = x_236;
x_11 = x_202;
goto _start;
}
else
{
lean_object* x_246; lean_object* x_247; 
lean_dec(x_236);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_231)) {
 x_246 = lean_alloc_ctor(1, 1, 0);
} else {
 x_246 = x_231;
}
lean_ctor_set(x_246, 0, x_243);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_202);
return x_247;
}
}
else
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_242);
lean_dec(x_236);
lean_dec(x_231);
x_248 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_249 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_248, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_202);
return x_249;
}
}
else
{
lean_object* x_250; 
x_250 = lean_array_fget(x_30, x_238);
lean_dec(x_238);
lean_dec(x_30);
if (lean_obj_tag(x_250) == 1)
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec(x_250);
x_252 = l_List_isEmpty___rarg(x_236);
if (x_252 == 0)
{
lean_dec(x_231);
x_1 = x_251;
x_2 = x_236;
x_11 = x_202;
goto _start;
}
else
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_236);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_is_scalar(x_231)) {
 x_254 = lean_alloc_ctor(1, 1, 0);
} else {
 x_254 = x_231;
}
lean_ctor_set(x_254, 0, x_251);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_202);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; 
lean_dec(x_250);
lean_dec(x_236);
lean_dec(x_231);
x_256 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5;
x_257 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_256, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_202);
return x_257;
}
}
}
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_231);
lean_dec(x_230);
x_258 = l_Lean_Compiler_LCNF_getDecl_x3f(x_28, x_7, x_8, x_9, x_10, x_202);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_261 = x_258;
} else {
 lean_dec_ref(x_258);
 x_261 = lean_box(0);
}
x_262 = lean_box(0);
if (lean_is_scalar(x_261)) {
 x_263 = lean_alloc_ctor(0, 2, 0);
} else {
 x_263 = x_261;
}
lean_ctor_set(x_263, 0, x_262);
lean_ctor_set(x_263, 1, x_260);
return x_263;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_264 = lean_ctor_get(x_258, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_265 = x_258;
} else {
 lean_dec_ref(x_258);
 x_265 = lean_box(0);
}
x_266 = lean_ctor_get(x_259, 0);
lean_inc(x_266);
lean_dec(x_259);
x_267 = l_Lean_Compiler_LCNF_Decl_getArity(x_266);
x_268 = lean_array_get_size(x_30);
x_269 = lean_nat_dec_eq(x_267, x_268);
lean_dec(x_268);
lean_dec(x_267);
if (x_269 == 0)
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_266);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_270 = lean_box(0);
if (lean_is_scalar(x_265)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_265;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_264);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; uint8_t x_274; lean_object* x_275; 
lean_dec(x_265);
lean_inc(x_29);
lean_inc(x_266);
x_272 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_266, x_29);
x_273 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_266, x_29);
x_274 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_275 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_272, x_273, x_30, x_274, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_264);
lean_dec(x_272);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec(x_275);
x_278 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_276, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_277);
return x_278;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_279 = lean_ctor_get(x_275, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_275, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_281 = x_275;
} else {
 lean_dec_ref(x_275);
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
}
}
}
}
default: 
{
uint8_t x_283; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_283 = !lean_is_exclusive(x_12);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_12, 0);
lean_dec(x_284);
x_285 = lean_box(0);
lean_ctor_set(x_12, 0, x_285);
return x_12;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_12, 1);
lean_inc(x_286);
lean_dec(x_12);
x_287 = lean_box(0);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_st_ref_get(x_10, x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_12);
x_20 = lean_array_push(x_17, x_19);
x_21 = lean_st_ref_set(x_3, x_20, x_18);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_1 = x_13;
x_11 = x_22;
goto _start;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_st_ref_get(x_10, x_11);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_take(x_3, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_24);
x_32 = lean_array_push(x_29, x_31);
x_33 = lean_st_ref_set(x_3, x_32, x_30);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_1 = x_25;
x_11 = x_34;
goto _start;
}
case 5:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_37;
}
default: 
{
lean_object* x_38; uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = l_Lean_Compiler_LCNF_eraseCode(x_1, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_st_ref_get(x_10, x_11);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___closed__1;
x_17 = lean_st_mk_ref(x_16, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_18);
x_20 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(x_2, x_13, x_18, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_st_ref_get(x_10, x_22);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_st_ref_get(x_18, x_24);
lean_dec(x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Compiler_LCNF_eraseCodeDecls(x_26, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_35 = !lean_is_exclusive(x_25);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_21, 0, x_39);
lean_ctor_set(x_25, 0, x_21);
return x_25;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_25, 0);
x_41 = lean_ctor_get(x_21, 0);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_25, 0, x_43);
return x_25;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_25, 0);
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_25);
x_46 = lean_ctor_get(x_21, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_47 = x_21;
} else {
 lean_dec_ref(x_21);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_46);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(1, 1, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_45);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_51 = !lean_is_exclusive(x_20);
if (x_51 == 0)
{
return x_20;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_20, 0);
x_53 = lean_ctor_get(x_20, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_20);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_dec(x_4);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = l_Lean_Compiler_LCNF_LetExpr_inferType(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_isClass_x3f(x_14, x_10, x_11, x_15);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1(x_2, x_3, x_19, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_20;
}
else
{
uint8_t x_21; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 2)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_getType(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Compiler_LCNF_isClass_x3f(x_13, x_7, x_8, x_14);
lean_dec(x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_box(0);
x_25 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__2(x_1, x_10, x_11, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_12);
if (x_26 == 0)
{
return x_12;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_12, 0);
x_28 = lean_ctor_get(x_12, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_12);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_9);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1 = _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__1);
l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2 = _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__2);
l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3 = _init_l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3();
lean_mark_persistent(l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__1);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__3);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__5);
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
