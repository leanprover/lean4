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
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_instInhabited___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__2;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDeclErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_Simp_instMonadSimpM;
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = l_List_isEmpty___rarg(x_1);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit(x_2, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
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
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_28);
x_35 = lean_environment_find(x_34, x_28);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_Compiler_LCNF_getDecl_x3f(x_28, x_7, x_8, x_9, x_10, x_33);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
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
x_38 = !lean_is_exclusive(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_36);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_36, 1);
x_46 = lean_ctor_get(x_36, 0);
lean_dec(x_46);
x_47 = lean_ctor_get(x_37, 0);
lean_inc(x_47);
lean_dec(x_37);
x_48 = l_Lean_Compiler_LCNF_Decl_getArity(x_47);
x_49 = lean_array_get_size(x_30);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
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
x_51 = lean_box(0);
lean_ctor_set(x_36, 0, x_51);
return x_36;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
lean_free_object(x_36);
lean_inc(x_29);
lean_inc(x_47);
x_52 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_47, x_29);
x_53 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_47, x_29);
x_54 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_55 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_52, x_53, x_30, x_54, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_45);
lean_dec(x_52);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_56, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_57);
return x_58;
}
else
{
uint8_t x_59; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_dec(x_36);
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
lean_dec(x_37);
x_65 = l_Lean_Compiler_LCNF_Decl_getArity(x_64);
x_66 = lean_array_get_size(x_30);
x_67 = lean_nat_dec_eq(x_65, x_66);
lean_dec(x_66);
lean_dec(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_64);
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
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
lean_inc(x_29);
lean_inc(x_64);
x_70 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_64, x_29);
x_71 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_64, x_29);
x_72 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_73 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_70, x_71, x_30, x_72, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_70);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
}
else
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_35, 0);
lean_inc(x_81);
lean_dec(x_35);
if (lean_obj_tag(x_81) == 6)
{
lean_dec(x_29);
lean_dec(x_28);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_81);
lean_dec(x_30);
x_82 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___closed__4;
x_83 = l_panic___at_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___spec__1(x_82, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
lean_dec(x_81);
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_2, 1);
lean_inc(x_86);
lean_dec(x_2);
x_87 = lean_ctor_get(x_84, 3);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_nat_add(x_87, x_85);
lean_dec(x_85);
lean_dec(x_87);
x_89 = lean_array_get_size(x_30);
x_90 = lean_nat_dec_lt(x_88, x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_88);
lean_dec(x_30);
x_107 = l_Lean_Compiler_LCNF_instInhabitedArg;
x_108 = l___private_Init_Util_0__outOfBounds___rarg(x_107);
if (lean_obj_tag(x_108) == 1)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___lambda__1(x_86, x_109, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
return x_110;
}
else
{
lean_object* x_111; 
lean_dec(x_108);
x_111 = lean_box(0);
x_91 = x_111;
goto block_106;
}
}
else
{
lean_object* x_112; 
x_112 = lean_array_fget(x_30, x_88);
lean_dec(x_88);
lean_dec(x_30);
if (lean_obj_tag(x_112) == 1)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___lambda__1(x_86, x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_33);
return x_114;
}
else
{
lean_object* x_115; 
lean_dec(x_112);
x_115 = lean_box(0);
x_91 = x_115;
goto block_106;
}
}
block_106:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_91);
x_92 = l_Lean_Compiler_LCNF_mkLetDeclErased(x_7, x_8, x_9, x_10, x_33);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_st_ref_get(x_10, x_94);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_st_ref_take(x_3, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_93);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_93);
x_101 = lean_array_push(x_98, x_100);
x_102 = lean_st_ref_set(x_3, x_101, x_99);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_ctor_get(x_93, 0);
lean_inc(x_104);
lean_dec(x_93);
x_105 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visit___lambda__1(x_86, x_104, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_103);
return x_105;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_81);
x_116 = l_Lean_Compiler_LCNF_getDecl_x3f(x_28, x_7, x_8, x_9, x_10, x_33);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
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
x_118 = !lean_is_exclusive(x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 0);
lean_dec(x_119);
x_120 = lean_box(0);
lean_ctor_set(x_116, 0, x_120);
return x_116;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_116, 1);
lean_inc(x_121);
lean_dec(x_116);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_116);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; 
x_125 = lean_ctor_get(x_116, 1);
x_126 = lean_ctor_get(x_116, 0);
lean_dec(x_126);
x_127 = lean_ctor_get(x_117, 0);
lean_inc(x_127);
lean_dec(x_117);
x_128 = l_Lean_Compiler_LCNF_Decl_getArity(x_127);
x_129 = lean_array_get_size(x_30);
x_130 = lean_nat_dec_eq(x_128, x_129);
lean_dec(x_129);
lean_dec(x_128);
if (x_130 == 0)
{
lean_object* x_131; 
lean_dec(x_127);
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
x_131 = lean_box(0);
lean_ctor_set(x_116, 0, x_131);
return x_116;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; 
lean_free_object(x_116);
lean_inc(x_29);
lean_inc(x_127);
x_132 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_127, x_29);
x_133 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_127, x_29);
x_134 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_135 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_132, x_133, x_30, x_134, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_125);
lean_dec(x_132);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_136, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_137);
return x_138;
}
else
{
uint8_t x_139; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_139 = !lean_is_exclusive(x_135);
if (x_139 == 0)
{
return x_135;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_135, 0);
x_141 = lean_ctor_get(x_135, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_135);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_116, 1);
lean_inc(x_143);
lean_dec(x_116);
x_144 = lean_ctor_get(x_117, 0);
lean_inc(x_144);
lean_dec(x_117);
x_145 = l_Lean_Compiler_LCNF_Decl_getArity(x_144);
x_146 = lean_array_get_size(x_30);
x_147 = lean_nat_dec_eq(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_144);
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
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_143);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; 
lean_inc(x_29);
lean_inc(x_144);
x_150 = l_Lean_Compiler_LCNF_Decl_instantiateParamsLevelParams(x_144, x_29);
x_151 = l_Lean_Compiler_LCNF_Decl_instantiateValueLevelParams(x_144, x_29);
x_152 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_153 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_150, x_151, x_30, x_152, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_143);
lean_dec(x_150);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f_visitCode(x_154, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_155);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_157 = lean_ctor_get(x_153, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_153, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_159 = x_153;
} else {
 lean_dec_ref(x_153);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
}
}
}
}
default: 
{
uint8_t x_161; 
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
x_161 = !lean_is_exclusive(x_12);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_12, 0);
lean_dec(x_162);
x_163 = lean_box(0);
lean_ctor_set(x_12, 0, x_163);
return x_12;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_12, 1);
lean_inc(x_164);
lean_dec(x_12);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
return x_166;
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
x_13 = l_Lean_Compiler_LCNF_LetValue_inferType(x_1, x_8, x_9, x_10, x_11, x_12);
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
l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___closed__1 = _init_l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f___lambda__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
