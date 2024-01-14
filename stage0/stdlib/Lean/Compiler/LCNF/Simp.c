// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp
// Imports: Init Lean.Compiler.LCNF.ReduceJpArity Lean.Compiler.LCNF.Renaming Lean.Compiler.LCNF.Simp.Basic Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.JpCases Lean.Compiler.LCNF.Simp.Config Lean.Compiler.LCNF.Simp.InlineCandidate Lean.Compiler.LCNF.Simp.SimpM Lean.Compiler.LCNF.Simp.Main Lean.Compiler.LCNF.Simp.InlineProj Lean.Compiler.LCNF.Simp.DefaultAlt Lean.Compiler.LCNF.Simp.SimpValue Lean.Compiler.LCNF.Simp.Used
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
lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__10;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10;
lean_object* l_Lean_mkHashSetImp___rarg(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__7;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__12;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1___boxed(lean_object**);
lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__6;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__1;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__17;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__11;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__3;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__8;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineable(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__9;
lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__14;
lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_simp___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__18;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__4;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__7;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__6;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__5;
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_size_go(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__16;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__3;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__8;
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__13;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__15;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_1);
x_18 = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(x_1, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_st_ref_get(x_11, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_22, sizeof(void*)*7);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_3);
lean_ctor_set(x_32, 2, x_4);
lean_ctor_set(x_32, 3, x_5);
lean_ctor_set(x_32, 4, x_1);
lean_ctor_set(x_32, 5, x_8);
lean_ctor_set_uint8(x_32, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_32, sizeof(void*)*6 + 1, x_7);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_21, 0, x_33);
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_21, 1);
lean_inc(x_34);
lean_dec(x_21);
x_35 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_35, 2, x_4);
lean_ctor_set(x_35, 3, x_5);
lean_ctor_set(x_35, 4, x_1);
lean_ctor_set(x_35, 5, x_8);
lean_ctor_set_uint8(x_35, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_35, sizeof(void*)*6 + 1, x_7);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_dec(x_18);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_19, 0);
x_41 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_3);
lean_ctor_set(x_41, 2, x_4);
lean_ctor_set(x_41, 3, x_5);
lean_ctor_set(x_41, 4, x_40);
lean_ctor_set(x_41, 5, x_8);
lean_ctor_set_uint8(x_41, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_41, sizeof(void*)*6 + 1, x_7);
x_42 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_41, x_13, x_14, x_15, x_16, x_38);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_ctor_set(x_19, 0, x_44);
lean_ctor_set(x_42, 0, x_19);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_42, 0);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_42);
lean_ctor_set(x_19, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_free_object(x_19);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_42);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_19, 0);
lean_inc(x_52);
lean_dec(x_19);
x_53 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 2, x_4);
lean_ctor_set(x_53, 3, x_5);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_8);
lean_ctor_set_uint8(x_53, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_53, sizeof(void*)*6 + 1, x_7);
x_54 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_53, x_13, x_14, x_15, x_16, x_38);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_55);
if (lean_is_scalar(x_57)) {
 x_59 = lean_alloc_ctor(0, 2, 0);
} else {
 x_59 = x_57;
}
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_56);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_54, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_62 = x_54;
} else {
 lean_dec_ref(x_54);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_18);
if (x_64 == 0)
{
return x_18;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_18, 0);
x_66 = lean_ctor_get(x_18, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_18);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Compiler", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("inline", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("info", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
x_4 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("step", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("new", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6;
x_4 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("stat", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("", 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", size: ", 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", # visited: ", 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", # inline: ", 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(", # inline local: ", 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(" :=\n", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes(":", 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_17 = lean_ctor_get(x_1, 5);
lean_inc(x_17);
x_18 = 0;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_14);
x_19 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_14, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_129 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
x_130 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_129, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_21 = x_133;
goto block_128;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_134 = lean_ctor_get(x_130, 1);
lean_inc(x_134);
lean_dec(x_130);
x_135 = lean_st_ref_get(x_3, x_134);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_ctor_get(x_136, 3);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_138, x_5, x_6, x_7, x_8, x_137);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
lean_inc(x_10);
x_142 = l_Lean_MessageData_ofName(x_10);
x_143 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_142);
x_145 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25;
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26;
x_148 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_140);
x_149 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_150);
lean_ctor_set(x_151, 1, x_143);
x_152 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__6(x_129, x_151, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_141);
x_153 = lean_ctor_get(x_152, 1);
lean_inc(x_153);
lean_dec(x_152);
x_21 = x_153;
goto block_128;
}
else
{
uint8_t x_154; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_154 = !lean_is_exclusive(x_139);
if (x_154 == 0)
{
return x_139;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_139, 0);
x_156 = lean_ctor_get(x_139, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_139);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
block_128:
{
lean_object* x_22; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
x_113 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_112, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_unbox(x_114);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_1);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_22 = x_116;
goto block_111;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_113, 1);
lean_inc(x_117);
lean_dec(x_113);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_118 = l_Lean_Compiler_LCNF_ppDecl(x_1, x_5, x_6, x_7, x_8, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_121 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_121, 0, x_119);
x_122 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__6(x_112, x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_120);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_22 = x_123;
goto block_111;
}
else
{
uint8_t x_124; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = !lean_is_exclusive(x_118);
if (x_124 == 0)
{
return x_118;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_118, 0);
x_126 = lean_ctor_get(x_118, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_118);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
block_111:
{
lean_object* x_23; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_Compiler_LCNF_Simp_simp(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_3, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_24, x_29, x_5, x_6, x_7, x_8, x_28);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_80 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
x_81 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
lean_dec(x_81);
x_33 = x_84;
goto block_79;
}
else
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_85);
lean_dec(x_81);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_31);
x_86 = l_Lean_Compiler_LCNF_ppCode(x_31, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_10);
x_89 = l_Lean_MessageData_ofName(x_10);
x_90 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
x_92 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_87);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_90);
x_97 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__6(x_80, x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_88);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_33 = x_98;
goto block_79;
}
else
{
uint8_t x_99; 
lean_dec(x_31);
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_86);
if (x_99 == 0)
{
return x_86;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_86, 0);
x_101 = lean_ctor_get(x_86, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_86);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
block_79:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
x_35 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_box(0);
x_40 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(x_31, x_10, x_11, x_12, x_13, x_15, x_16, x_17, x_39, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_dec(x_35);
lean_inc(x_10);
x_42 = l_Lean_MessageData_ofName(x_10);
x_43 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
x_45 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_unsigned_to_nat(0u);
lean_inc(x_31);
x_48 = l_Lean_Compiler_LCNF_Code_size_go(x_31, x_47);
x_49 = l_Nat_repr(x_48);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_46);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_ctor_get(x_27, 4);
lean_inc(x_55);
x_56 = l_Nat_repr(x_55);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_54);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_ctor_get(x_27, 5);
lean_inc(x_62);
x_63 = l_Nat_repr(x_62);
x_64 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_61);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_ctor_get(x_27, 6);
lean_inc(x_69);
lean_dec(x_27);
x_70 = l_Nat_repr(x_69);
x_71 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_71, 0, x_70);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_43);
x_75 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__6(x_34, x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(x_31, x_10, x_11, x_12, x_13, x_15, x_16, x_17, x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_77);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_76);
return x_78;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_27);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_103 = !lean_is_exclusive(x_30);
if (x_103 == 0)
{
return x_30;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_30, 0);
x_105 = lean_ctor_get(x_30, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_30);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_107 = !lean_is_exclusive(x_23);
if (x_107 == 0)
{
return x_23;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_23, 0);
x_109 = lean_ctor_get(x_23, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_23);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
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
x_158 = !lean_is_exclusive(x_19);
if (x_158 == 0)
{
return x_19;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_19, 0);
x_160 = lean_ctor_get(x_19, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_19);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
_start:
{
uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_18 = lean_unbox(x_6);
lean_dec(x_6);
x_19 = lean_unbox(x_7);
lean_dec(x_7);
x_20 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_18, x_19, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_20;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__1;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashSetImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__4;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__5;
x_4 = 0;
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_5);
lean_ctor_set(x_6, 5, x_5);
lean_ctor_set(x_6, 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*7, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__2;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__3;
lean_inc(x_2);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
x_12 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__6;
x_13 = lean_st_mk_ref(x_12, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__8;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_14);
lean_inc(x_1);
x_17 = l_Lean_Compiler_LCNF_Decl_simp_x3f(x_1, x_11, x_14, x_16, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_14, x_19);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_1);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec(x_18);
x_1 = x_26;
x_7 = x_25;
goto _start;
}
}
else
{
uint8_t x_28; 
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 0;
lean_ctor_set_uint8(x_2, 0, x_11);
lean_ctor_set_uint8(x_2, 1, x_11);
lean_ctor_set_uint8(x_2, 3, x_3);
x_12 = lean_box(0);
x_13 = lean_apply_7(x_1, x_2, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get_uint8(x_2, 2);
lean_dec(x_2);
x_15 = 0;
x_16 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_16, 0, x_15);
lean_ctor_set_uint8(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, 2, x_14);
lean_ctor_set_uint8(x_16, 3, x_3);
x_17 = lean_box(0);
x_18 = lean_apply_7(x_1, x_16, x_17, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_Decl_isTemplateLike(x_1, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Decl_simp___lambda__1___boxed), 8, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_ctor_get_uint8(x_2, 3);
x_16 = l_Lean_Compiler_LCNF_inBasePhase(x_3, x_4, x_5, x_6, x_13);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = l_Lean_Compiler_LCNF_Decl_simp___lambda__2(x_14, x_2, x_15, x_20, x_3, x_4, x_5, x_6, x_19);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = l_Lean_Meta_isInstance(x_23, x_5, x_6, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = l_Lean_Compiler_LCNF_Decl_simp___lambda__2(x_14, x_2, x_15, x_28, x_3, x_4, x_5, x_6, x_27);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = l_Lean_Compiler_LCNF_Decl_inlineable(x_1);
lean_dec(x_1);
if (x_31 == 0)
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
x_32 = 0;
x_33 = lean_box(0);
x_34 = l_Lean_Compiler_LCNF_Decl_simp___lambda__2(x_14, x_2, x_32, x_33, x_3, x_4, x_5, x_6, x_30);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_box(0);
x_36 = l_Lean_Compiler_LCNF_Decl_simp___lambda__2(x_14, x_2, x_15, x_35, x_3, x_4, x_5, x_6, x_30);
return x_36;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Decl_simp___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Compiler_LCNF_Decl_simp___lambda__2(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Decl_simp(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lambda__1), 7, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Compiler_LCNF_simp___closed__1;
x_6 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_5, x_4, x_3, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_3);
lean_dec(x_3);
x_5 = l_Lean_Compiler_LCNF_simp(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Lean", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__3;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("LCNF", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__4;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("initFn", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__6;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_@", 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__8;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__10;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__11;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Simp", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__13;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("_hyg", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__15;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__17;
x_2 = lean_unsigned_to_nat(832u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__1;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__18;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
x_8 = 0;
x_9 = l_Lean_registerTraceClass(x_7, x_8, x_4, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
x_12 = l_Lean_registerTraceClass(x_11, x_8, x_4, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
x_15 = l_Lean_registerTraceClass(x_14, x_8, x_4, x_13);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_12);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
return x_9;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_9);
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
x_24 = !lean_is_exclusive(x_5);
if (x_24 == 0)
{
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_5, 0);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_5);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ReduceJpArity(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Renaming(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_JpCases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Config(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Renaming(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Config(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25);
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26);
l_Lean_Compiler_LCNF_Decl_simp_go___closed__1 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__1);
l_Lean_Compiler_LCNF_Decl_simp_go___closed__2 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__2);
l_Lean_Compiler_LCNF_Decl_simp_go___closed__3 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__3);
l_Lean_Compiler_LCNF_Decl_simp_go___closed__4 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__4);
l_Lean_Compiler_LCNF_Decl_simp_go___closed__5 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__5);
l_Lean_Compiler_LCNF_Decl_simp_go___closed__6 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__6);
l_Lean_Compiler_LCNF_Decl_simp_go___closed__7 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__7);
l_Lean_Compiler_LCNF_Decl_simp_go___closed__8 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__8);
l_Lean_Compiler_LCNF_simp___closed__1 = _init_l_Lean_Compiler_LCNF_simp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_simp___closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__17);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__18 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832____closed__18);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_832_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
