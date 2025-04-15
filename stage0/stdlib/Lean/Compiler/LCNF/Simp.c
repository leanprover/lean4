// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp
// Imports: Lean.Compiler.LCNF.ReduceJpArity Lean.Compiler.LCNF.Renaming Lean.Compiler.LCNF.Simp.Basic Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.JpCases Lean.Compiler.LCNF.Simp.Config Lean.Compiler.LCNF.Simp.InlineCandidate Lean.Compiler.LCNF.Simp.SimpM Lean.Compiler.LCNF.Simp.Main Lean.Compiler.LCNF.Simp.InlineProj Lean.Compiler.LCNF.Simp.DefaultAlt Lean.Compiler.LCNF.Simp.SimpValue Lean.Compiler.LCNF.Simp.Used
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
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__11;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__13;
lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__1;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__5;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__15;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__7;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__16;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1___boxed(lean_object**);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__2;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Decl_inlineable(lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__10;
lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
lean_object* l_Lean_Compiler_LCNF_inBasePhase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_simp___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__18;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__6;
lean_object* l_Lean_Meta_isInstance(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_size_go(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__17;
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__14;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__2;
lean_object* l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__8;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__9;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__4;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__4;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__12;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__6;
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__3;
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__7;
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_1);
x_33 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_4);
lean_ctor_set(x_33, 3, x_5);
lean_ctor_set(x_33, 4, x_32);
lean_ctor_set(x_33, 5, x_8);
lean_ctor_set_uint8(x_33, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_33, sizeof(void*)*6 + 1, x_7);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_21, 0, x_34);
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_1);
x_37 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_37, 0, x_2);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_4);
lean_ctor_set(x_37, 3, x_5);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_8);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_37, sizeof(void*)*6 + 1, x_7);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_18, 1);
lean_inc(x_40);
lean_dec(x_18);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_19, 0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_3);
lean_ctor_set(x_44, 2, x_4);
lean_ctor_set(x_44, 3, x_5);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_8);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_44, sizeof(void*)*6 + 1, x_7);
x_45 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_44, x_13, x_14, x_15, x_16, x_40);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_ctor_set(x_19, 0, x_47);
lean_ctor_set(x_45, 0, x_19);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_45, 0);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_45);
lean_ctor_set(x_19, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_19);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_free_object(x_19);
x_51 = !lean_is_exclusive(x_45);
if (x_51 == 0)
{
return x_45;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_45, 0);
x_53 = lean_ctor_get(x_45, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_45);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_19, 0);
lean_inc(x_55);
lean_dec(x_19);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_3);
lean_ctor_set(x_57, 2, x_4);
lean_ctor_set(x_57, 3, x_5);
lean_ctor_set(x_57, 4, x_56);
lean_ctor_set(x_57, 5, x_8);
lean_ctor_set_uint8(x_57, sizeof(void*)*6, x_6);
lean_ctor_set_uint8(x_57, sizeof(void*)*6 + 1, x_7);
x_58 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_57, x_13, x_14, x_15, x_16, x_40);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_59);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_58, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_66 = x_58;
} else {
 lean_dec_ref(x_58);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
else
{
uint8_t x_68; 
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
x_68 = !lean_is_exclusive(x_18);
if (x_68 == 0)
{
return x_18;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_18, 0);
x_70 = lean_ctor_get(x_18, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_18);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inline", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("info", 4, 4);
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
x_1 = lean_mk_string_unchecked("step", 4, 4);
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
x_1 = lean_mk_string_unchecked("new", 3, 3);
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
x_1 = lean_mk_string_unchecked("stat", 4, 4);
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
x_1 = lean_mk_string_unchecked("", 0, 0);
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
x_1 = lean_mk_string_unchecked(", size: ", 8, 8);
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
x_1 = lean_mk_string_unchecked(", # visited: ", 13, 13);
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
x_1 = lean_mk_string_unchecked(", # inline: ", 12, 12);
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
x_1 = lean_mk_string_unchecked(", # inline local: ", 18, 18);
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
x_1 = lean_mk_string_unchecked(" :=\n", 4, 4);
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
x_1 = lean_mk_string_unchecked(":", 1, 1);
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
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_17 = lean_ctor_get(x_1, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_19 = x_10;
} else {
 lean_dec_ref(x_10);
 x_19 = lean_box(0);
}
x_20 = 0;
lean_inc(x_18);
x_21 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo(x_18, x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_190 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
x_191 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_190, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_22);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_unbox(x_192);
lean_dec(x_192);
if (x_193 == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_191, 1);
lean_inc(x_194);
lean_dec(x_191);
x_23 = x_194;
goto block_189;
}
else
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_191);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_196 = lean_ctor_get(x_191, 1);
x_197 = lean_ctor_get(x_191, 0);
lean_dec(x_197);
x_198 = lean_st_ref_get(x_3, x_196);
x_199 = !lean_is_exclusive(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_198, 0);
x_201 = lean_ctor_get(x_198, 1);
x_202 = lean_ctor_get(x_200, 3);
lean_inc(x_202);
lean_dec(x_200);
x_203 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_202, x_5, x_6, x_7, x_8, x_201);
lean_dec(x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
lean_inc(x_11);
x_206 = l_Lean_MessageData_ofName(x_11);
x_207 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
lean_ctor_set_tag(x_198, 7);
lean_ctor_set(x_198, 1, x_206);
lean_ctor_set(x_198, 0, x_207);
x_208 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25;
lean_ctor_set_tag(x_191, 7);
lean_ctor_set(x_191, 1, x_208);
lean_ctor_set(x_191, 0, x_198);
x_209 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26;
x_210 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_204);
x_211 = l_Lean_MessageData_ofFormat(x_210);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_191);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_207);
x_214 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_190, x_213, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_205);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_23 = x_215;
goto block_189;
}
else
{
uint8_t x_216; 
lean_free_object(x_198);
lean_free_object(x_191);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_216 = !lean_is_exclusive(x_203);
if (x_216 == 0)
{
return x_203;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_203, 0);
x_218 = lean_ctor_get(x_203, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_203);
x_219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_219, 0, x_217);
lean_ctor_set(x_219, 1, x_218);
return x_219;
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_220 = lean_ctor_get(x_198, 0);
x_221 = lean_ctor_get(x_198, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_198);
x_222 = lean_ctor_get(x_220, 3);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_222, x_5, x_6, x_7, x_8, x_221);
lean_dec(x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
lean_inc(x_11);
x_226 = l_Lean_MessageData_ofName(x_11);
x_227 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_226);
x_229 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25;
lean_ctor_set_tag(x_191, 7);
lean_ctor_set(x_191, 1, x_229);
lean_ctor_set(x_191, 0, x_228);
x_230 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26;
x_231 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_224);
x_232 = l_Lean_MessageData_ofFormat(x_231);
x_233 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_233, 0, x_191);
lean_ctor_set(x_233, 1, x_232);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_227);
x_235 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_190, x_234, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_225);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_23 = x_236;
goto block_189;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_free_object(x_191);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_237 = lean_ctor_get(x_223, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_223, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_239 = x_223;
} else {
 lean_dec_ref(x_223);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_241 = lean_ctor_get(x_191, 1);
lean_inc(x_241);
lean_dec(x_191);
x_242 = lean_st_ref_get(x_3, x_241);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
x_246 = lean_ctor_get(x_243, 3);
lean_inc(x_246);
lean_dec(x_243);
x_247 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_246, x_5, x_6, x_7, x_8, x_244);
lean_dec(x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
lean_inc(x_11);
x_250 = l_Lean_MessageData_ofName(x_11);
x_251 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
if (lean_is_scalar(x_245)) {
 x_252 = lean_alloc_ctor(7, 2, 0);
} else {
 x_252 = x_245;
 lean_ctor_set_tag(x_252, 7);
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
x_253 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25;
x_254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_255 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26;
x_256 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_248);
x_257 = l_Lean_MessageData_ofFormat(x_256);
x_258 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_258, 0, x_254);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_251);
x_260 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_190, x_259, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_249);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_23 = x_261;
goto block_189;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_245);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_262 = lean_ctor_get(x_247, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_247, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_264 = x_247;
} else {
 lean_dec_ref(x_247);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(1, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
}
}
block_189:
{
lean_object* x_24; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_173 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
x_174 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_23);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_unbox(x_175);
lean_dec(x_175);
if (x_176 == 0)
{
lean_object* x_177; 
lean_dec(x_1);
x_177 = lean_ctor_get(x_174, 1);
lean_inc(x_177);
lean_dec(x_174);
x_24 = x_177;
goto block_172;
}
else
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_174, 1);
lean_inc(x_178);
lean_dec(x_174);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_179 = l_Lean_Compiler_LCNF_ppDecl(x_1, x_5, x_6, x_7, x_8, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_MessageData_ofFormat(x_180);
x_183 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_173, x_182, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_181);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
lean_dec(x_183);
x_24 = x_184;
goto block_172;
}
else
{
uint8_t x_185; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_185 = !lean_is_exclusive(x_179);
if (x_185 == 0)
{
return x_179;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_179, 0);
x_187 = lean_ctor_get(x_179, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_179);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
block_172:
{
lean_object* x_25; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_Compiler_LCNF_Simp_simp(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_3, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_29, 2);
lean_inc(x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_26, x_32, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_122 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
x_123 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_122, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_35);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_dec(x_123);
x_36 = x_126;
goto block_121;
}
else
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_123);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_123, 1);
x_129 = lean_ctor_get(x_123, 0);
lean_dec(x_129);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
x_130 = l_Lean_Compiler_LCNF_ppCode(x_34, x_5, x_6, x_7, x_8, x_128);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_11);
x_133 = l_Lean_MessageData_ofName(x_11);
x_134 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
lean_ctor_set_tag(x_123, 7);
lean_ctor_set(x_123, 1, x_133);
lean_ctor_set(x_123, 0, x_134);
x_135 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_123);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_MessageData_ofFormat(x_131);
x_138 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
x_140 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_122, x_139, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_132);
x_141 = lean_ctor_get(x_140, 1);
lean_inc(x_141);
lean_dec(x_140);
x_36 = x_141;
goto block_121;
}
else
{
uint8_t x_142; 
lean_free_object(x_123);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_130);
if (x_142 == 0)
{
return x_130;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_130, 0);
x_144 = lean_ctor_get(x_130, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_130);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_123, 1);
lean_inc(x_146);
lean_dec(x_123);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_34);
x_147 = l_Lean_Compiler_LCNF_ppCode(x_34, x_5, x_6, x_7, x_8, x_146);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
lean_inc(x_11);
x_150 = l_Lean_MessageData_ofName(x_11);
x_151 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_150);
x_153 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_MessageData_ofFormat(x_148);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_151);
x_158 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_122, x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_149);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec(x_158);
x_36 = x_159;
goto block_121;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_160 = lean_ctor_get(x_147, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_147, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_162 = x_147;
} else {
 lean_dec_ref(x_147);
 x_162 = lean_box(0);
}
if (lean_is_scalar(x_162)) {
 x_163 = lean_alloc_ctor(1, 2, 0);
} else {
 x_163 = x_162;
}
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_161);
return x_163;
}
}
}
block_121:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
x_38 = l_Lean_isTracingEnabledFor___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__1(x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_36);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_19);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_42 = lean_box(0);
x_43 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(x_34, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_42, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_43;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_45 = lean_ctor_get(x_38, 1);
x_46 = lean_ctor_get(x_38, 0);
lean_dec(x_46);
lean_inc(x_11);
x_47 = l_Lean_MessageData_ofName(x_11);
x_48 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
lean_ctor_set_tag(x_38, 7);
lean_ctor_set(x_38, 1, x_47);
lean_ctor_set(x_38, 0, x_48);
x_49 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
if (lean_is_scalar(x_31)) {
 x_50 = lean_alloc_ctor(7, 2, 0);
} else {
 x_50 = x_31;
 lean_ctor_set_tag(x_50, 7);
}
lean_ctor_set(x_50, 0, x_38);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_unsigned_to_nat(0u);
x_52 = l_Lean_Compiler_LCNF_Code_size_go(x_34, x_51);
x_53 = l___private_Init_Data_Repr_0__Nat_reprFast(x_52);
if (lean_is_scalar(x_19)) {
 x_54 = lean_alloc_ctor(3, 1, 0);
} else {
 x_54 = x_19;
 lean_ctor_set_tag(x_54, 3);
}
lean_ctor_set(x_54, 0, x_53);
x_55 = l_Lean_MessageData_ofFormat(x_54);
x_56 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_ctor_get(x_29, 4);
lean_inc(x_59);
x_60 = l___private_Init_Data_Repr_0__Nat_reprFast(x_59);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_MessageData_ofFormat(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_ctor_get(x_29, 5);
lean_inc(x_66);
x_67 = l___private_Init_Data_Repr_0__Nat_reprFast(x_66);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = l_Lean_MessageData_ofFormat(x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_ctor_get(x_29, 6);
lean_inc(x_73);
lean_dec(x_29);
x_74 = l___private_Init_Data_Repr_0__Nat_reprFast(x_73);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = l_Lean_MessageData_ofFormat(x_75);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_48);
x_79 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_37, x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_45);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(x_34, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_81);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_80);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_83 = lean_ctor_get(x_38, 1);
lean_inc(x_83);
lean_dec(x_38);
lean_inc(x_11);
x_84 = l_Lean_MessageData_ofName(x_11);
x_85 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
x_87 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
if (lean_is_scalar(x_31)) {
 x_88 = lean_alloc_ctor(7, 2, 0);
} else {
 x_88 = x_31;
 lean_ctor_set_tag(x_88, 7);
}
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Lean_Compiler_LCNF_Code_size_go(x_34, x_89);
x_91 = l___private_Init_Data_Repr_0__Nat_reprFast(x_90);
if (lean_is_scalar(x_19)) {
 x_92 = lean_alloc_ctor(3, 1, 0);
} else {
 x_92 = x_19;
 lean_ctor_set_tag(x_92, 3);
}
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_MessageData_ofFormat(x_92);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_ctor_get(x_29, 4);
lean_inc(x_97);
x_98 = l___private_Init_Data_Repr_0__Nat_reprFast(x_97);
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_Lean_MessageData_ofFormat(x_99);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_ctor_get(x_29, 5);
lean_inc(x_104);
x_105 = l___private_Init_Data_Repr_0__Nat_reprFast(x_104);
x_106 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Lean_MessageData_ofFormat(x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_ctor_get(x_29, 6);
lean_inc(x_111);
lean_dec(x_29);
x_112 = l___private_Init_Data_Repr_0__Nat_reprFast(x_111);
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_110);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_85);
x_117 = l_Lean_addTrace___at_Lean_Compiler_LCNF_Simp_withInlining_check___spec__3(x_37, x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_83);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = l_Lean_Compiler_LCNF_Decl_simp_x3f___lambda__1(x_34, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_118, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_119);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_118);
return x_120;
}
}
}
}
else
{
uint8_t x_164; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_164 = !lean_is_exclusive(x_33);
if (x_164 == 0)
{
return x_33;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_33, 0);
x_166 = lean_ctor_get(x_33, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_33);
x_167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
return x_167;
}
}
}
else
{
uint8_t x_168; 
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_25);
if (x_168 == 0)
{
return x_25;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_25, 0);
x_170 = lean_ctor_get(x_25, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_25);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_21);
if (x_266 == 0)
{
return x_21;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_21, 0);
x_268 = lean_ctor_get(x_21, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_21);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_270 = lean_box(0);
x_271 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_9);
return x_271;
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
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__3;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__5;
x_3 = 0;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_1);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set(x_5, 4, x_4);
lean_ctor_set(x_5, 5, x_4);
lean_ctor_set(x_5, 6, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*7, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__2;
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
x_10 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__2;
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
x_16 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__7;
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
lean_dec(x_23);
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
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__3;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__4;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__6;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__8;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__9;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__10;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__11;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__12;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__13;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__15;
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__16;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__17;
x_2 = lean_unsigned_to_nat(843u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__1;
x_3 = 1;
x_4 = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__18;
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
l_Lean_Compiler_LCNF_simp___closed__1 = _init_l_Lean_Compiler_LCNF_simp___closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_simp___closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__1 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__1();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__1);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__2 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__2();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__2);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__3 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__3();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__3);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__4 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__4();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__4);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__5 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__5();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__5);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__6 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__6();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__6);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__7 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__7();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__7);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__8 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__8();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__8);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__9 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__9);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__10 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__10();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__10);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__11 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__11();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__11);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__12 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__12();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__12);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__13 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__13();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__13);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__14 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__14();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__14);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__15 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__15();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__15);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__16 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__16();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__16);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__17 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__17();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__17);
l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__18 = _init_l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__18();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843____closed__18);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_843_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
