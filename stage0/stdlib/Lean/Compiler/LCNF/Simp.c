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
lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__5;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_712_(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__7;
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_object* l_Lean_Compiler_LCNF_Code_size(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__2;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__8;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__0;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
static lean_object* l_Lean_Compiler_LCNF_simp___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__9;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__6;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__3;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_go___closed__4;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6;
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Compiler", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stat", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", size: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", # visited: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", # inline: ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", # inline local: ", 18, 18);
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
x_1 = lean_mk_string_unchecked("new", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" :=\n", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("step", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inline", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("info", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_4 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
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
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_14, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_81 = x_14;
} else {
 lean_dec_ref(x_14);
 x_81 = lean_box(0);
}
x_82 = lean_box(0);
x_83 = lean_unbox(x_82);
lean_inc(x_80);
x_84 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_80, x_83, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_164; lean_object* x_165; lean_object* x_286; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_87 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_305 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
x_306 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_305, x_7, x_85);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_unbox(x_307);
lean_dec(x_307);
if (x_308 == 0)
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_dec(x_306);
x_286 = x_309;
goto block_304;
}
else
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_306);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; uint8_t x_314; 
x_311 = lean_ctor_get(x_306, 1);
x_312 = lean_ctor_get(x_306, 0);
lean_dec(x_312);
x_313 = lean_st_ref_get(x_3, x_311);
x_314 = !lean_is_exclusive(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_315 = lean_ctor_get(x_313, 0);
x_316 = lean_ctor_get(x_313, 1);
x_317 = lean_ctor_get(x_315, 3);
lean_inc(x_317);
lean_dec(x_315);
x_318 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_317, x_5, x_6, x_7, x_8, x_316);
lean_dec(x_317);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_321 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_inc(x_10);
x_322 = l_Lean_MessageData_ofName(x_10);
lean_ctor_set_tag(x_313, 7);
lean_ctor_set(x_313, 1, x_322);
lean_ctor_set(x_313, 0, x_321);
x_323 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
lean_ctor_set_tag(x_306, 7);
lean_ctor_set(x_306, 1, x_323);
lean_ctor_set(x_306, 0, x_313);
x_324 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24;
x_325 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_325, 0, x_324);
lean_ctor_set(x_325, 1, x_319);
x_326 = l_Lean_MessageData_ofFormat(x_325);
x_327 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_327, 0, x_306);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_321);
x_329 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_305, x_328, x_6, x_7, x_8, x_320);
x_330 = lean_ctor_get(x_329, 1);
lean_inc(x_330);
lean_dec(x_329);
x_286 = x_330;
goto block_304;
}
else
{
uint8_t x_331; 
lean_free_object(x_313);
lean_free_object(x_306);
lean_dec(x_81);
lean_dec(x_80);
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
lean_dec(x_1);
x_331 = !lean_is_exclusive(x_318);
if (x_331 == 0)
{
return x_318;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_318, 0);
x_333 = lean_ctor_get(x_318, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_318);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_335 = lean_ctor_get(x_313, 0);
x_336 = lean_ctor_get(x_313, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_313);
x_337 = lean_ctor_get(x_335, 3);
lean_inc(x_337);
lean_dec(x_335);
x_338 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_337, x_5, x_6, x_7, x_8, x_336);
lean_dec(x_337);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_inc(x_10);
x_342 = l_Lean_MessageData_ofName(x_10);
x_343 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
x_344 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
lean_ctor_set_tag(x_306, 7);
lean_ctor_set(x_306, 1, x_344);
lean_ctor_set(x_306, 0, x_343);
x_345 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24;
x_346 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_346, 0, x_345);
lean_ctor_set(x_346, 1, x_339);
x_347 = l_Lean_MessageData_ofFormat(x_346);
x_348 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_348, 0, x_306);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_341);
x_350 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_305, x_349, x_6, x_7, x_8, x_340);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
lean_dec(x_350);
x_286 = x_351;
goto block_304;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_free_object(x_306);
lean_dec(x_81);
lean_dec(x_80);
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
lean_dec(x_1);
x_352 = lean_ctor_get(x_338, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_338, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_354 = x_338;
} else {
 lean_dec_ref(x_338);
 x_354 = lean_box(0);
}
if (lean_is_scalar(x_354)) {
 x_355 = lean_alloc_ctor(1, 2, 0);
} else {
 x_355 = x_354;
}
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_353);
return x_355;
}
}
}
else
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_356 = lean_ctor_get(x_306, 1);
lean_inc(x_356);
lean_dec(x_306);
x_357 = lean_st_ref_get(x_3, x_356);
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_360 = x_357;
} else {
 lean_dec_ref(x_357);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_358, 3);
lean_inc(x_361);
lean_dec(x_358);
x_362 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_361, x_5, x_6, x_7, x_8, x_359);
lean_dec(x_361);
if (lean_obj_tag(x_362) == 0)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
x_365 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_inc(x_10);
x_366 = l_Lean_MessageData_ofName(x_10);
if (lean_is_scalar(x_360)) {
 x_367 = lean_alloc_ctor(7, 2, 0);
} else {
 x_367 = x_360;
 lean_ctor_set_tag(x_367, 7);
}
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
x_368 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
x_369 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24;
x_371 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_371, 0, x_370);
lean_ctor_set(x_371, 1, x_363);
x_372 = l_Lean_MessageData_ofFormat(x_371);
x_373 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_373, 0, x_369);
lean_ctor_set(x_373, 1, x_372);
x_374 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_365);
x_375 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_305, x_374, x_6, x_7, x_8, x_364);
x_376 = lean_ctor_get(x_375, 1);
lean_inc(x_376);
lean_dec(x_375);
x_286 = x_376;
goto block_304;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_360);
lean_dec(x_81);
lean_dec(x_80);
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
lean_dec(x_1);
x_377 = lean_ctor_get(x_362, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_362, 1);
lean_inc(x_378);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_379 = x_362;
} else {
 lean_dec_ref(x_362);
 x_379 = lean_box(0);
}
if (lean_is_scalar(x_379)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_379;
}
lean_ctor_set(x_380, 0, x_377);
lean_ctor_set(x_380, 1, x_378);
return x_380;
}
}
}
block_163:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
x_94 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_93, x_7, x_92);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_unbox(x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_81);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
lean_dec(x_94);
x_18 = x_91;
x_19 = x_3;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_97;
goto block_79;
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_94);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_99 = lean_ctor_get(x_94, 1);
x_100 = lean_ctor_get(x_94, 0);
lean_dec(x_100);
x_101 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_inc(x_10);
x_102 = l_Lean_MessageData_ofName(x_10);
lean_ctor_set_tag(x_94, 7);
lean_ctor_set(x_94, 1, x_102);
lean_ctor_set(x_94, 0, x_101);
x_103 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_94);
lean_ctor_set(x_104, 1, x_103);
x_105 = l_Lean_Compiler_LCNF_Code_size(x_91);
x_106 = l_Nat_reprFast(x_105);
if (lean_is_scalar(x_81)) {
 x_107 = lean_alloc_ctor(3, 1, 0);
} else {
 x_107 = x_81;
 lean_ctor_set_tag(x_107, 3);
}
lean_ctor_set(x_107, 0, x_106);
x_108 = l_Lean_MessageData_ofFormat(x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_104);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Nat_reprFast(x_90);
x_113 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_113, 0, x_112);
x_114 = l_Lean_MessageData_ofFormat(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_111);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Nat_reprFast(x_88);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l_Lean_MessageData_ofFormat(x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
x_122 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
x_124 = l_Nat_reprFast(x_89);
x_125 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_126 = l_Lean_MessageData_ofFormat(x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_101);
x_129 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_93, x_128, x_6, x_7, x_8, x_99);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_18 = x_91;
x_19 = x_3;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_130;
goto block_79;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_131 = lean_ctor_get(x_94, 1);
lean_inc(x_131);
lean_dec(x_94);
x_132 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_inc(x_10);
x_133 = l_Lean_MessageData_ofName(x_10);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Compiler_LCNF_Code_size(x_91);
x_138 = l_Nat_reprFast(x_137);
if (lean_is_scalar(x_81)) {
 x_139 = lean_alloc_ctor(3, 1, 0);
} else {
 x_139 = x_81;
 lean_ctor_set_tag(x_139, 3);
}
lean_ctor_set(x_139, 0, x_138);
x_140 = l_Lean_MessageData_ofFormat(x_139);
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_136);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
x_144 = l_Nat_reprFast(x_90);
x_145 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_145, 0, x_144);
x_146 = l_Lean_MessageData_ofFormat(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_143);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Nat_reprFast(x_88);
x_151 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = l_Lean_MessageData_ofFormat(x_151);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_149);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Nat_reprFast(x_89);
x_157 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_158 = l_Lean_MessageData_ofFormat(x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_132);
x_161 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_93, x_160, x_6, x_7, x_8, x_131);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_18 = x_91;
x_19 = x_3;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_162;
goto block_79;
}
}
}
block_285:
{
lean_object* x_166; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
x_166 = l_Lean_Compiler_LCNF_Simp_simp(x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_165);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_169 = lean_st_ref_get(x_3, x_168);
x_170 = !lean_is_exclusive(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_171 = lean_ctor_get(x_169, 0);
x_172 = lean_ctor_get(x_169, 1);
x_173 = lean_ctor_get(x_171, 2);
lean_inc(x_173);
x_174 = lean_ctor_get(x_171, 4);
lean_inc(x_174);
x_175 = lean_ctor_get(x_171, 5);
lean_inc(x_175);
x_176 = lean_ctor_get(x_171, 6);
lean_inc(x_176);
lean_dec(x_171);
x_177 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_167, x_173, x_5, x_6, x_7, x_8, x_172);
lean_dec(x_173);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_179 = lean_ctor_get(x_177, 0);
x_180 = lean_ctor_get(x_177, 1);
x_181 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
x_182 = l_Lean_Name_mkStr4(x_86, x_87, x_164, x_181);
lean_inc(x_182);
x_183 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_182, x_7, x_180);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_182);
lean_free_object(x_177);
lean_free_object(x_169);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_88 = x_175;
x_89 = x_176;
x_90 = x_174;
x_91 = x_179;
x_92 = x_186;
goto block_163;
}
else
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_183);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_183, 1);
x_189 = lean_ctor_get(x_183, 0);
lean_dec(x_189);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_179);
x_190 = l_Lean_Compiler_LCNF_ppCode(x_179, x_5, x_6, x_7, x_8, x_188);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_inc(x_10);
x_194 = l_Lean_MessageData_ofName(x_10);
lean_ctor_set_tag(x_183, 7);
lean_ctor_set(x_183, 1, x_194);
lean_ctor_set(x_183, 0, x_193);
x_195 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
lean_ctor_set_tag(x_177, 7);
lean_ctor_set(x_177, 1, x_195);
lean_ctor_set(x_177, 0, x_183);
x_196 = l_Lean_MessageData_ofFormat(x_191);
lean_ctor_set_tag(x_169, 7);
lean_ctor_set(x_169, 1, x_196);
lean_ctor_set(x_169, 0, x_177);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_169);
lean_ctor_set(x_197, 1, x_193);
x_198 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_182, x_197, x_6, x_7, x_8, x_192);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
x_88 = x_175;
x_89 = x_176;
x_90 = x_174;
x_91 = x_179;
x_92 = x_199;
goto block_163;
}
else
{
uint8_t x_200; 
lean_free_object(x_183);
lean_dec(x_182);
lean_free_object(x_177);
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_169);
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_200 = !lean_is_exclusive(x_190);
if (x_200 == 0)
{
return x_190;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_190, 0);
x_202 = lean_ctor_get(x_190, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_190);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_183, 1);
lean_inc(x_204);
lean_dec(x_183);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_179);
x_205 = l_Lean_Compiler_LCNF_ppCode(x_179, x_5, x_6, x_7, x_8, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_inc(x_10);
x_209 = l_Lean_MessageData_ofName(x_10);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
lean_ctor_set_tag(x_177, 7);
lean_ctor_set(x_177, 1, x_211);
lean_ctor_set(x_177, 0, x_210);
x_212 = l_Lean_MessageData_ofFormat(x_206);
lean_ctor_set_tag(x_169, 7);
lean_ctor_set(x_169, 1, x_212);
lean_ctor_set(x_169, 0, x_177);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_169);
lean_ctor_set(x_213, 1, x_208);
x_214 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_182, x_213, x_6, x_7, x_8, x_207);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_88 = x_175;
x_89 = x_176;
x_90 = x_174;
x_91 = x_179;
x_92 = x_215;
goto block_163;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_182);
lean_free_object(x_177);
lean_dec(x_179);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_169);
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_216 = lean_ctor_get(x_205, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_205, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_218 = x_205;
} else {
 lean_dec_ref(x_205);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; 
x_220 = lean_ctor_get(x_177, 0);
x_221 = lean_ctor_get(x_177, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_177);
x_222 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
x_223 = l_Lean_Name_mkStr4(x_86, x_87, x_164, x_222);
lean_inc(x_223);
x_224 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_223, x_7, x_221);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_unbox(x_225);
lean_dec(x_225);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_223);
lean_free_object(x_169);
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_88 = x_175;
x_89 = x_176;
x_90 = x_174;
x_91 = x_220;
x_92 = x_227;
goto block_163;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_229 = x_224;
} else {
 lean_dec_ref(x_224);
 x_229 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_220);
x_230 = l_Lean_Compiler_LCNF_ppCode(x_220, x_5, x_6, x_7, x_8, x_228);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_inc(x_10);
x_234 = l_Lean_MessageData_ofName(x_10);
if (lean_is_scalar(x_229)) {
 x_235 = lean_alloc_ctor(7, 2, 0);
} else {
 x_235 = x_229;
 lean_ctor_set_tag(x_235, 7);
}
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
x_236 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
x_238 = l_Lean_MessageData_ofFormat(x_231);
lean_ctor_set_tag(x_169, 7);
lean_ctor_set(x_169, 1, x_238);
lean_ctor_set(x_169, 0, x_237);
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_169);
lean_ctor_set(x_239, 1, x_233);
x_240 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_223, x_239, x_6, x_7, x_8, x_232);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
lean_dec(x_240);
x_88 = x_175;
x_89 = x_176;
x_90 = x_174;
x_91 = x_220;
x_92 = x_241;
goto block_163;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_229);
lean_dec(x_223);
lean_dec(x_220);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_free_object(x_169);
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_242 = lean_ctor_get(x_230, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_230, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_244 = x_230;
} else {
 lean_dec_ref(x_230);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_246 = lean_ctor_get(x_169, 0);
x_247 = lean_ctor_get(x_169, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_169);
x_248 = lean_ctor_get(x_246, 2);
lean_inc(x_248);
x_249 = lean_ctor_get(x_246, 4);
lean_inc(x_249);
x_250 = lean_ctor_get(x_246, 5);
lean_inc(x_250);
x_251 = lean_ctor_get(x_246, 6);
lean_inc(x_251);
lean_dec(x_246);
x_252 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_167, x_248, x_5, x_6, x_7, x_8, x_247);
lean_dec(x_248);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_255 = x_252;
} else {
 lean_dec_ref(x_252);
 x_255 = lean_box(0);
}
x_256 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
x_257 = l_Lean_Name_mkStr4(x_86, x_87, x_164, x_256);
lean_inc(x_257);
x_258 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_257, x_7, x_254);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_unbox(x_259);
lean_dec(x_259);
if (x_260 == 0)
{
lean_object* x_261; 
lean_dec(x_257);
lean_dec(x_255);
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_88 = x_250;
x_89 = x_251;
x_90 = x_249;
x_91 = x_253;
x_92 = x_261;
goto block_163;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_258, 1);
lean_inc(x_262);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 x_263 = x_258;
} else {
 lean_dec_ref(x_258);
 x_263 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_253);
x_264 = l_Lean_Compiler_LCNF_ppCode(x_253, x_5, x_6, x_7, x_8, x_262);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_inc(x_10);
x_268 = l_Lean_MessageData_ofName(x_10);
if (lean_is_scalar(x_263)) {
 x_269 = lean_alloc_ctor(7, 2, 0);
} else {
 x_269 = x_263;
 lean_ctor_set_tag(x_269, 7);
}
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
if (lean_is_scalar(x_255)) {
 x_271 = lean_alloc_ctor(7, 2, 0);
} else {
 x_271 = x_255;
 lean_ctor_set_tag(x_271, 7);
}
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_270);
x_272 = l_Lean_MessageData_ofFormat(x_265);
x_273 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_267);
x_275 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_257, x_274, x_6, x_7, x_8, x_266);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_88 = x_250;
x_89 = x_251;
x_90 = x_249;
x_91 = x_253;
x_92 = x_276;
goto block_163;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_263);
lean_dec(x_257);
lean_dec(x_255);
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_277 = lean_ctor_get(x_264, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_264, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_279 = x_264;
} else {
 lean_dec_ref(x_264);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_164);
lean_dec(x_81);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_281 = !lean_is_exclusive(x_166);
if (x_281 == 0)
{
return x_166;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_166, 0);
x_283 = lean_ctor_get(x_166, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_166);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
block_304:
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_287 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
x_288 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
x_289 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__1___redArg(x_288, x_7, x_286);
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_unbox(x_290);
lean_dec(x_290);
if (x_291 == 0)
{
lean_object* x_292; 
lean_dec(x_1);
x_292 = lean_ctor_get(x_289, 1);
lean_inc(x_292);
lean_dec(x_289);
x_164 = x_287;
x_165 = x_292;
goto block_285;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_289, 1);
lean_inc(x_293);
lean_dec(x_289);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_294 = l_Lean_Compiler_LCNF_ppDecl(x_1, x_5, x_6, x_7, x_8, x_293);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
x_297 = l_Lean_MessageData_ofFormat(x_295);
x_298 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Simp_withInlining_check_spec__2___redArg(x_288, x_297, x_6, x_7, x_8, x_296);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_164 = x_287;
x_165 = x_299;
goto block_285;
}
else
{
uint8_t x_300; 
lean_dec(x_81);
lean_dec(x_80);
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
x_300 = !lean_is_exclusive(x_294);
if (x_300 == 0)
{
return x_294;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_294, 0);
x_302 = lean_ctor_get(x_294, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_294);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_81);
lean_dec(x_80);
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
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_84);
if (x_381 == 0)
{
return x_84;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_84, 0);
x_383 = lean_ctor_get(x_84, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_84);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
lean_object* x_385; lean_object* x_386; 
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
x_385 = lean_box(0);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_385);
lean_ctor_set(x_386, 1, x_9);
return x_386;
}
block_79:
{
lean_object* x_25; 
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_18);
x_25 = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(x_18, x_20, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_st_ref_get(x_19, x_27);
lean_dec(x_19);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*7);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_31 = !lean_is_exclusive(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_28, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_28, 0, x_33);
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_28);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_28, 0);
lean_dec(x_38);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_18);
x_40 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_40, 0, x_10);
lean_ctor_set(x_40, 1, x_11);
lean_ctor_set(x_40, 2, x_12);
lean_ctor_set(x_40, 3, x_13);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_17);
lean_ctor_set_uint8(x_40, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_40, sizeof(void*)*6 + 1, x_16);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_28, 0, x_41);
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_dec(x_28);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_18);
x_44 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_44, 0, x_10);
lean_ctor_set(x_44, 1, x_11);
lean_ctor_set(x_44, 2, x_12);
lean_ctor_set(x_44, 3, x_13);
lean_ctor_set(x_44, 4, x_43);
lean_ctor_set(x_44, 5, x_17);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_44, sizeof(void*)*6 + 1, x_16);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
}
}
else
{
lean_object* x_47; uint8_t x_48; 
lean_dec(x_19);
lean_dec(x_18);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec(x_25);
x_48 = !lean_is_exclusive(x_26);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_26, 0);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_51, 0, x_10);
lean_ctor_set(x_51, 1, x_11);
lean_ctor_set(x_51, 2, x_12);
lean_ctor_set(x_51, 3, x_13);
lean_ctor_set(x_51, 4, x_50);
lean_ctor_set(x_51, 5, x_17);
lean_ctor_set_uint8(x_51, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_51, sizeof(void*)*6 + 1, x_16);
x_52 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_51, x_20, x_21, x_22, x_23, x_47);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_ctor_set(x_26, 0, x_54);
lean_ctor_set(x_52, 0, x_26);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_52, 0);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_52);
lean_ctor_set(x_26, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_26);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_free_object(x_26);
x_58 = !lean_is_exclusive(x_52);
if (x_58 == 0)
{
return x_52;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_52, 0);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_52);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_26, 0);
lean_inc(x_62);
lean_dec(x_26);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_64, 0, x_10);
lean_ctor_set(x_64, 1, x_11);
lean_ctor_set(x_64, 2, x_12);
lean_ctor_set(x_64, 3, x_13);
lean_ctor_set(x_64, 4, x_63);
lean_ctor_set(x_64, 5, x_17);
lean_ctor_set_uint8(x_64, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_64, sizeof(void*)*6 + 1, x_16);
x_65 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_64, x_20, x_21, x_22, x_23, x_47);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_68 = x_65;
} else {
 lean_dec_ref(x_65);
 x_68 = lean_box(0);
}
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_66);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_65, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_73 = x_65;
} else {
 lean_dec_ref(x_65);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_75 = !lean_is_exclusive(x_25);
if (x_75 == 0)
{
return x_25;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_25, 0);
x_77 = lean_ctor_get(x_25, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_25);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__4;
x_5 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
lean_ctor_set(x_5, 6, x_1);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*7, x_6);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__6;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__8;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__5;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_box(0);
x_14 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__7;
lean_inc(x_2);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
x_16 = l_Lean_Compiler_LCNF_Decl_simp_go___closed__9;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_10);
lean_inc(x_1);
x_17 = l_Lean_Compiler_LCNF_Decl_simp_x3f(x_1, x_15, x_10, x_16, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_10, x_19);
lean_dec(x_10);
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
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(x_1, x_6, x_7);
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
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
lean_ctor_set_uint8(x_2, 0, x_16);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_2, 1, x_17);
x_18 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_18;
}
else
{
uint8_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_19 = lean_ctor_get_uint8(x_2, 2);
x_20 = lean_ctor_get_uint8(x_2, 3);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 0, 4);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, 0, x_23);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, 1, x_24);
lean_ctor_set_uint8(x_22, 2, x_19);
lean_ctor_set_uint8(x_22, 3, x_20);
x_25 = l_Lean_Compiler_LCNF_Decl_simp_go(x_1, x_22, x_3, x_4, x_5, x_6, x_13);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Decl_simp(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_simp___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object* x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_simp___lam__0), 7, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = l_Lean_Compiler_LCNF_simp___closed__0;
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
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_2 = l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(712u);
x_2 = l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp___hyg_712_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_4 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_712_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; 
x_2 = l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_3 = lean_box(1);
x_4 = l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_5 = lean_unbox(x_3);
x_6 = l_Lean_registerTraceClass(x_2, x_5, x_4, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_registerTraceClass(x_8, x_10, x_4, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
x_14 = lean_unbox(x_9);
x_15 = l_Lean_registerTraceClass(x_13, x_14, x_4, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp___hyg_712_;
x_18 = lean_unbox(x_9);
x_19 = l_Lean_registerTraceClass(x_17, x_18, x_4, x_16);
return x_19;
}
else
{
return x_15;
}
}
else
{
return x_11;
}
}
else
{
return x_6;
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
l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0);
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
l_Lean_Compiler_LCNF_Decl_simp_go___closed__0 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__0);
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
l_Lean_Compiler_LCNF_Decl_simp_go___closed__9 = _init_l_Lean_Compiler_LCNF_Decl_simp_go___closed__9();
lean_mark_persistent(l_Lean_Compiler_LCNF_Decl_simp_go___closed__9);
l_Lean_Compiler_LCNF_simp___closed__0 = _init_l_Lean_Compiler_LCNF_simp___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_simp___closed__0);
l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp___hyg_712_ = _init_l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp___hyg_712_();
lean_mark_persistent(l_Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp___hyg_712_);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp___hyg_712_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
