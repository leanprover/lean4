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
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
extern lean_object* l_Lean_instEmptyCollectionFVarIdHashSet;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_applyRenaming(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_size(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__6;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* l_Lean_Compiler_LCNF_ppCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l_Lean_Compiler_LCNF_simp___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* l_Lean_Compiler_LCNF_ppDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5;
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_simp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2;
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4;
static double l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0;
lean_object* l_Lean_Compiler_LCNF_Decl_reduceJpArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
static lean_object* l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_1, x_7, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static double _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_st_ref_get(x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_get(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_15);
lean_dec(x_10);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_dec(x_18);
x_19 = lean_st_ref_take(x_5, x_14);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 4);
lean_inc_ref(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_20, 4);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; double x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec_ref(x_17);
x_30 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2;
lean_inc(x_7);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_15);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_29);
lean_ctor_set(x_31, 3, x_7);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_31);
x_32 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3;
x_33 = 0;
x_34 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4;
x_35 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_float(x_35, sizeof(void*)*2, x_32);
lean_ctor_set_float(x_35, sizeof(void*)*2 + 8, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*2 + 16, x_33);
x_36 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5;
x_37 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_19);
lean_ctor_set(x_37, 2, x_36);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_37);
lean_ctor_set(x_13, 0, x_8);
x_38 = l_Lean_PersistentArray_push___redArg(x_28, x_13);
lean_ctor_set(x_21, 0, x_38);
x_39 = lean_st_ref_set(x_5, x_20, x_23);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint64_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; double x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_46 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_47 = lean_ctor_get(x_21, 0);
lean_inc(x_47);
lean_dec(x_21);
x_48 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec_ref(x_17);
x_49 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2;
lean_inc(x_7);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_15);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_50, 2, x_48);
lean_ctor_set(x_50, 3, x_7);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_50);
x_51 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3;
x_52 = 0;
x_53 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4;
x_54 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set_float(x_54, sizeof(void*)*2, x_51);
lean_ctor_set_float(x_54, sizeof(void*)*2 + 8, x_51);
lean_ctor_set_uint8(x_54, sizeof(void*)*2 + 16, x_52);
x_55 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5;
x_56 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_19);
lean_ctor_set(x_56, 2, x_55);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_56);
lean_ctor_set(x_13, 0, x_8);
x_57 = l_Lean_PersistentArray_push___redArg(x_47, x_13);
x_58 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set_uint64(x_58, sizeof(void*)*1, x_46);
lean_ctor_set(x_20, 4, x_58);
x_59 = lean_st_ref_set(x_5, x_20, x_23);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint64_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; double x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
x_66 = lean_ctor_get(x_20, 2);
x_67 = lean_ctor_get(x_20, 3);
x_68 = lean_ctor_get(x_20, 5);
x_69 = lean_ctor_get(x_20, 6);
x_70 = lean_ctor_get(x_20, 7);
x_71 = lean_ctor_get(x_20, 8);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_72 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_73 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_73);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_74 = x_21;
} else {
 lean_dec_ref(x_21);
 x_74 = lean_box(0);
}
x_75 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec_ref(x_17);
x_76 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2;
lean_inc(x_7);
x_77 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_77, 0, x_15);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_7);
lean_ctor_set_tag(x_19, 3);
lean_ctor_set(x_19, 1, x_2);
lean_ctor_set(x_19, 0, x_77);
x_78 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3;
x_79 = 0;
x_80 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4;
x_81 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_80);
lean_ctor_set_float(x_81, sizeof(void*)*2, x_78);
lean_ctor_set_float(x_81, sizeof(void*)*2 + 8, x_78);
lean_ctor_set_uint8(x_81, sizeof(void*)*2 + 16, x_79);
x_82 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5;
x_83 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_19);
lean_ctor_set(x_83, 2, x_82);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_83);
lean_ctor_set(x_13, 0, x_8);
x_84 = l_Lean_PersistentArray_push___redArg(x_73, x_13);
if (lean_is_scalar(x_74)) {
 x_85 = lean_alloc_ctor(0, 1, 8);
} else {
 x_85 = x_74;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set_uint64(x_85, sizeof(void*)*1, x_72);
x_86 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_86, 0, x_64);
lean_ctor_set(x_86, 1, x_65);
lean_ctor_set(x_86, 2, x_66);
lean_ctor_set(x_86, 3, x_67);
lean_ctor_set(x_86, 4, x_85);
lean_ctor_set(x_86, 5, x_68);
lean_ctor_set(x_86, 6, x_69);
lean_ctor_set(x_86, 7, x_70);
lean_ctor_set(x_86, 8, x_71);
x_87 = lean_st_ref_set(x_5, x_86, x_23);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
x_90 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint64_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; double x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_92 = lean_ctor_get(x_19, 1);
lean_inc(x_92);
lean_dec(x_19);
x_93 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_93);
x_94 = lean_ctor_get(x_20, 1);
lean_inc(x_94);
x_95 = lean_ctor_get(x_20, 2);
lean_inc_ref(x_95);
x_96 = lean_ctor_get(x_20, 3);
lean_inc_ref(x_96);
x_97 = lean_ctor_get(x_20, 5);
lean_inc_ref(x_97);
x_98 = lean_ctor_get(x_20, 6);
lean_inc_ref(x_98);
x_99 = lean_ctor_get(x_20, 7);
lean_inc_ref(x_99);
x_100 = lean_ctor_get(x_20, 8);
lean_inc_ref(x_100);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 lean_ctor_release(x_20, 2);
 lean_ctor_release(x_20, 3);
 lean_ctor_release(x_20, 4);
 lean_ctor_release(x_20, 5);
 lean_ctor_release(x_20, 6);
 lean_ctor_release(x_20, 7);
 lean_ctor_release(x_20, 8);
 x_101 = x_20;
} else {
 lean_dec_ref(x_20);
 x_101 = lean_box(0);
}
x_102 = lean_ctor_get_uint64(x_21, sizeof(void*)*1);
x_103 = lean_ctor_get(x_21, 0);
lean_inc_ref(x_103);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_104 = x_21;
} else {
 lean_dec_ref(x_21);
 x_104 = lean_box(0);
}
x_105 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17);
lean_dec_ref(x_17);
x_106 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2;
lean_inc(x_7);
x_107 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_107, 0, x_15);
lean_ctor_set(x_107, 1, x_106);
lean_ctor_set(x_107, 2, x_105);
lean_ctor_set(x_107, 3, x_7);
x_108 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_2);
x_109 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3;
x_110 = 0;
x_111 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4;
x_112 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_112, 1, x_111);
lean_ctor_set_float(x_112, sizeof(void*)*2, x_109);
lean_ctor_set_float(x_112, sizeof(void*)*2 + 8, x_109);
lean_ctor_set_uint8(x_112, sizeof(void*)*2 + 16, x_110);
x_113 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5;
x_114 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_108);
lean_ctor_set(x_114, 2, x_113);
lean_inc(x_8);
lean_ctor_set(x_13, 1, x_114);
lean_ctor_set(x_13, 0, x_8);
x_115 = l_Lean_PersistentArray_push___redArg(x_103, x_13);
if (lean_is_scalar(x_104)) {
 x_116 = lean_alloc_ctor(0, 1, 8);
} else {
 x_116 = x_104;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set_uint64(x_116, sizeof(void*)*1, x_102);
if (lean_is_scalar(x_101)) {
 x_117 = lean_alloc_ctor(0, 9, 0);
} else {
 x_117 = x_101;
}
lean_ctor_set(x_117, 0, x_93);
lean_ctor_set(x_117, 1, x_94);
lean_ctor_set(x_117, 2, x_95);
lean_ctor_set(x_117, 3, x_96);
lean_ctor_set(x_117, 4, x_116);
lean_ctor_set(x_117, 5, x_97);
lean_ctor_set(x_117, 6, x_98);
lean_ctor_set(x_117, 7, x_99);
lean_ctor_set(x_117, 8, x_100);
x_118 = lean_st_ref_set(x_5, x_117, x_92);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = lean_box(0);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
return x_122;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint64_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; double x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_123 = lean_ctor_get(x_13, 0);
lean_inc(x_123);
lean_dec(x_13);
x_124 = lean_st_ref_take(x_5, x_14);
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 4);
lean_inc_ref(x_126);
x_127 = lean_ctor_get(x_124, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_128 = x_124;
} else {
 lean_dec_ref(x_124);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_125, 0);
lean_inc_ref(x_129);
x_130 = lean_ctor_get(x_125, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_125, 2);
lean_inc_ref(x_131);
x_132 = lean_ctor_get(x_125, 3);
lean_inc_ref(x_132);
x_133 = lean_ctor_get(x_125, 5);
lean_inc_ref(x_133);
x_134 = lean_ctor_get(x_125, 6);
lean_inc_ref(x_134);
x_135 = lean_ctor_get(x_125, 7);
lean_inc_ref(x_135);
x_136 = lean_ctor_get(x_125, 8);
lean_inc_ref(x_136);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 lean_ctor_release(x_125, 2);
 lean_ctor_release(x_125, 3);
 lean_ctor_release(x_125, 4);
 lean_ctor_release(x_125, 5);
 lean_ctor_release(x_125, 6);
 lean_ctor_release(x_125, 7);
 lean_ctor_release(x_125, 8);
 x_137 = x_125;
} else {
 lean_dec_ref(x_125);
 x_137 = lean_box(0);
}
x_138 = lean_ctor_get_uint64(x_126, sizeof(void*)*1);
x_139 = lean_ctor_get(x_126, 0);
lean_inc_ref(x_139);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 x_140 = x_126;
} else {
 lean_dec_ref(x_126);
 x_140 = lean_box(0);
}
x_141 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_123);
lean_dec_ref(x_123);
x_142 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2;
lean_inc(x_7);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_15);
lean_ctor_set(x_143, 1, x_142);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_7);
if (lean_is_scalar(x_128)) {
 x_144 = lean_alloc_ctor(3, 2, 0);
} else {
 x_144 = x_128;
 lean_ctor_set_tag(x_144, 3);
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_2);
x_145 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3;
x_146 = 0;
x_147 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4;
x_148 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_148, 0, x_1);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set_float(x_148, sizeof(void*)*2, x_145);
lean_ctor_set_float(x_148, sizeof(void*)*2 + 8, x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*2 + 16, x_146);
x_149 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5;
x_150 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_144);
lean_ctor_set(x_150, 2, x_149);
lean_inc(x_8);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_8);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_PersistentArray_push___redArg(x_139, x_151);
if (lean_is_scalar(x_140)) {
 x_153 = lean_alloc_ctor(0, 1, 8);
} else {
 x_153 = x_140;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set_uint64(x_153, sizeof(void*)*1, x_138);
if (lean_is_scalar(x_137)) {
 x_154 = lean_alloc_ctor(0, 9, 0);
} else {
 x_154 = x_137;
}
lean_ctor_set(x_154, 0, x_129);
lean_ctor_set(x_154, 1, x_130);
lean_ctor_set(x_154, 2, x_131);
lean_ctor_set(x_154, 3, x_132);
lean_ctor_set(x_154, 4, x_153);
lean_ctor_set(x_154, 5, x_133);
lean_ctor_set(x_154, 6, x_134);
lean_ctor_set(x_154, 7, x_135);
lean_ctor_set(x_154, 8, x_136);
x_155 = lean_st_ref_set(x_5, x_154, x_127);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10);
return x_11;
}
}
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
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", size: ", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", # visited: ", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", # inline: ", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", # inline local: ", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("new", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" :=\n", 4, 4);
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
x_1 = lean_mk_string_unchecked("step", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inline", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("info", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_4 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23() {
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
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_14);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_17 = lean_ctor_get(x_1, 5);
lean_inc(x_17);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_80);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_81 = x_14;
} else {
 lean_dec_ref(x_14);
 x_81 = lean_box(0);
}
x_82 = 0;
lean_inc_ref(x_80);
x_83 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_80, x_82, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_163; lean_object* x_164; lean_object* x_267; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_86 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_286 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20;
x_287 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_286, x_7, x_84);
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_unbox(x_288);
lean_dec(x_288);
if (x_289 == 0)
{
lean_object* x_290; 
x_290 = lean_ctor_get(x_287, 1);
lean_inc(x_290);
lean_dec_ref(x_287);
x_267 = x_290;
goto block_285;
}
else
{
uint8_t x_291; 
x_291 = !lean_is_exclusive(x_287);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_292 = lean_ctor_get(x_287, 1);
x_293 = lean_ctor_get(x_287, 0);
lean_dec(x_293);
x_294 = lean_st_ref_get(x_3, x_292);
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_294, 0);
x_297 = lean_ctor_get(x_294, 1);
x_298 = lean_ctor_get(x_296, 3);
lean_inc_ref(x_298);
lean_dec(x_296);
x_299 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_298, x_5, x_6, x_7, x_8, x_297);
lean_dec_ref(x_298);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec_ref(x_299);
x_302 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
lean_inc(x_10);
x_303 = l_Lean_MessageData_ofName(x_10);
lean_ctor_set_tag(x_294, 7);
lean_ctor_set(x_294, 1, x_303);
lean_ctor_set(x_294, 0, x_302);
x_304 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
lean_ctor_set_tag(x_287, 7);
lean_ctor_set(x_287, 1, x_304);
lean_ctor_set(x_287, 0, x_294);
x_305 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
x_306 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_300);
x_307 = l_Lean_MessageData_ofFormat(x_306);
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_287);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_302);
x_310 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_286, x_309, x_6, x_7, x_8, x_301);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
lean_dec_ref(x_310);
x_267 = x_311;
goto block_285;
}
else
{
uint8_t x_312; 
lean_free_object(x_294);
lean_free_object(x_287);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_312 = !lean_is_exclusive(x_299);
if (x_312 == 0)
{
return x_299;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_299, 0);
x_314 = lean_ctor_get(x_299, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_299);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_316 = lean_ctor_get(x_294, 0);
x_317 = lean_ctor_get(x_294, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_294);
x_318 = lean_ctor_get(x_316, 3);
lean_inc_ref(x_318);
lean_dec(x_316);
x_319 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_318, x_5, x_6, x_7, x_8, x_317);
lean_dec_ref(x_318);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec_ref(x_319);
x_322 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
lean_inc(x_10);
x_323 = l_Lean_MessageData_ofName(x_10);
x_324 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
x_325 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
lean_ctor_set_tag(x_287, 7);
lean_ctor_set(x_287, 1, x_325);
lean_ctor_set(x_287, 0, x_324);
x_326 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
x_327 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_327, 0, x_326);
lean_ctor_set(x_327, 1, x_320);
x_328 = l_Lean_MessageData_ofFormat(x_327);
x_329 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_329, 0, x_287);
lean_ctor_set(x_329, 1, x_328);
x_330 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_322);
x_331 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_286, x_330, x_6, x_7, x_8, x_321);
x_332 = lean_ctor_get(x_331, 1);
lean_inc(x_332);
lean_dec_ref(x_331);
x_267 = x_332;
goto block_285;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_free_object(x_287);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_333 = lean_ctor_get(x_319, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_319, 1);
lean_inc(x_334);
if (lean_is_exclusive(x_319)) {
 lean_ctor_release(x_319, 0);
 lean_ctor_release(x_319, 1);
 x_335 = x_319;
} else {
 lean_dec_ref(x_319);
 x_335 = lean_box(0);
}
if (lean_is_scalar(x_335)) {
 x_336 = lean_alloc_ctor(1, 2, 0);
} else {
 x_336 = x_335;
}
lean_ctor_set(x_336, 0, x_333);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_337 = lean_ctor_get(x_287, 1);
lean_inc(x_337);
lean_dec(x_287);
x_338 = lean_st_ref_get(x_3, x_337);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 x_341 = x_338;
} else {
 lean_dec_ref(x_338);
 x_341 = lean_box(0);
}
x_342 = lean_ctor_get(x_339, 3);
lean_inc_ref(x_342);
lean_dec(x_339);
x_343 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_342, x_5, x_6, x_7, x_8, x_340);
lean_dec_ref(x_342);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_343, 1);
lean_inc(x_345);
lean_dec_ref(x_343);
x_346 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
lean_inc(x_10);
x_347 = l_Lean_MessageData_ofName(x_10);
if (lean_is_scalar(x_341)) {
 x_348 = lean_alloc_ctor(7, 2, 0);
} else {
 x_348 = x_341;
 lean_ctor_set_tag(x_348, 7);
}
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
x_349 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
x_350 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_350, 0, x_348);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
x_352 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_344);
x_353 = l_Lean_MessageData_ofFormat(x_352);
x_354 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_354, 0, x_350);
lean_ctor_set(x_354, 1, x_353);
x_355 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_346);
x_356 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_286, x_355, x_6, x_7, x_8, x_345);
x_357 = lean_ctor_get(x_356, 1);
lean_inc(x_357);
lean_dec_ref(x_356);
x_267 = x_357;
goto block_285;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; 
lean_dec(x_341);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_358 = lean_ctor_get(x_343, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_343, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 x_360 = x_343;
} else {
 lean_dec_ref(x_343);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_360)) {
 x_361 = lean_alloc_ctor(1, 2, 0);
} else {
 x_361 = x_360;
}
lean_ctor_set(x_361, 0, x_358);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
}
block_162:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_92 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
x_93 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_92, x_7, x_91);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_81);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec_ref(x_93);
x_18 = x_90;
x_19 = x_3;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_96;
goto block_79;
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_98 = lean_ctor_get(x_93, 1);
x_99 = lean_ctor_get(x_93, 0);
lean_dec(x_99);
x_100 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
lean_inc(x_10);
x_101 = l_Lean_MessageData_ofName(x_10);
lean_ctor_set_tag(x_93, 7);
lean_ctor_set(x_93, 1, x_101);
lean_ctor_set(x_93, 0, x_100);
x_102 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6;
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_Compiler_LCNF_Code_size(x_90);
x_105 = l_Nat_reprFast(x_104);
if (lean_is_scalar(x_81)) {
 x_106 = lean_alloc_ctor(3, 1, 0);
} else {
 x_106 = x_81;
 lean_ctor_set_tag(x_106, 3);
}
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Lean_MessageData_ofFormat(x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_107);
x_109 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Nat_reprFast(x_88);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_MessageData_ofFormat(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10;
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Nat_reprFast(x_89);
x_118 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = l_Lean_MessageData_ofFormat(x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Nat_reprFast(x_87);
x_124 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Lean_MessageData_ofFormat(x_124);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_100);
x_128 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_92, x_127, x_6, x_7, x_8, x_98);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec_ref(x_128);
x_18 = x_90;
x_19 = x_3;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_129;
goto block_79;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_130 = lean_ctor_get(x_93, 1);
lean_inc(x_130);
lean_dec(x_93);
x_131 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
lean_inc(x_10);
x_132 = l_Lean_MessageData_ofName(x_10);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6;
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_Compiler_LCNF_Code_size(x_90);
x_137 = l_Nat_reprFast(x_136);
if (lean_is_scalar(x_81)) {
 x_138 = lean_alloc_ctor(3, 1, 0);
} else {
 x_138 = x_81;
 lean_ctor_set_tag(x_138, 3);
}
lean_ctor_set(x_138, 0, x_137);
x_139 = l_Lean_MessageData_ofFormat(x_138);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_135);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8;
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Nat_reprFast(x_88);
x_144 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_144, 0, x_143);
x_145 = l_Lean_MessageData_ofFormat(x_144);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_142);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10;
x_148 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
x_149 = l_Nat_reprFast(x_89);
x_150 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_150, 0, x_149);
x_151 = l_Lean_MessageData_ofFormat(x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Nat_reprFast(x_87);
x_156 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_156, 0, x_155);
x_157 = l_Lean_MessageData_ofFormat(x_156);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_131);
x_160 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_92, x_159, x_6, x_7, x_8, x_130);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec_ref(x_160);
x_18 = x_90;
x_19 = x_3;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_161;
goto block_79;
}
}
}
block_266:
{
lean_object* x_165; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_165 = l_Lean_Compiler_LCNF_Simp_simp(x_80, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_164);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
lean_dec_ref(x_165);
x_168 = lean_st_ref_get(x_3, x_167);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = lean_ctor_get(x_168, 1);
x_172 = lean_ctor_get(x_170, 2);
lean_inc(x_172);
x_173 = lean_ctor_get(x_170, 4);
lean_inc(x_173);
x_174 = lean_ctor_get(x_170, 5);
lean_inc(x_174);
x_175 = lean_ctor_get(x_170, 6);
lean_inc(x_175);
lean_dec(x_170);
x_176 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_166, x_172, x_5, x_6, x_7, x_8, x_171);
lean_dec(x_172);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec_ref(x_176);
x_179 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_180 = l_Lean_Name_mkStr4(x_85, x_86, x_163, x_179);
lean_inc(x_180);
x_181 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_180, x_7, x_178);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_unbox(x_182);
lean_dec(x_182);
if (x_183 == 0)
{
lean_object* x_184; 
lean_dec(x_180);
lean_free_object(x_168);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
lean_dec_ref(x_181);
x_87 = x_175;
x_88 = x_173;
x_89 = x_174;
x_90 = x_177;
x_91 = x_184;
goto block_162;
}
else
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_181);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_181, 1);
x_187 = lean_ctor_get(x_181, 0);
lean_dec(x_187);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_177);
x_188 = l_Lean_Compiler_LCNF_ppCode(x_177, x_5, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec_ref(x_188);
x_191 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
lean_inc(x_10);
x_192 = l_Lean_MessageData_ofName(x_10);
lean_ctor_set_tag(x_181, 7);
lean_ctor_set(x_181, 1, x_192);
lean_ctor_set(x_181, 0, x_191);
x_193 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
lean_ctor_set_tag(x_168, 7);
lean_ctor_set(x_168, 1, x_193);
lean_ctor_set(x_168, 0, x_181);
x_194 = l_Lean_MessageData_ofFormat(x_189);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_168);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_191);
x_197 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_180, x_196, x_6, x_7, x_8, x_190);
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
lean_dec_ref(x_197);
x_87 = x_175;
x_88 = x_173;
x_89 = x_174;
x_90 = x_177;
x_91 = x_198;
goto block_162;
}
else
{
uint8_t x_199; 
lean_free_object(x_181);
lean_dec(x_180);
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_free_object(x_168);
lean_dec(x_81);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_199 = !lean_is_exclusive(x_188);
if (x_199 == 0)
{
return x_188;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_188, 0);
x_201 = lean_ctor_get(x_188, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_188);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_181, 1);
lean_inc(x_203);
lean_dec(x_181);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_177);
x_204 = l_Lean_Compiler_LCNF_ppCode(x_177, x_5, x_6, x_7, x_8, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec_ref(x_204);
x_207 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
lean_inc(x_10);
x_208 = l_Lean_MessageData_ofName(x_10);
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
lean_ctor_set_tag(x_168, 7);
lean_ctor_set(x_168, 1, x_210);
lean_ctor_set(x_168, 0, x_209);
x_211 = l_Lean_MessageData_ofFormat(x_205);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_168);
lean_ctor_set(x_212, 1, x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_207);
x_214 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_180, x_213, x_6, x_7, x_8, x_206);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec_ref(x_214);
x_87 = x_175;
x_88 = x_173;
x_89 = x_174;
x_90 = x_177;
x_91 = x_215;
goto block_162;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_180);
lean_dec(x_177);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_free_object(x_168);
lean_dec(x_81);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_216 = lean_ctor_get(x_204, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_204, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_218 = x_204;
} else {
 lean_dec_ref(x_204);
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
uint8_t x_220; 
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
lean_free_object(x_168);
lean_dec_ref(x_163);
lean_dec(x_81);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_220 = !lean_is_exclusive(x_176);
if (x_220 == 0)
{
return x_176;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_176, 0);
x_222 = lean_ctor_get(x_176, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_176);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_168, 0);
x_225 = lean_ctor_get(x_168, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_168);
x_226 = lean_ctor_get(x_224, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_224, 4);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 5);
lean_inc(x_228);
x_229 = lean_ctor_get(x_224, 6);
lean_inc(x_229);
lean_dec(x_224);
x_230 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_166, x_226, x_5, x_6, x_7, x_8, x_225);
lean_dec(x_226);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec_ref(x_230);
x_233 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_234 = l_Lean_Name_mkStr4(x_85, x_86, x_163, x_233);
lean_inc(x_234);
x_235 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_234, x_7, x_232);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_unbox(x_236);
lean_dec(x_236);
if (x_237 == 0)
{
lean_object* x_238; 
lean_dec(x_234);
x_238 = lean_ctor_get(x_235, 1);
lean_inc(x_238);
lean_dec_ref(x_235);
x_87 = x_229;
x_88 = x_227;
x_89 = x_228;
x_90 = x_231;
x_91 = x_238;
goto block_162;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_235, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_240 = x_235;
} else {
 lean_dec_ref(x_235);
 x_240 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_231);
x_241 = l_Lean_Compiler_LCNF_ppCode(x_231, x_5, x_6, x_7, x_8, x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
lean_dec_ref(x_241);
x_244 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4;
lean_inc(x_10);
x_245 = l_Lean_MessageData_ofName(x_10);
if (lean_is_scalar(x_240)) {
 x_246 = lean_alloc_ctor(7, 2, 0);
} else {
 x_246 = x_240;
 lean_ctor_set_tag(x_246, 7);
}
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
x_248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
x_249 = l_Lean_MessageData_ofFormat(x_242);
x_250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_244);
x_252 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_234, x_251, x_6, x_7, x_8, x_243);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec_ref(x_252);
x_87 = x_229;
x_88 = x_227;
x_89 = x_228;
x_90 = x_231;
x_91 = x_253;
goto block_162;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_240);
lean_dec(x_234);
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_81);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_254 = lean_ctor_get(x_241, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_241, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_256 = x_241;
} else {
 lean_dec_ref(x_241);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec_ref(x_163);
lean_dec(x_81);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_258 = lean_ctor_get(x_230, 0);
lean_inc(x_258);
x_259 = lean_ctor_get(x_230, 1);
lean_inc(x_259);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 lean_ctor_release(x_230, 1);
 x_260 = x_230;
} else {
 lean_dec_ref(x_230);
 x_260 = lean_box(0);
}
if (lean_is_scalar(x_260)) {
 x_261 = lean_alloc_ctor(1, 2, 0);
} else {
 x_261 = x_260;
}
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_259);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec_ref(x_163);
lean_dec(x_81);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
x_262 = !lean_is_exclusive(x_165);
if (x_262 == 0)
{
return x_165;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_165, 0);
x_264 = lean_ctor_get(x_165, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_165);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
block_285:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_268 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
x_269 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
x_270 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_269, x_7, x_267);
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_unbox(x_271);
lean_dec(x_271);
if (x_272 == 0)
{
lean_object* x_273; 
lean_dec_ref(x_1);
x_273 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
lean_dec_ref(x_270);
x_163 = x_268;
x_164 = x_273;
goto block_266;
}
else
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_270, 1);
lean_inc(x_274);
lean_dec_ref(x_270);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_275 = l_Lean_Compiler_LCNF_ppDecl(x_1, x_5, x_6, x_7, x_8, x_274);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
lean_dec_ref(x_275);
x_278 = l_Lean_MessageData_ofFormat(x_276);
x_279 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_269, x_278, x_6, x_7, x_8, x_277);
x_280 = lean_ctor_get(x_279, 1);
lean_inc(x_280);
lean_dec_ref(x_279);
x_163 = x_268;
x_164 = x_280;
goto block_266;
}
else
{
uint8_t x_281; 
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_281 = !lean_is_exclusive(x_275);
if (x_281 == 0)
{
return x_275;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_275, 0);
x_283 = lean_ctor_get(x_275, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_275);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
}
}
else
{
uint8_t x_362; 
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_362 = !lean_is_exclusive(x_83);
if (x_362 == 0)
{
return x_83;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_363 = lean_ctor_get(x_83, 0);
x_364 = lean_ctor_get(x_83, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_83);
x_365 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_365, 0, x_363);
lean_ctor_set(x_365, 1, x_364);
return x_365;
}
}
}
else
{
lean_object* x_366; lean_object* x_367; 
lean_dec(x_17);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_366 = lean_box(0);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_9);
return x_367;
}
block_79:
{
lean_object* x_25; 
lean_inc(x_23);
lean_inc_ref(x_22);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc_ref(x_18);
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
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_st_ref_get(x_19, x_27);
lean_dec(x_19);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_29, sizeof(void*)*7);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
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
lean_dec_ref(x_18);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_dec_ref(x_25);
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
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_box(1);
x_4 = l_Lean_instEmptyCollectionFVarIdHashSet;
x_5 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4;
x_6 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_5);
lean_ctor_set(x_6, 4, x_1);
lean_ctor_set(x_6, 5, x_1);
lean_ctor_set(x_6, 6, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*7, x_2);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1;
x_2 = lean_box(1);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5;
x_9 = lean_st_mk_ref(x_8, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_box(0);
x_14 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1;
lean_inc_ref(x_2);
lean_inc(x_12);
x_15 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_13);
lean_ctor_set(x_15, 3, x_14);
x_16 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__6;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_10);
lean_inc_ref(x_1);
x_17 = l_Lean_Compiler_LCNF_Decl_simp_x3f(x_1, x_15, x_10, x_16, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = lean_st_ref_get(x_10, x_19);
lean_dec(x_10);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_21; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
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
lean_dec_ref(x_1);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec_ref(x_20);
x_26 = lean_ctor_get(x_18, 0);
lean_inc(x_26);
lean_dec_ref(x_18);
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
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
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
lean_object* x_8; 
lean_inc_ref(x_1);
x_8 = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(x_1, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec_ref(x_8);
x_12 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec_ref(x_8);
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
lean_ctor_set_uint8(x_2, 0, x_15);
lean_ctor_set_uint8(x_2, 1, x_15);
x_16 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(x_1, x_2, x_3, x_4, x_5, x_6, x_13);
return x_16;
}
else
{
uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get_uint8(x_2, 2);
x_18 = lean_ctor_get_uint8(x_2, 3);
lean_dec(x_2);
x_19 = 0;
x_20 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_20, 0, x_19);
lean_ctor_set_uint8(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, 2, x_17);
lean_ctor_set_uint8(x_20, 3, x_18);
x_21 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(x_1, x_20, x_3, x_4, x_5, x_6, x_13);
return x_21;
}
}
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_22 = !lean_is_exclusive(x_8);
if (x_22 == 0)
{
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_8, 0);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_8);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
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
x_5 = l_Lean_Compiler_LCNF_simp(x_1, x_2, x_4);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_private", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LCNF", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Simp", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(1672504145u);
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hygCtx", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_4 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_3 = 1;
x_4 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec_ref(x_5);
x_7 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
x_8 = 0;
x_9 = l_Lean_registerTraceClass(x_7, x_8, x_4, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
x_12 = l_Lean_registerTraceClass(x_11, x_8, x_4, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
x_15 = l_Lean_registerTraceClass(x_14, x_8, x_4, x_13);
return x_15;
}
else
{
return x_12;
}
}
else
{
return x_9;
}
}
else
{
return x_5;
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
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__0);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__1);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__2);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__3();
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__4);
l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5 = _init_l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg___closed__5);
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
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__6 = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__6();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__6);
l_Lean_Compiler_LCNF_simp___closed__0 = _init_l_Lean_Compiler_LCNF_simp___closed__0();
lean_mark_persistent(l_Lean_Compiler_LCNF_simp___closed__0);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_ = _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
lean_mark_persistent(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_);
if (builtin) {res = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
