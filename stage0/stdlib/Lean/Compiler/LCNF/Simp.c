// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp
// Imports: public import Lean.Compiler.LCNF.ReduceJpArity public import Lean.Compiler.LCNF.Simp.Basic public import Lean.Compiler.LCNF.Simp.FunDeclInfo public import Lean.Compiler.LCNF.Simp.JpCases public import Lean.Compiler.LCNF.Simp.Config public import Lean.Compiler.LCNF.Simp.InlineCandidate public import Lean.Compiler.LCNF.Simp.SimpM public import Lean.Compiler.LCNF.Simp.Main public import Lean.Compiler.LCNF.Simp.InlineProj public import Lean.Compiler.LCNF.Simp.DefaultAlt public import Lean.Compiler.LCNF.Simp.SimpValue public import Lean.Compiler.LCNF.Simp.Used
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", size: ", 8, 8);
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
x_1 = lean_mk_string_unchecked(", # visited: ", 13, 13);
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
x_1 = lean_mk_string_unchecked(", # inline: ", 12, 12);
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
x_1 = lean_mk_string_unchecked(", # inline local: ", 18, 18);
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
x_1 = lean_mk_string_unchecked("new", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" :=\n", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("step", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inline", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("info", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17;
x_3 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_4 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(":", 1, 1);
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
lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_85 = x_14;
} else {
 lean_dec_ref(x_14);
 x_85 = lean_box(0);
}
x_86 = 0;
lean_inc_ref(x_84);
x_87 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_84, x_86, x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_161; lean_object* x_162; lean_object* x_256; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
x_90 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
x_275 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
x_276 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_275, x_7, x_88);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_unbox(x_277);
lean_dec(x_277);
if (x_278 == 0)
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_dec_ref(x_276);
x_256 = x_279;
goto block_274;
}
else
{
uint8_t x_280; 
x_280 = !lean_is_exclusive(x_276);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_281 = lean_ctor_get(x_276, 1);
x_282 = lean_ctor_get(x_276, 0);
lean_dec(x_282);
x_283 = lean_st_ref_get(x_3, x_281);
x_284 = !lean_is_exclusive(x_283);
if (x_284 == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_283, 0);
x_286 = lean_ctor_get(x_283, 1);
x_287 = lean_ctor_get(x_285, 3);
lean_inc_ref(x_287);
lean_dec(x_285);
x_288 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_287, x_5, x_6, x_7, x_8, x_286);
lean_dec_ref(x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec_ref(x_288);
lean_inc(x_10);
x_291 = l_Lean_MessageData_ofName(x_10);
x_292 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
lean_ctor_set_tag(x_283, 7);
lean_ctor_set(x_283, 1, x_292);
lean_ctor_set(x_283, 0, x_291);
x_293 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
lean_ctor_set_tag(x_276, 4);
lean_ctor_set(x_276, 1, x_289);
lean_ctor_set(x_276, 0, x_293);
x_294 = l_Lean_MessageData_ofFormat(x_276);
x_295 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_295, 0, x_283);
lean_ctor_set(x_295, 1, x_294);
x_296 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_275, x_295, x_6, x_7, x_8, x_290);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec_ref(x_296);
x_256 = x_297;
goto block_274;
}
else
{
uint8_t x_298; 
lean_free_object(x_283);
lean_free_object(x_276);
lean_dec(x_85);
lean_dec_ref(x_84);
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
x_298 = !lean_is_exclusive(x_288);
if (x_298 == 0)
{
return x_288;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_288, 0);
x_300 = lean_ctor_get(x_288, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_288);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_302 = lean_ctor_get(x_283, 0);
x_303 = lean_ctor_get(x_283, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_283);
x_304 = lean_ctor_get(x_302, 3);
lean_inc_ref(x_304);
lean_dec(x_302);
x_305 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_304, x_5, x_6, x_7, x_8, x_303);
lean_dec_ref(x_304);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec_ref(x_305);
lean_inc(x_10);
x_308 = l_Lean_MessageData_ofName(x_10);
x_309 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
x_310 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
x_311 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
lean_ctor_set_tag(x_276, 4);
lean_ctor_set(x_276, 1, x_306);
lean_ctor_set(x_276, 0, x_311);
x_312 = l_Lean_MessageData_ofFormat(x_276);
x_313 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_313, 0, x_310);
lean_ctor_set(x_313, 1, x_312);
x_314 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_275, x_313, x_6, x_7, x_8, x_307);
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec_ref(x_314);
x_256 = x_315;
goto block_274;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_free_object(x_276);
lean_dec(x_85);
lean_dec_ref(x_84);
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
x_316 = lean_ctor_get(x_305, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_305, 1);
lean_inc(x_317);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 lean_ctor_release(x_305, 1);
 x_318 = x_305;
} else {
 lean_dec_ref(x_305);
 x_318 = lean_box(0);
}
if (lean_is_scalar(x_318)) {
 x_319 = lean_alloc_ctor(1, 2, 0);
} else {
 x_319 = x_318;
}
lean_ctor_set(x_319, 0, x_316);
lean_ctor_set(x_319, 1, x_317);
return x_319;
}
}
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_320 = lean_ctor_get(x_276, 1);
lean_inc(x_320);
lean_dec(x_276);
x_321 = lean_st_ref_get(x_3, x_320);
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
if (lean_is_exclusive(x_321)) {
 lean_ctor_release(x_321, 0);
 lean_ctor_release(x_321, 1);
 x_324 = x_321;
} else {
 lean_dec_ref(x_321);
 x_324 = lean_box(0);
}
x_325 = lean_ctor_get(x_322, 3);
lean_inc_ref(x_325);
lean_dec(x_322);
x_326 = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(x_325, x_5, x_6, x_7, x_8, x_323);
lean_dec_ref(x_325);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
lean_dec_ref(x_326);
lean_inc(x_10);
x_329 = l_Lean_MessageData_ofName(x_10);
x_330 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21;
if (lean_is_scalar(x_324)) {
 x_331 = lean_alloc_ctor(7, 2, 0);
} else {
 x_331 = x_324;
 lean_ctor_set_tag(x_331, 7);
}
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
x_332 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22;
x_333 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_327);
x_334 = l_Lean_MessageData_ofFormat(x_333);
x_335 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_335, 0, x_331);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_275, x_335, x_6, x_7, x_8, x_328);
x_337 = lean_ctor_get(x_336, 1);
lean_inc(x_337);
lean_dec_ref(x_336);
x_256 = x_337;
goto block_274;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_324);
lean_dec(x_85);
lean_dec_ref(x_84);
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
x_338 = lean_ctor_get(x_326, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_326, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_340 = x_326;
} else {
 lean_dec_ref(x_326);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
}
}
block_160:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
x_97 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_96, x_7, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_85);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec_ref(x_97);
x_18 = x_93;
x_19 = x_3;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_100;
goto block_83;
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_97);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_102 = lean_ctor_get(x_97, 1);
x_103 = lean_ctor_get(x_97, 0);
lean_dec(x_103);
lean_inc(x_10);
x_104 = l_Lean_MessageData_ofName(x_10);
x_105 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
lean_ctor_set_tag(x_97, 7);
lean_ctor_set(x_97, 1, x_105);
lean_ctor_set(x_97, 0, x_104);
x_106 = l_Lean_Compiler_LCNF_Code_size(x_93);
x_107 = l_Nat_reprFast(x_106);
if (lean_is_scalar(x_85)) {
 x_108 = lean_alloc_ctor(3, 1, 0);
} else {
 x_108 = x_85;
 lean_ctor_set_tag(x_108, 3);
}
lean_ctor_set(x_108, 0, x_107);
x_109 = l_Lean_MessageData_ofFormat(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_97);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = l_Nat_reprFast(x_92);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Lean_MessageData_ofFormat(x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_112);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Nat_reprFast(x_94);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_MessageData_ofFormat(x_120);
x_122 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_122, 0, x_118);
lean_ctor_set(x_122, 1, x_121);
x_123 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Nat_reprFast(x_91);
x_126 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_126, 0, x_125);
x_127 = l_Lean_MessageData_ofFormat(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_124);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_96, x_128, x_6, x_7, x_8, x_102);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec_ref(x_129);
x_18 = x_93;
x_19 = x_3;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_130;
goto block_83;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_131 = lean_ctor_get(x_97, 1);
lean_inc(x_131);
lean_dec(x_97);
lean_inc(x_10);
x_132 = l_Lean_MessageData_ofName(x_10);
x_133 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Compiler_LCNF_Code_size(x_93);
x_136 = l_Nat_reprFast(x_135);
if (lean_is_scalar(x_85)) {
 x_137 = lean_alloc_ctor(3, 1, 0);
} else {
 x_137 = x_85;
 lean_ctor_set_tag(x_137, 3);
}
lean_ctor_set(x_137, 0, x_136);
x_138 = l_Lean_MessageData_ofFormat(x_137);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
x_141 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_142 = l_Nat_reprFast(x_92);
x_143 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = l_Lean_MessageData_ofFormat(x_143);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_144);
x_146 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Nat_reprFast(x_94);
x_149 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = l_Lean_MessageData_ofFormat(x_149);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_147);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Nat_reprFast(x_91);
x_155 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_155, 0, x_154);
x_156 = l_Lean_MessageData_ofFormat(x_155);
x_157 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_96, x_157, x_6, x_7, x_8, x_131);
x_159 = lean_ctor_get(x_158, 1);
lean_inc(x_159);
lean_dec_ref(x_158);
x_18 = x_93;
x_19 = x_3;
x_20 = x_5;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_159;
goto block_83;
}
}
}
block_255:
{
lean_object* x_163; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_3);
x_163 = l_Lean_Compiler_LCNF_Simp_simp(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec_ref(x_163);
x_166 = lean_st_ref_get(x_3, x_165);
x_167 = !lean_is_exclusive(x_166);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_168 = lean_ctor_get(x_166, 0);
x_169 = lean_ctor_get(x_166, 1);
x_170 = lean_ctor_get(x_168, 2);
lean_inc(x_170);
x_171 = lean_ctor_get(x_168, 4);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 5);
lean_inc(x_172);
x_173 = lean_ctor_get(x_168, 6);
lean_inc(x_173);
lean_dec(x_168);
x_174 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_164, x_170, x_5, x_6, x_7, x_8, x_169);
lean_dec(x_170);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
lean_dec_ref(x_174);
x_177 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
x_178 = l_Lean_Name_mkStr4(x_89, x_90, x_161, x_177);
lean_inc(x_178);
x_179 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_178, x_7, x_176);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_unbox(x_180);
lean_dec(x_180);
if (x_181 == 0)
{
lean_object* x_182; 
lean_dec(x_178);
lean_free_object(x_166);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
lean_dec_ref(x_179);
x_91 = x_173;
x_92 = x_171;
x_93 = x_175;
x_94 = x_172;
x_95 = x_182;
goto block_160;
}
else
{
uint8_t x_183; 
x_183 = !lean_is_exclusive(x_179);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_179, 1);
x_185 = lean_ctor_get(x_179, 0);
lean_dec(x_185);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_175);
x_186 = l_Lean_Compiler_LCNF_ppCode(x_175, x_5, x_6, x_7, x_8, x_184);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec_ref(x_186);
lean_inc(x_10);
x_189 = l_Lean_MessageData_ofName(x_10);
x_190 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
lean_ctor_set_tag(x_179, 7);
lean_ctor_set(x_179, 1, x_190);
lean_ctor_set(x_179, 0, x_189);
x_191 = l_Lean_MessageData_ofFormat(x_187);
lean_ctor_set_tag(x_166, 7);
lean_ctor_set(x_166, 1, x_191);
lean_ctor_set(x_166, 0, x_179);
x_192 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_178, x_166, x_6, x_7, x_8, x_188);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
lean_dec_ref(x_192);
x_91 = x_173;
x_92 = x_171;
x_93 = x_175;
x_94 = x_172;
x_95 = x_193;
goto block_160;
}
else
{
uint8_t x_194; 
lean_free_object(x_179);
lean_dec(x_178);
lean_dec(x_175);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_free_object(x_166);
lean_dec(x_85);
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
x_194 = !lean_is_exclusive(x_186);
if (x_194 == 0)
{
return x_186;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_186, 0);
x_196 = lean_ctor_get(x_186, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_186);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_179, 1);
lean_inc(x_198);
lean_dec(x_179);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_175);
x_199 = l_Lean_Compiler_LCNF_ppCode(x_175, x_5, x_6, x_7, x_8, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec_ref(x_199);
lean_inc(x_10);
x_202 = l_Lean_MessageData_ofName(x_10);
x_203 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = l_Lean_MessageData_ofFormat(x_200);
lean_ctor_set_tag(x_166, 7);
lean_ctor_set(x_166, 1, x_205);
lean_ctor_set(x_166, 0, x_204);
x_206 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_178, x_166, x_6, x_7, x_8, x_201);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec_ref(x_206);
x_91 = x_173;
x_92 = x_171;
x_93 = x_175;
x_94 = x_172;
x_95 = x_207;
goto block_160;
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_178);
lean_dec(x_175);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_free_object(x_166);
lean_dec(x_85);
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
x_208 = lean_ctor_get(x_199, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_199, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_210 = x_199;
} else {
 lean_dec_ref(x_199);
 x_210 = lean_box(0);
}
if (lean_is_scalar(x_210)) {
 x_211 = lean_alloc_ctor(1, 2, 0);
} else {
 x_211 = x_210;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_209);
return x_211;
}
}
}
}
else
{
uint8_t x_212; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_free_object(x_166);
lean_dec_ref(x_161);
lean_dec(x_85);
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
x_212 = !lean_is_exclusive(x_174);
if (x_212 == 0)
{
return x_174;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_174, 0);
x_214 = lean_ctor_get(x_174, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_174);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_216 = lean_ctor_get(x_166, 0);
x_217 = lean_ctor_get(x_166, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_166);
x_218 = lean_ctor_get(x_216, 2);
lean_inc(x_218);
x_219 = lean_ctor_get(x_216, 4);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 5);
lean_inc(x_220);
x_221 = lean_ctor_get(x_216, 6);
lean_inc(x_221);
lean_dec(x_216);
x_222 = l_Lean_Compiler_LCNF_Code_applyRenaming(x_164, x_218, x_5, x_6, x_7, x_8, x_217);
lean_dec(x_218);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; uint8_t x_229; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec_ref(x_222);
x_225 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
x_226 = l_Lean_Name_mkStr4(x_89, x_90, x_161, x_225);
lean_inc(x_226);
x_227 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_226, x_7, x_224);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_unbox(x_228);
lean_dec(x_228);
if (x_229 == 0)
{
lean_object* x_230; 
lean_dec(x_226);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec_ref(x_227);
x_91 = x_221;
x_92 = x_219;
x_93 = x_223;
x_94 = x_220;
x_95 = x_230;
goto block_160;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_227, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 lean_ctor_release(x_227, 1);
 x_232 = x_227;
} else {
 lean_dec_ref(x_227);
 x_232 = lean_box(0);
}
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_223);
x_233 = l_Lean_Compiler_LCNF_ppCode(x_223, x_5, x_6, x_7, x_8, x_231);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec_ref(x_233);
lean_inc(x_10);
x_236 = l_Lean_MessageData_ofName(x_10);
x_237 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14;
if (lean_is_scalar(x_232)) {
 x_238 = lean_alloc_ctor(7, 2, 0);
} else {
 x_238 = x_232;
 lean_ctor_set_tag(x_238, 7);
}
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
x_239 = l_Lean_MessageData_ofFormat(x_234);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_226, x_240, x_6, x_7, x_8, x_235);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec_ref(x_241);
x_91 = x_221;
x_92 = x_219;
x_93 = x_223;
x_94 = x_220;
x_95 = x_242;
goto block_160;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_232);
lean_dec(x_226);
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_85);
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
x_243 = lean_ctor_get(x_233, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_233, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_245 = x_233;
} else {
 lean_dec_ref(x_233);
 x_245 = lean_box(0);
}
if (lean_is_scalar(x_245)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_245;
}
lean_ctor_set(x_246, 0, x_243);
lean_ctor_set(x_246, 1, x_244);
return x_246;
}
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec_ref(x_161);
lean_dec(x_85);
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
x_247 = lean_ctor_get(x_222, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_222, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_249 = x_222;
} else {
 lean_dec_ref(x_222);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
}
else
{
uint8_t x_251; 
lean_dec_ref(x_161);
lean_dec(x_85);
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
x_251 = !lean_is_exclusive(x_163);
if (x_251 == 0)
{
return x_163;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_163, 0);
x_253 = lean_ctor_get(x_163, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_163);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
block_274:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_257 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
x_258 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
x_259 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(x_258, x_7, x_256);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_unbox(x_260);
lean_dec(x_260);
if (x_261 == 0)
{
lean_object* x_262; 
lean_dec_ref(x_1);
x_262 = lean_ctor_get(x_259, 1);
lean_inc(x_262);
lean_dec_ref(x_259);
x_161 = x_257;
x_162 = x_262;
goto block_255;
}
else
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_259, 1);
lean_inc(x_263);
lean_dec_ref(x_259);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_264 = l_Lean_Compiler_LCNF_ppDecl(x_1, x_5, x_6, x_7, x_8, x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec_ref(x_264);
x_267 = l_Lean_MessageData_ofFormat(x_265);
x_268 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_simp_x3f_spec__1___redArg(x_258, x_267, x_6, x_7, x_8, x_266);
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
lean_dec_ref(x_268);
x_161 = x_257;
x_162 = x_269;
goto block_255;
}
else
{
uint8_t x_270; 
lean_dec(x_85);
lean_dec_ref(x_84);
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
x_270 = !lean_is_exclusive(x_264);
if (x_270 == 0)
{
return x_264;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_264, 0);
x_272 = lean_ctor_get(x_264, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_264);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
return x_273;
}
}
}
}
}
else
{
uint8_t x_342; 
lean_dec(x_85);
lean_dec_ref(x_84);
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
x_342 = !lean_is_exclusive(x_87);
if (x_342 == 0)
{
return x_87;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_87, 0);
x_344 = lean_ctor_get(x_87, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_87);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
else
{
lean_object* x_346; lean_object* x_347; 
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
x_346 = lean_box(0);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_9);
return x_347;
}
block_83:
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
uint8_t x_27; 
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
x_27 = !lean_is_exclusive(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_25, 1);
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_st_ref_get(x_19, x_28);
lean_dec(x_19);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*7);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec_ref(x_30);
x_34 = lean_box(0);
lean_ctor_set(x_25, 1, x_33);
lean_ctor_set(x_25, 0, x_34);
return x_25;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec_ref(x_30);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_18);
x_37 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_37, 0, x_10);
lean_ctor_set(x_37, 1, x_11);
lean_ctor_set(x_37, 2, x_12);
lean_ctor_set(x_37, 3, x_13);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set(x_37, 5, x_17);
lean_ctor_set_uint8(x_37, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_37, sizeof(void*)*6 + 1, x_16);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_25, 1, x_35);
lean_ctor_set(x_25, 0, x_38);
return x_25;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_dec(x_25);
x_40 = lean_st_ref_get(x_19, x_39);
lean_dec(x_19);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*7);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec_ref(x_40);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_18);
x_48 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_11);
lean_ctor_set(x_48, 2, x_12);
lean_ctor_set(x_48, 3, x_13);
lean_ctor_set(x_48, 4, x_47);
lean_ctor_set(x_48, 5, x_17);
lean_ctor_set_uint8(x_48, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_48, sizeof(void*)*6 + 1, x_16);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_19);
lean_dec_ref(x_18);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_dec_ref(x_25);
x_52 = !lean_is_exclusive(x_26);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_26, 0);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_11);
lean_ctor_set(x_55, 2, x_12);
lean_ctor_set(x_55, 3, x_13);
lean_ctor_set(x_55, 4, x_54);
lean_ctor_set(x_55, 5, x_17);
lean_ctor_set_uint8(x_55, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_55, sizeof(void*)*6 + 1, x_16);
x_56 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_55, x_20, x_21, x_22, x_23, x_51);
if (lean_obj_tag(x_56) == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_56, 0);
lean_ctor_set(x_26, 0, x_58);
lean_ctor_set(x_56, 0, x_26);
return x_56;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_56, 0);
x_60 = lean_ctor_get(x_56, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_56);
lean_ctor_set(x_26, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_26);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_free_object(x_26);
x_62 = !lean_is_exclusive(x_56);
if (x_62 == 0)
{
return x_56;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_56, 0);
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_56);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_26, 0);
lean_inc(x_66);
lean_dec(x_26);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_68, 0, x_10);
lean_ctor_set(x_68, 1, x_11);
lean_ctor_set(x_68, 2, x_12);
lean_ctor_set(x_68, 3, x_13);
lean_ctor_set(x_68, 4, x_67);
lean_ctor_set(x_68, 5, x_17);
lean_ctor_set_uint8(x_68, sizeof(void*)*6, x_15);
lean_ctor_set_uint8(x_68, sizeof(void*)*6 + 1, x_16);
x_69 = l_Lean_Compiler_LCNF_Decl_reduceJpArity(x_68, x_20, x_21, x_22, x_23, x_51);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_70);
if (lean_is_scalar(x_72)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_72;
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_71);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_69, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_77 = x_69;
} else {
 lean_dec_ref(x_69);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
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
x_79 = !lean_is_exclusive(x_25);
if (x_79 == 0)
{
return x_25;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_25, 0);
x_81 = lean_ctor_get(x_25, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_25);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
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
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_st_ref_get(x_10, x_20);
lean_dec(x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_22; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_ctor_set(x_17, 1, x_22);
lean_ctor_set(x_17, 0, x_1);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_17);
lean_dec_ref(x_1);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec_ref(x_21);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec_ref(x_19);
x_1 = x_24;
x_7 = x_23;
goto _start;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_st_ref_get(x_10, x_27);
lean_dec(x_10);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec_ref(x_1);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec_ref(x_28);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec_ref(x_26);
x_1 = x_32;
x_7 = x_31;
goto _start;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_34 = !lean_is_exclusive(x_17);
if (x_34 == 0)
{
return x_17;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_17, 0);
x_36 = lean_ctor_get(x_17, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_17);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
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
x_1 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12;
x_2 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
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
x_11 = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
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
