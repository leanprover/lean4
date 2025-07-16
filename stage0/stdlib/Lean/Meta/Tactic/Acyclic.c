// Lean compiler output
// Module: Lean.Meta.Tactic.Acyclic
// Imports: Lean.Meta.MatchUtil Lean.Meta.Tactic.Simp.Main
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
static lean_object* l_Lean_MVarId_acyclic_go___closed__0;
static lean_object* l_Lean_MVarId_acyclic_go___closed__30;
static lean_object* l_Lean_MVarId_acyclic_go___closed__13;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__18;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__3;
static lean_object* l_Lean_MVarId_acyclic_go___closed__27;
static lean_object* l_Lean_MVarId_acyclic_go___closed__25;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__20;
lean_object* l_Lean_Meta_isConstructorApp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__10;
static lean_object* l_Lean_MVarId_acyclic_go___closed__22;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__17;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__32;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn___closed__4____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_initFn___closed__1____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_initFn___closed__3____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_acyclic_go___closed__34;
static lean_object* l_Lean_MVarId_acyclic_go___closed__8;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__1;
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__36;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__29;
static lean_object* l_Lean_MVarId_acyclic_go___closed__12;
static lean_object* l_Lean_MVarId_acyclic___lam__0___closed__2;
static lean_object* l_Lean_MVarId_acyclic_go___closed__19;
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn___closed__0____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_acyclic___lam__0___closed__1;
static lean_object* l_Lean_MVarId_initFn___closed__5____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_acyclic_go___closed__23;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__26;
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn___closed__14____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__9;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn___closed__2____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
lean_object* l_Lean_Meta_getSimpTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__11;
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn___closed__15____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_MVarId_acyclic___lam__0___closed__3;
static lean_object* l_Lean_MVarId_acyclic_go___closed__31;
static lean_object* l_Lean_MVarId_initFn___closed__12____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_initFn___closed__8____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__33;
static lean_object* l_Lean_MVarId_initFn___closed__10____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_initFn___closed__7____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_acyclic_go___closed__14;
static lean_object* l_Lean_MVarId_initFn___closed__9____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_acyclic_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn___closed__11____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__21;
static lean_object* l_Lean_MVarId_acyclic_go___closed__15;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__16;
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__24;
static lean_object* l_Lean_MVarId_initFn___closed__13____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__7;
static lean_object* l_Lean_MVarId_acyclic_go___closed__6;
static lean_object* l_Lean_MVarId_acyclic_go___closed__37;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_856_(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__35;
static lean_object* l_Lean_MVarId_initFn___closed__6____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
static lean_object* l_Lean_MVarId_acyclic___lam__0___closed__0;
static lean_object* l_Lean_MVarId_acyclic_go___closed__28;
static lean_object* l_Lean_MVarId_acyclic_go___closed__5;
static lean_object* l_Lean_MVarId_acyclic_go___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_12; 
x_12 = l_Lean_Expr_isFVar(x_1);
if (x_12 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
goto block_11;
}
else
{
uint8_t x_13; 
x_13 = l_Lean_Expr_occurs(x_1, x_2);
if (x_13 == 0)
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
goto block_11;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_Meta_isConstructorApp_x27(x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
block_11:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("acyclic", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_MVarId_acyclic_go___closed__2;
x_2 = l_Lean_MVarId_acyclic_go___closed__1;
x_3 = l_Lean_MVarId_acyclic_go___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed with\n", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SizeOf", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sizeOf", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__9;
x_2 = l_Lean_MVarId_acyclic_go___closed__8;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__12() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_unsigned_to_nat(100000u);
x_6 = lean_alloc_ctor(0, 2, 24);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_1);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 19, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 20, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 21, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 22, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 23, x_2);
return x_6;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(4u);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = l_Lean_MVarId_acyclic_go___closed__13;
x_3 = lean_nat_div(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__14;
x_2 = l_Nat_nextPowerOfTwo(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_acyclic_go___closed__15;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__16;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_MVarId_acyclic_go___closed__19;
x_2 = l_Lean_MVarId_acyclic_go___closed__17;
x_3 = 1;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty(lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_MVarId_acyclic_go___closed__22;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__25;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__27() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_MVarId_acyclic_go___closed__25;
x_4 = l_Lean_MVarId_acyclic_go___closed__26;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_MVarId_acyclic_go___closed__27;
x_2 = l_Lean_MVarId_acyclic_go___closed__24;
x_3 = l_Lean_MVarId_acyclic_go___closed__22;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__28;
x_2 = l_Lean_MVarId_acyclic_go___closed__23;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt_of_lt_of_eq", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__31;
x_2 = l_Lean_MVarId_acyclic_go___closed__30;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt_irrefl", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__34;
x_2 = l_Lean_MVarId_acyclic_go___closed__30;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__36() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succeeded", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__36;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = l_Lean_MVarId_acyclic_go___closed__10;
x_45 = l_Lean_MVarId_acyclic_go___closed__11;
x_46 = lean_array_push(x_45, x_3);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_47 = l_Lean_Meta_mkAppM(x_44, x_46, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec_ref(x_47);
x_50 = lean_array_push(x_45, x_4);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_51 = l_Lean_Meta_mkAppM(x_44, x_50, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_48);
x_54 = l_Lean_Meta_mkLT(x_48, x_52, x_5, x_6, x_7, x_8, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec_ref(x_54);
x_57 = lean_box(0);
lean_inc_ref(x_5);
x_58 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_55, x_57, x_5, x_6, x_7, x_8, x_56);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = l_Lean_Meta_getSimpTheorems___redArg(x_8, x_60);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = 0;
x_65 = 1;
x_66 = l_Lean_MVarId_acyclic_go___closed__12;
x_67 = lean_array_push(x_45, x_62);
x_68 = l_Lean_MVarId_acyclic_go___closed__20;
x_69 = l_Lean_Meta_Simp_mkContext___redArg(x_66, x_67, x_68, x_5, x_8, x_63);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec_ref(x_69);
x_72 = l_Lean_Expr_mvarId_x21(x_59);
x_73 = l_Lean_MVarId_acyclic_go___closed__21;
x_74 = lean_box(0);
x_75 = l_Lean_MVarId_acyclic_go___closed__29;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_76 = l_Lean_Meta_simpTarget(x_72, x_70, x_73, x_74, x_65, x_75, x_5, x_6, x_7, x_8, x_71);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec_ref(x_76);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_80 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec_ref(x_80);
x_83 = l_Lean_Expr_appFn_x21(x_48);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_84 = l_Lean_Meta_mkCongrArg(x_83, x_81, x_5, x_6, x_7, x_8, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = l_Lean_MVarId_acyclic_go___closed__32;
x_88 = l_Lean_MVarId_acyclic_go___closed__33;
x_89 = lean_array_push(x_88, x_59);
x_90 = lean_array_push(x_89, x_85);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_91 = l_Lean_Meta_mkAppM(x_87, x_90, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec_ref(x_91);
x_94 = l_Lean_MVarId_acyclic_go___closed__35;
x_95 = lean_array_push(x_45, x_48);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_96 = l_Lean_Meta_mkAppM(x_94, x_95, x_5, x_6, x_7, x_8, x_93);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec_ref(x_96);
lean_inc(x_1);
x_99 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = l_Lean_Expr_app___override(x_97, x_92);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_103 = l_Lean_Meta_mkFalseElim(x_100, x_102, x_5, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_106 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_104, x_6, x_105);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = l_Lean_MVarId_acyclic_go___closed__3;
x_109 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_108, x_7, x_107);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
uint8_t x_112; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_112 = !lean_is_exclusive(x_109);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_109, 0);
lean_dec(x_113);
x_114 = lean_box(x_65);
lean_ctor_set(x_109, 0, x_114);
return x_109;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_109, 1);
lean_inc(x_115);
lean_dec(x_109);
x_116 = lean_box(x_65);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_118 = lean_ctor_get(x_109, 1);
lean_inc(x_118);
lean_dec_ref(x_109);
x_119 = l_Lean_MVarId_acyclic_go___closed__37;
x_120 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_108, x_119, x_5, x_6, x_7, x_8, x_118);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_120, 0);
lean_dec(x_122);
x_123 = lean_box(x_65);
lean_ctor_set(x_120, 0, x_123);
return x_120;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_125 = lean_box(x_65);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_103);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_103, 0);
x_129 = lean_ctor_get(x_103, 1);
lean_inc(x_129);
lean_inc(x_128);
x_38 = x_103;
x_39 = x_128;
x_40 = x_129;
goto block_43;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_103, 0);
x_131 = lean_ctor_get(x_103, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_103);
lean_inc(x_131);
lean_inc(x_130);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_38 = x_132;
x_39 = x_130;
x_40 = x_131;
goto block_43;
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_97);
lean_dec(x_92);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_99);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_99, 0);
x_135 = lean_ctor_get(x_99, 1);
lean_inc(x_135);
lean_inc(x_134);
x_38 = x_99;
x_39 = x_134;
x_40 = x_135;
goto block_43;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_99, 0);
x_137 = lean_ctor_get(x_99, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_99);
lean_inc(x_137);
lean_inc(x_136);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
x_38 = x_138;
x_39 = x_136;
x_40 = x_137;
goto block_43;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_92);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_96);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_96, 0);
x_141 = lean_ctor_get(x_96, 1);
lean_inc(x_141);
lean_inc(x_140);
x_38 = x_96;
x_39 = x_140;
x_40 = x_141;
goto block_43;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_96, 0);
x_143 = lean_ctor_get(x_96, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_96);
lean_inc(x_143);
lean_inc(x_142);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_38 = x_144;
x_39 = x_142;
x_40 = x_143;
goto block_43;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_48);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_91);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_91, 0);
x_147 = lean_ctor_get(x_91, 1);
lean_inc(x_147);
lean_inc(x_146);
x_38 = x_91;
x_39 = x_146;
x_40 = x_147;
goto block_43;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_91, 0);
x_149 = lean_ctor_get(x_91, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_91);
lean_inc(x_149);
lean_inc(x_148);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_38 = x_150;
x_39 = x_148;
x_40 = x_149;
goto block_43;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_84);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_84, 0);
x_153 = lean_ctor_get(x_84, 1);
lean_inc(x_153);
lean_inc(x_152);
x_38 = x_84;
x_39 = x_152;
x_40 = x_153;
goto block_43;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_84, 0);
x_155 = lean_ctor_get(x_84, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_84);
lean_inc(x_155);
lean_inc(x_154);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_38 = x_156;
x_39 = x_154;
x_40 = x_155;
goto block_43;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_80);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_80, 0);
x_159 = lean_ctor_get(x_80, 1);
lean_inc(x_159);
lean_inc(x_158);
x_38 = x_80;
x_39 = x_158;
x_40 = x_159;
goto block_43;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_80, 0);
x_161 = lean_ctor_get(x_80, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_80);
lean_inc(x_161);
lean_inc(x_160);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_38 = x_162;
x_39 = x_160;
x_40 = x_161;
goto block_43;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_78);
lean_dec(x_59);
lean_dec(x_48);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_2);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_76);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
x_164 = lean_ctor_get(x_76, 0);
lean_dec(x_164);
x_165 = lean_box(x_64);
lean_ctor_set(x_76, 0, x_165);
return x_76;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_76, 1);
lean_inc(x_166);
lean_dec(x_76);
x_167 = lean_box(x_64);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_166);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_59);
lean_dec(x_48);
lean_dec_ref(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_76);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_76, 0);
x_171 = lean_ctor_get(x_76, 1);
lean_inc(x_171);
lean_inc(x_170);
x_38 = x_76;
x_39 = x_170;
x_40 = x_171;
goto block_43;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_76, 0);
x_173 = lean_ctor_get(x_76, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_76);
lean_inc(x_173);
lean_inc(x_172);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
x_38 = x_174;
x_39 = x_172;
x_40 = x_173;
goto block_43;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_48);
lean_dec_ref(x_2);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_54);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_54, 0);
x_177 = lean_ctor_get(x_54, 1);
lean_inc(x_177);
lean_inc(x_176);
x_38 = x_54;
x_39 = x_176;
x_40 = x_177;
goto block_43;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_54, 0);
x_179 = lean_ctor_get(x_54, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_54);
lean_inc(x_179);
lean_inc(x_178);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
x_38 = x_180;
x_39 = x_178;
x_40 = x_179;
goto block_43;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_48);
lean_dec_ref(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_51);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
x_182 = lean_ctor_get(x_51, 0);
x_183 = lean_ctor_get(x_51, 1);
lean_inc(x_183);
lean_inc(x_182);
x_38 = x_51;
x_39 = x_182;
x_40 = x_183;
goto block_43;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_51, 0);
x_185 = lean_ctor_get(x_51, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_51);
lean_inc(x_185);
lean_inc(x_184);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_38 = x_186;
x_39 = x_184;
x_40 = x_185;
goto block_43;
}
}
}
else
{
uint8_t x_187; 
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec(x_1);
x_187 = !lean_is_exclusive(x_47);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; 
x_188 = lean_ctor_get(x_47, 0);
x_189 = lean_ctor_get(x_47, 1);
lean_inc(x_189);
lean_inc(x_188);
x_38 = x_47;
x_39 = x_188;
x_40 = x_189;
goto block_43;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_47, 0);
x_191 = lean_ctor_get(x_47, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_47);
lean_inc(x_191);
lean_inc(x_190);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_38 = x_192;
x_39 = x_190;
x_40 = x_191;
goto block_43;
}
}
block_37:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_dec_ref(x_11);
x_14 = l_Lean_MVarId_acyclic_go___closed__3;
x_15 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_14, x_7, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(x_13);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(x_13);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec_ref(x_15);
x_25 = l_Lean_MVarId_acyclic_go___closed__5;
x_26 = l_Lean_Exception_toMessageData(x_10);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_MVarId_acyclic_go___closed__7;
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_14, x_29, x_5, x_6, x_7, x_8, x_24);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(x_13);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(x_13);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_dec_ref(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_11;
}
}
block_43:
{
uint8_t x_41; 
x_41 = l_Lean_Exception_isInterrupt(x_39);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = l_Lean_Exception_isRuntime(x_39);
x_10 = x_39;
x_11 = x_38;
x_12 = x_40;
x_13 = x_42;
goto block_37;
}
else
{
x_10 = x_39;
x_11 = x_38;
x_12 = x_40;
x_13 = x_41;
goto block_37;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_11 = l_Lean_Meta_whnfD(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_47 = l_Lean_MVarId_acyclic_go___closed__3;
x_48 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_47, x_5, x_13);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec_ref(x_48);
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_51;
goto block_46;
}
else
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_48);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_48, 1);
x_54 = lean_ctor_get(x_48, 0);
lean_dec(x_54);
x_55 = l_Lean_MVarId_acyclic___lam__0___closed__3;
lean_inc(x_12);
x_56 = l_Lean_MessageData_ofExpr(x_12);
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_56);
lean_ctor_set(x_48, 0, x_55);
x_57 = l_Lean_MVarId_acyclic_go___closed__7;
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_47, x_58, x_3, x_4, x_5, x_6, x_53);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec_ref(x_59);
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_60;
goto block_46;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_48, 1);
lean_inc(x_61);
lean_dec(x_48);
x_62 = l_Lean_MVarId_acyclic___lam__0___closed__3;
lean_inc(x_12);
x_63 = l_Lean_MessageData_ofExpr(x_12);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_MVarId_acyclic_go___closed__7;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_47, x_66, x_3, x_4, x_5, x_6, x_61);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec_ref(x_67);
x_15 = x_3;
x_16 = x_4;
x_17 = x_5;
x_18 = x_6;
x_19 = x_68;
goto block_46;
}
}
block_46:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = l_Lean_MVarId_acyclic___lam__0___closed__1;
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Expr_isAppOfArity(x_12, x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_12);
lean_dec(x_2);
lean_dec_ref(x_1);
x_23 = lean_box(x_22);
if (lean_is_scalar(x_14)) {
 x_24 = lean_alloc_ctor(0, 2, 0);
} else {
 x_24 = x_14;
}
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
x_25 = l_Lean_Expr_appFn_x21(x_12);
x_26 = l_Lean_Expr_appArg_x21(x_25);
lean_dec_ref(x_25);
x_27 = l_Lean_Expr_appArg_x21(x_12);
lean_dec(x_12);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_27);
lean_inc_ref(x_26);
x_28 = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(x_26, x_27, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec_ref(x_28);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc_ref(x_26);
lean_inc_ref(x_27);
x_32 = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(x_27, x_26, x_15, x_16, x_17, x_18, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
lean_inc(x_18);
lean_inc_ref(x_17);
lean_inc(x_16);
lean_inc_ref(x_15);
x_36 = l_Lean_Meta_mkEqSymm(x_1, x_15, x_16, x_17, x_18, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec_ref(x_36);
x_39 = l_Lean_MVarId_acyclic_go(x_2, x_37, x_27, x_26, x_15, x_16, x_17, x_18, x_38);
return x_39;
}
else
{
uint8_t x_40; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_36);
if (x_40 == 0)
{
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_32;
}
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_28, 1);
lean_inc(x_44);
lean_dec_ref(x_28);
x_45 = l_Lean_MVarId_acyclic_go(x_2, x_1, x_26, x_27, x_15, x_16, x_17, x_18, x_44);
return x_45;
}
}
else
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec(x_18);
lean_dec_ref(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_28;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_11);
if (x_69 == 0)
{
return x_11;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_11, 0);
x_71 = lean_ctor_get(x_11, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_8);
if (x_73 == 0)
{
return x_8;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_8, 0);
x_75 = lean_ctor_get(x_8, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_8);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__0____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__1____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn___closed__0____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__2____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MVarId", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__3____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn___closed__2____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_2 = l_Lean_MVarId_initFn___closed__1____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__4____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__5____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn___closed__4____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_2 = l_Lean_MVarId_initFn___closed__3____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__6____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__7____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn___closed__6____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_2 = l_Lean_MVarId_initFn___closed__5____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__8____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn___closed__0____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_2 = l_Lean_MVarId_initFn___closed__7____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__9____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__0;
x_2 = l_Lean_MVarId_initFn___closed__8____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__10____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__1;
x_2 = l_Lean_MVarId_initFn___closed__9____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__11____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Acyclic", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__12____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn___closed__11____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_2 = l_Lean_MVarId_initFn___closed__10____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__13____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__14____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn___closed__13____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_2 = l_Lean_MVarId_initFn___closed__12____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_3 = l_Lean_Name_str___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn___closed__15____x40_Lean_Meta_Tactic_Acyclic___hyg_856_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(856u);
x_2 = l_Lean_MVarId_initFn___closed__14____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_3 = l_Lean_Name_num___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_856_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_MVarId_acyclic_go___closed__3;
x_3 = 0;
x_4 = l_Lean_MVarId_initFn___closed__15____x40_Lean_Meta_Tactic_Acyclic___hyg_856_;
x_5 = l_Lean_registerTraceClass(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MVarId_acyclic_go___closed__0 = _init_l_Lean_MVarId_acyclic_go___closed__0();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__0);
l_Lean_MVarId_acyclic_go___closed__1 = _init_l_Lean_MVarId_acyclic_go___closed__1();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__1);
l_Lean_MVarId_acyclic_go___closed__2 = _init_l_Lean_MVarId_acyclic_go___closed__2();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__2);
l_Lean_MVarId_acyclic_go___closed__3 = _init_l_Lean_MVarId_acyclic_go___closed__3();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__3);
l_Lean_MVarId_acyclic_go___closed__4 = _init_l_Lean_MVarId_acyclic_go___closed__4();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__4);
l_Lean_MVarId_acyclic_go___closed__5 = _init_l_Lean_MVarId_acyclic_go___closed__5();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__5);
l_Lean_MVarId_acyclic_go___closed__6 = _init_l_Lean_MVarId_acyclic_go___closed__6();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__6);
l_Lean_MVarId_acyclic_go___closed__7 = _init_l_Lean_MVarId_acyclic_go___closed__7();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__7);
l_Lean_MVarId_acyclic_go___closed__8 = _init_l_Lean_MVarId_acyclic_go___closed__8();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__8);
l_Lean_MVarId_acyclic_go___closed__9 = _init_l_Lean_MVarId_acyclic_go___closed__9();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__9);
l_Lean_MVarId_acyclic_go___closed__10 = _init_l_Lean_MVarId_acyclic_go___closed__10();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__10);
l_Lean_MVarId_acyclic_go___closed__11 = _init_l_Lean_MVarId_acyclic_go___closed__11();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__11);
l_Lean_MVarId_acyclic_go___closed__12 = _init_l_Lean_MVarId_acyclic_go___closed__12();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__12);
l_Lean_MVarId_acyclic_go___closed__13 = _init_l_Lean_MVarId_acyclic_go___closed__13();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__13);
l_Lean_MVarId_acyclic_go___closed__14 = _init_l_Lean_MVarId_acyclic_go___closed__14();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__14);
l_Lean_MVarId_acyclic_go___closed__15 = _init_l_Lean_MVarId_acyclic_go___closed__15();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__15);
l_Lean_MVarId_acyclic_go___closed__16 = _init_l_Lean_MVarId_acyclic_go___closed__16();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__16);
l_Lean_MVarId_acyclic_go___closed__17 = _init_l_Lean_MVarId_acyclic_go___closed__17();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__17);
l_Lean_MVarId_acyclic_go___closed__18 = _init_l_Lean_MVarId_acyclic_go___closed__18();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__18);
l_Lean_MVarId_acyclic_go___closed__19 = _init_l_Lean_MVarId_acyclic_go___closed__19();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__19);
l_Lean_MVarId_acyclic_go___closed__20 = _init_l_Lean_MVarId_acyclic_go___closed__20();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__20);
l_Lean_MVarId_acyclic_go___closed__21 = _init_l_Lean_MVarId_acyclic_go___closed__21();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__21);
l_Lean_MVarId_acyclic_go___closed__22 = _init_l_Lean_MVarId_acyclic_go___closed__22();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__22);
l_Lean_MVarId_acyclic_go___closed__23 = _init_l_Lean_MVarId_acyclic_go___closed__23();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__23);
l_Lean_MVarId_acyclic_go___closed__24 = _init_l_Lean_MVarId_acyclic_go___closed__24();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__24);
l_Lean_MVarId_acyclic_go___closed__25 = _init_l_Lean_MVarId_acyclic_go___closed__25();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__25);
l_Lean_MVarId_acyclic_go___closed__26 = _init_l_Lean_MVarId_acyclic_go___closed__26();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__26);
l_Lean_MVarId_acyclic_go___closed__27 = _init_l_Lean_MVarId_acyclic_go___closed__27();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__27);
l_Lean_MVarId_acyclic_go___closed__28 = _init_l_Lean_MVarId_acyclic_go___closed__28();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__28);
l_Lean_MVarId_acyclic_go___closed__29 = _init_l_Lean_MVarId_acyclic_go___closed__29();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__29);
l_Lean_MVarId_acyclic_go___closed__30 = _init_l_Lean_MVarId_acyclic_go___closed__30();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__30);
l_Lean_MVarId_acyclic_go___closed__31 = _init_l_Lean_MVarId_acyclic_go___closed__31();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__31);
l_Lean_MVarId_acyclic_go___closed__32 = _init_l_Lean_MVarId_acyclic_go___closed__32();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__32);
l_Lean_MVarId_acyclic_go___closed__33 = _init_l_Lean_MVarId_acyclic_go___closed__33();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__33);
l_Lean_MVarId_acyclic_go___closed__34 = _init_l_Lean_MVarId_acyclic_go___closed__34();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__34);
l_Lean_MVarId_acyclic_go___closed__35 = _init_l_Lean_MVarId_acyclic_go___closed__35();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__35);
l_Lean_MVarId_acyclic_go___closed__36 = _init_l_Lean_MVarId_acyclic_go___closed__36();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__36);
l_Lean_MVarId_acyclic_go___closed__37 = _init_l_Lean_MVarId_acyclic_go___closed__37();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__37);
l_Lean_MVarId_acyclic___lam__0___closed__0 = _init_l_Lean_MVarId_acyclic___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_acyclic___lam__0___closed__0);
l_Lean_MVarId_acyclic___lam__0___closed__1 = _init_l_Lean_MVarId_acyclic___lam__0___closed__1();
lean_mark_persistent(l_Lean_MVarId_acyclic___lam__0___closed__1);
l_Lean_MVarId_acyclic___lam__0___closed__2 = _init_l_Lean_MVarId_acyclic___lam__0___closed__2();
lean_mark_persistent(l_Lean_MVarId_acyclic___lam__0___closed__2);
l_Lean_MVarId_acyclic___lam__0___closed__3 = _init_l_Lean_MVarId_acyclic___lam__0___closed__3();
lean_mark_persistent(l_Lean_MVarId_acyclic___lam__0___closed__3);
l_Lean_MVarId_initFn___closed__0____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__0____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__0____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__1____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__1____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__1____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__2____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__2____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__2____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__3____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__3____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__3____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__4____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__4____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__4____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__5____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__5____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__5____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__6____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__6____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__6____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__7____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__7____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__7____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__8____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__8____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__8____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__9____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__9____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__9____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__10____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__10____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__10____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__11____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__11____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__11____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__12____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__12____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__12____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__13____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__13____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__13____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__14____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__14____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__14____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
l_Lean_MVarId_initFn___closed__15____x40_Lean_Meta_Tactic_Acyclic___hyg_856_ = _init_l_Lean_MVarId_initFn___closed__15____x40_Lean_Meta_Tactic_Acyclic___hyg_856_();
lean_mark_persistent(l_Lean_MVarId_initFn___closed__15____x40_Lean_Meta_Tactic_Acyclic___hyg_856_);
if (builtin) {res = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_856_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
