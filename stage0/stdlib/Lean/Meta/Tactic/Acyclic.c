// Lean compiler output
// Module: Lean.Meta.Tactic.Acyclic
// Imports: Init Lean.Meta.MatchUtil Lean.Meta.Tactic.Simp.Main
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
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__1;
static lean_object* l_Lean_Meta_acyclic___lambda__2___closed__1;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_acyclic___lambda__2___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__21;
static lean_object* l_Lean_Meta_acyclic_go___closed__19;
lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__7;
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__29;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__5;
static lean_object* l_Lean_Meta_acyclic_go___closed__24;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__22;
static lean_object* l_Lean_Meta_acyclic_go___closed__33;
static lean_object* l_Lean_Meta_acyclic_go___closed__18;
static lean_object* l_Lean_Meta_acyclic_go___closed__13;
static lean_object* l_Lean_Meta_acyclic_go___closed__23;
static lean_object* l_Lean_Meta_acyclic_go___closed__14;
static lean_object* l_Lean_Meta_acyclic_go___closed__28;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_772_(lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__15;
static lean_object* l_Lean_Meta_acyclic_go___closed__30;
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_simpExtension;
static lean_object* l_Lean_Meta_acyclic___lambda__1___closed__2;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__12;
lean_object* l_Std_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__16;
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__20;
static lean_object* l_Lean_Meta_acyclic_go___closed__10;
static lean_object* l_Lean_Meta_acyclic_go___closed__32;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__3;
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic___lambda__1___closed__1;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__4;
static lean_object* l_Lean_Meta_acyclic_go___closed__27;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__26;
static lean_object* l_Lean_Meta_acyclic_go___closed__11;
static lean_object* l_Lean_Meta_acyclic_go___closed__9;
uint8_t l_Lean_Expr_isConstructorApp(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__31;
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_Meta_isTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_Meta_isTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__6;
static lean_object* l_Lean_Meta_acyclic_go___closed__8;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_acyclic_go___closed__25;
static lean_object* l_Lean_Meta_acyclic_go___closed__17;
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l_Lean_Meta_acyclic_go___closed__2;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_Meta_isTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isFVar(x_1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
uint8_t x_12; 
lean_inc(x_2);
x_12 = l_Lean_Expr_occurs(x_1, x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_st_ref_get(x_6, x_7);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Expr_isConstructorApp(x_19, x_2);
lean_dec(x_2);
x_21 = lean_box(x_20);
lean_ctor_set(x_16, 0, x_21);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Expr_isConstructorApp(x_24, x_2);
lean_dec(x_2);
x_26 = lean_box(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_Meta_isTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_Meta_isTarget(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Meta");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_acyclic_go___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Tactic");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_acyclic_go___closed__2;
x_2 = l_Lean_Meta_acyclic_go___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("acyclic");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_acyclic_go___closed__4;
x_2 = l_Lean_Meta_acyclic_go___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_acyclic_go___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed with\n");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_acyclic_go___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_acyclic_go___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("SizeOf");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_acyclic_go___closed__12;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sizeOf");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_acyclic_go___closed__13;
x_2 = l_Lean_Meta_acyclic_go___closed__14;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtension;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 2, 11);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 6, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 9, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 10, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Std_mkHashMapImp___rarg(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_acyclic_go___closed__20;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_acyclic_go___closed__21;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__23() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_Meta_acyclic_go___closed__19;
x_3 = l_Lean_Meta_acyclic_go___closed__22;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Nat");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_acyclic_go___closed__24;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lt_of_lt_of_eq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_acyclic_go___closed__25;
x_2 = l_Lean_Meta_acyclic_go___closed__26;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lt_irrefl");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_acyclic_go___closed__25;
x_2 = l_Lean_Meta_acyclic_go___closed__29;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_acyclic_go___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succeeded");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic_go___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_acyclic_go___closed__32;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = l_Lean_Meta_acyclic_go___closed__16;
x_57 = lean_array_push(x_56, x_3);
x_58 = l_Lean_Meta_acyclic_go___closed__15;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_Meta_mkAppM(x_58, x_57, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_array_push(x_56, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_63 = l_Lean_Meta_mkAppM(x_58, x_62, x_5, x_6, x_7, x_8, x_61);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_60);
x_66 = l_Lean_Meta_mkLT(x_60, x_64, x_5, x_6, x_7, x_8, x_65);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_box(0);
lean_inc(x_5);
x_70 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_67, x_69, x_5, x_6, x_7, x_8, x_68);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Meta_acyclic_go___closed__17;
x_74 = l_Lean_Meta_SimpExtension_getTheorems(x_73, x_7, x_8, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Expr_mvarId_x21(x_71);
x_78 = lean_box(0);
x_79 = l_Lean_Meta_acyclic_go___closed__18;
x_80 = l_Lean_Meta_acyclic_go___closed__23;
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_75);
lean_ctor_set(x_82, 2, x_80);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_82, 4, x_81);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_83 = l_Lean_Meta_simpTarget(x_77, x_82, x_78, x_5, x_6, x_7, x_8, x_76);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_86 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Expr_appFn_x21(x_60);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_90 = l_Lean_Meta_mkCongrArg(x_89, x_87, x_5, x_6, x_7, x_8, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Meta_acyclic_go___closed__28;
x_94 = lean_array_push(x_93, x_71);
x_95 = lean_array_push(x_94, x_91);
x_96 = l_Lean_Meta_acyclic_go___closed__27;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_97 = l_Lean_Meta_mkAppM(x_96, x_95, x_5, x_6, x_7, x_8, x_92);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = lean_array_push(x_56, x_60);
x_101 = l_Lean_Meta_acyclic_go___closed__30;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = l_Lean_Meta_mkAppM(x_101, x_100, x_5, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_1);
x_105 = l_Lean_Meta_getMVarType(x_1, x_5, x_6, x_7, x_8, x_104);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_mkApp(x_103, x_98);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_109 = l_Lean_Meta_mkFalseElim(x_106, x_108, x_5, x_6, x_7, x_8, x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = l_Lean_Meta_assignExprMVar(x_1, x_110, x_5, x_6, x_7, x_8, x_111);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_Meta_acyclic_go___closed__6;
x_138 = lean_st_ref_get(x_8, x_113);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_139, 3);
lean_inc(x_140);
lean_dec(x_139);
x_141 = lean_ctor_get_uint8(x_140, sizeof(void*)*1);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_138, 1);
lean_inc(x_142);
lean_dec(x_138);
x_143 = 0;
x_115 = x_143;
x_116 = x_142;
goto block_137;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_144 = lean_ctor_get(x_138, 1);
lean_inc(x_144);
lean_dec(x_138);
x_145 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_114, x_5, x_6, x_7, x_8, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_unbox(x_146);
lean_dec(x_146);
x_115 = x_148;
x_116 = x_147;
goto block_137;
}
block_137:
{
lean_object* x_117; 
x_117 = l_Lean_Meta_acyclic_go___closed__31;
if (x_115 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_119 = lean_apply_6(x_117, x_118, x_5, x_6, x_7, x_8, x_116);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
return x_119;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_119);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_dec(x_119);
x_10 = x_124;
x_11 = x_125;
goto block_55;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = l_Lean_Meta_acyclic_go___closed__33;
x_127 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_114, x_126, x_5, x_6, x_7, x_8, x_116);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_130 = lean_apply_6(x_117, x_128, x_5, x_6, x_7, x_8, x_129);
if (lean_obj_tag(x_130) == 0)
{
uint8_t x_131; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_131 = !lean_is_exclusive(x_130);
if (x_131 == 0)
{
return x_130;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_130, 0);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_130);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_130, 1);
lean_inc(x_136);
lean_dec(x_130);
x_10 = x_135;
x_11 = x_136;
goto block_55;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_dec(x_1);
x_149 = lean_ctor_get(x_109, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_109, 1);
lean_inc(x_150);
lean_dec(x_109);
x_10 = x_149;
x_11 = x_150;
goto block_55;
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec(x_103);
lean_dec(x_98);
lean_dec(x_1);
x_151 = lean_ctor_get(x_105, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_105, 1);
lean_inc(x_152);
lean_dec(x_105);
x_10 = x_151;
x_11 = x_152;
goto block_55;
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_98);
lean_dec(x_1);
x_153 = lean_ctor_get(x_102, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_102, 1);
lean_inc(x_154);
lean_dec(x_102);
x_10 = x_153;
x_11 = x_154;
goto block_55;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
lean_dec(x_60);
lean_dec(x_1);
x_155 = lean_ctor_get(x_97, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_97, 1);
lean_inc(x_156);
lean_dec(x_97);
x_10 = x_155;
x_11 = x_156;
goto block_55;
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_71);
lean_dec(x_60);
lean_dec(x_1);
x_157 = lean_ctor_get(x_90, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_90, 1);
lean_inc(x_158);
lean_dec(x_90);
x_10 = x_157;
x_11 = x_158;
goto block_55;
}
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_71);
lean_dec(x_60);
lean_dec(x_1);
x_159 = lean_ctor_get(x_86, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_86, 1);
lean_inc(x_160);
lean_dec(x_86);
x_10 = x_159;
x_11 = x_160;
goto block_55;
}
}
else
{
uint8_t x_161; 
lean_dec(x_84);
lean_dec(x_71);
lean_dec(x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_83);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_83, 0);
lean_dec(x_162);
x_163 = 0;
x_164 = lean_box(x_163);
lean_ctor_set(x_83, 0, x_164);
return x_83;
}
else
{
lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_83, 1);
lean_inc(x_165);
lean_dec(x_83);
x_166 = 0;
x_167 = lean_box(x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_165);
return x_168;
}
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_71);
lean_dec(x_60);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_ctor_get(x_83, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_83, 1);
lean_inc(x_170);
lean_dec(x_83);
x_10 = x_169;
x_11 = x_170;
goto block_55;
}
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_60);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_66, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_66, 1);
lean_inc(x_172);
lean_dec(x_66);
x_10 = x_171;
x_11 = x_172;
goto block_55;
}
}
else
{
lean_object* x_173; lean_object* x_174; 
lean_dec(x_60);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_63, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_63, 1);
lean_inc(x_174);
lean_dec(x_63);
x_10 = x_173;
x_11 = x_174;
goto block_55;
}
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_ctor_get(x_59, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_59, 1);
lean_inc(x_176);
lean_dec(x_59);
x_10 = x_175;
x_11 = x_176;
goto block_55;
}
block_55:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_12 = l_Lean_Meta_acyclic_go___closed__6;
x_44 = lean_st_ref_get(x_8, x_11);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 3);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*1);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = 0;
x_13 = x_49;
x_14 = x_48;
goto block_43;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_12, x_5, x_6, x_7, x_8, x_50);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unbox(x_52);
lean_dec(x_52);
x_13 = x_54;
x_14 = x_53;
goto block_43;
}
block_43:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_acyclic_go___closed__7;
if (x_13 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_apply_6(x_15, x_16, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = l_Lean_Exception_toMessageData(x_10);
x_27 = l_Lean_Meta_acyclic_go___closed__9;
x_28 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
x_29 = l_Lean_Meta_acyclic_go___closed__11;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_12, x_30, x_5, x_6, x_7, x_8, x_14);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_apply_6(x_15, x_32, x_5, x_6, x_7, x_8, x_33);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_34);
if (x_39 == 0)
{
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 0);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_34);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_acyclic_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_acyclic_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_acyclic___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_acyclic___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_acyclic___lambda__1___closed__2;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity(x_1, x_10, x_11);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = 0;
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = l_Lean_Expr_appFn_x21(x_1);
x_17 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
x_18 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_18);
lean_inc(x_17);
x_19 = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_Meta_isTarget(x_17, x_18, x_5, x_6, x_7, x_8, x_9);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_17);
lean_inc(x_18);
x_23 = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_Meta_isTarget(x_18, x_17, x_5, x_6, x_7, x_8, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = 0;
x_29 = lean_box(x_28);
lean_ctor_set(x_23, 0, x_29);
return x_23;
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_dec(x_23);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_35 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_acyclic_go(x_3, x_36, x_18, x_17, x_5, x_6, x_7, x_8, x_37);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
return x_35;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_35, 0);
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_35);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_19, 1);
lean_inc(x_43);
lean_dec(x_19);
x_44 = l_Lean_Meta_acyclic_go(x_3, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_43);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_acyclic___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("type: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_acyclic___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_acyclic___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_whnfD(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Meta_acyclic_go___closed__6;
x_29 = lean_st_ref_get(x_6, x_13);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 3);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get_uint8(x_31, sizeof(void*)*1);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = 0;
x_15 = x_34;
x_16 = x_33;
goto block_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_14, x_3, x_4, x_5, x_6, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_unbox(x_37);
lean_dec(x_37);
x_15 = x_39;
x_16 = x_38;
goto block_28;
}
block_28:
{
if (x_15 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Meta_acyclic___lambda__1(x_12, x_1, x_2, x_17, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_inc(x_12);
x_19 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_19, 0, x_12);
x_20 = l_Lean_Meta_acyclic___lambda__2___closed__2;
x_21 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
x_22 = l_Lean_Meta_acyclic_go___closed__11;
x_23 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_14, x_23, x_3, x_4, x_5, x_6, x_16);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_acyclic___lambda__1(x_12, x_1, x_2, x_25, x_3, x_4, x_5, x_6, x_26);
lean_dec(x_25);
lean_dec(x_12);
return x_27;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_8);
if (x_44 == 0)
{
return x_8;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_8, 0);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_8);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_acyclic___lambda__2), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_acyclic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_acyclic___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_772_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_acyclic_go___closed__6;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Acyclic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_acyclic_go___closed__1 = _init_l_Lean_Meta_acyclic_go___closed__1();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__1);
l_Lean_Meta_acyclic_go___closed__2 = _init_l_Lean_Meta_acyclic_go___closed__2();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__2);
l_Lean_Meta_acyclic_go___closed__3 = _init_l_Lean_Meta_acyclic_go___closed__3();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__3);
l_Lean_Meta_acyclic_go___closed__4 = _init_l_Lean_Meta_acyclic_go___closed__4();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__4);
l_Lean_Meta_acyclic_go___closed__5 = _init_l_Lean_Meta_acyclic_go___closed__5();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__5);
l_Lean_Meta_acyclic_go___closed__6 = _init_l_Lean_Meta_acyclic_go___closed__6();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__6);
l_Lean_Meta_acyclic_go___closed__7 = _init_l_Lean_Meta_acyclic_go___closed__7();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__7);
l_Lean_Meta_acyclic_go___closed__8 = _init_l_Lean_Meta_acyclic_go___closed__8();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__8);
l_Lean_Meta_acyclic_go___closed__9 = _init_l_Lean_Meta_acyclic_go___closed__9();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__9);
l_Lean_Meta_acyclic_go___closed__10 = _init_l_Lean_Meta_acyclic_go___closed__10();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__10);
l_Lean_Meta_acyclic_go___closed__11 = _init_l_Lean_Meta_acyclic_go___closed__11();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__11);
l_Lean_Meta_acyclic_go___closed__12 = _init_l_Lean_Meta_acyclic_go___closed__12();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__12);
l_Lean_Meta_acyclic_go___closed__13 = _init_l_Lean_Meta_acyclic_go___closed__13();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__13);
l_Lean_Meta_acyclic_go___closed__14 = _init_l_Lean_Meta_acyclic_go___closed__14();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__14);
l_Lean_Meta_acyclic_go___closed__15 = _init_l_Lean_Meta_acyclic_go___closed__15();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__15);
l_Lean_Meta_acyclic_go___closed__16 = _init_l_Lean_Meta_acyclic_go___closed__16();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__16);
l_Lean_Meta_acyclic_go___closed__17 = _init_l_Lean_Meta_acyclic_go___closed__17();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__17);
l_Lean_Meta_acyclic_go___closed__18 = _init_l_Lean_Meta_acyclic_go___closed__18();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__18);
l_Lean_Meta_acyclic_go___closed__19 = _init_l_Lean_Meta_acyclic_go___closed__19();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__19);
l_Lean_Meta_acyclic_go___closed__20 = _init_l_Lean_Meta_acyclic_go___closed__20();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__20);
l_Lean_Meta_acyclic_go___closed__21 = _init_l_Lean_Meta_acyclic_go___closed__21();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__21);
l_Lean_Meta_acyclic_go___closed__22 = _init_l_Lean_Meta_acyclic_go___closed__22();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__22);
l_Lean_Meta_acyclic_go___closed__23 = _init_l_Lean_Meta_acyclic_go___closed__23();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__23);
l_Lean_Meta_acyclic_go___closed__24 = _init_l_Lean_Meta_acyclic_go___closed__24();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__24);
l_Lean_Meta_acyclic_go___closed__25 = _init_l_Lean_Meta_acyclic_go___closed__25();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__25);
l_Lean_Meta_acyclic_go___closed__26 = _init_l_Lean_Meta_acyclic_go___closed__26();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__26);
l_Lean_Meta_acyclic_go___closed__27 = _init_l_Lean_Meta_acyclic_go___closed__27();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__27);
l_Lean_Meta_acyclic_go___closed__28 = _init_l_Lean_Meta_acyclic_go___closed__28();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__28);
l_Lean_Meta_acyclic_go___closed__29 = _init_l_Lean_Meta_acyclic_go___closed__29();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__29);
l_Lean_Meta_acyclic_go___closed__30 = _init_l_Lean_Meta_acyclic_go___closed__30();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__30);
l_Lean_Meta_acyclic_go___closed__31 = _init_l_Lean_Meta_acyclic_go___closed__31();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__31);
l_Lean_Meta_acyclic_go___closed__32 = _init_l_Lean_Meta_acyclic_go___closed__32();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__32);
l_Lean_Meta_acyclic_go___closed__33 = _init_l_Lean_Meta_acyclic_go___closed__33();
lean_mark_persistent(l_Lean_Meta_acyclic_go___closed__33);
l_Lean_Meta_acyclic___lambda__1___closed__1 = _init_l_Lean_Meta_acyclic___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_acyclic___lambda__1___closed__1);
l_Lean_Meta_acyclic___lambda__1___closed__2 = _init_l_Lean_Meta_acyclic___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_acyclic___lambda__1___closed__2);
l_Lean_Meta_acyclic___lambda__2___closed__1 = _init_l_Lean_Meta_acyclic___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_acyclic___lambda__2___closed__1);
l_Lean_Meta_acyclic___lambda__2___closed__2 = _init_l_Lean_Meta_acyclic___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_acyclic___lambda__2___closed__2);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_772_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
