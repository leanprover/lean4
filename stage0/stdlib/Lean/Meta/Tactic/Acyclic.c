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
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_779_(lean_object*);
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
x_1 = lean_mk_string_from_bytes("Meta", 4);
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
x_1 = lean_mk_string_from_bytes("Tactic", 6);
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
x_1 = lean_mk_string_from_bytes("acyclic", 7);
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
x_1 = lean_mk_string_from_bytes("failed with\n", 12);
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
x_1 = lean_mk_string_from_bytes("", 0);
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
x_1 = lean_mk_string_from_bytes("SizeOf", 6);
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
x_1 = lean_mk_string_from_bytes("sizeOf", 6);
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
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 12);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 1, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 2, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 3, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 4, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 5, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 6, x_5);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 7, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 8, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
return x_6;
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
x_1 = lean_mk_string_from_bytes("Nat", 3);
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
x_1 = lean_mk_string_from_bytes("lt_of_lt_of_eq", 14);
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
x_1 = lean_mk_string_from_bytes("lt_irrefl", 9);
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
x_1 = lean_mk_string_from_bytes("succeeded", 9);
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
lean_object* x_10; lean_object* x_20; lean_object* x_21; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Lean_Meta_acyclic_go___closed__16;
x_51 = lean_array_push(x_50, x_3);
x_52 = l_Lean_Meta_acyclic_go___closed__15;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_53 = l_Lean_Meta_mkAppM(x_52, x_51, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_array_push(x_50, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_57 = l_Lean_Meta_mkAppM(x_52, x_56, x_5, x_6, x_7, x_8, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_54);
x_60 = l_Lean_Meta_mkLT(x_54, x_58, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_box(0);
lean_inc(x_5);
x_64 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_61, x_63, x_5, x_6, x_7, x_8, x_62);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Meta_acyclic_go___closed__17;
x_68 = l_Lean_Meta_SimpExtension_getTheorems(x_67, x_7, x_8, x_66);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Expr_mvarId_x21(x_65);
x_72 = lean_array_push(x_50, x_69);
x_73 = lean_box(0);
x_74 = l_Lean_Meta_acyclic_go___closed__18;
x_75 = l_Lean_Meta_acyclic_go___closed__23;
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_72);
lean_ctor_set(x_77, 2, x_75);
lean_ctor_set(x_77, 3, x_73);
lean_ctor_set(x_77, 4, x_76);
x_78 = 1;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_79 = l_Lean_Meta_simpTarget(x_71, x_77, x_73, x_78, x_5, x_6, x_7, x_8, x_70);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_82 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Expr_appFn_x21(x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_86 = l_Lean_Meta_mkCongrArg(x_85, x_83, x_5, x_6, x_7, x_8, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = l_Lean_Meta_acyclic_go___closed__28;
x_90 = lean_array_push(x_89, x_65);
x_91 = lean_array_push(x_90, x_87);
x_92 = l_Lean_Meta_acyclic_go___closed__27;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_93 = l_Lean_Meta_mkAppM(x_92, x_91, x_5, x_6, x_7, x_8, x_88);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_array_push(x_50, x_54);
x_97 = l_Lean_Meta_acyclic_go___closed__30;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_98 = l_Lean_Meta_mkAppM(x_97, x_96, x_5, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_1);
x_101 = l_Lean_Meta_getMVarType(x_1, x_5, x_6, x_7, x_8, x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_mkApp(x_99, x_94);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_105 = l_Lean_Meta_mkFalseElim(x_102, x_104, x_5, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l_Lean_Meta_assignExprMVar(x_1, x_106, x_5, x_6, x_7, x_8, x_107);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
lean_dec(x_108);
x_110 = l_Lean_Meta_acyclic_go___closed__6;
x_111 = lean_st_ref_get(x_8, x_109);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_112, 3);
lean_inc(x_113);
lean_dec(x_112);
x_114 = lean_ctor_get_uint8(x_113, sizeof(void*)*1);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_111, 1);
lean_inc(x_115);
lean_dec(x_111);
x_116 = l_Lean_Meta_acyclic_go___closed__31;
x_117 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_118 = lean_apply_6(x_116, x_117, x_5, x_6, x_7, x_8, x_115);
if (lean_obj_tag(x_118) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = x_118;
goto block_19;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
x_20 = x_119;
x_21 = x_120;
goto block_49;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_121 = lean_ctor_get(x_111, 1);
lean_inc(x_121);
lean_dec(x_111);
x_122 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_110, x_5, x_6, x_7, x_8, x_121);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = l_Lean_Meta_acyclic_go___closed__31;
x_126 = lean_unbox(x_123);
lean_dec(x_123);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_128 = lean_apply_6(x_125, x_127, x_5, x_6, x_7, x_8, x_124);
if (lean_obj_tag(x_128) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = x_128;
goto block_19;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_20 = x_129;
x_21 = x_130;
goto block_49;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = l_Lean_Meta_acyclic_go___closed__33;
x_132 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_110, x_131, x_5, x_6, x_7, x_8, x_124);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_135 = lean_apply_6(x_125, x_133, x_5, x_6, x_7, x_8, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = x_135;
goto block_19;
}
else
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_20 = x_136;
x_21 = x_137;
goto block_49;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_1);
x_138 = lean_ctor_get(x_105, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_105, 1);
lean_inc(x_139);
lean_dec(x_105);
x_20 = x_138;
x_21 = x_139;
goto block_49;
}
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_99);
lean_dec(x_94);
lean_dec(x_1);
x_140 = lean_ctor_get(x_101, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_101, 1);
lean_inc(x_141);
lean_dec(x_101);
x_20 = x_140;
x_21 = x_141;
goto block_49;
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_94);
lean_dec(x_1);
x_142 = lean_ctor_get(x_98, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_98, 1);
lean_inc(x_143);
lean_dec(x_98);
x_20 = x_142;
x_21 = x_143;
goto block_49;
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_54);
lean_dec(x_1);
x_144 = lean_ctor_get(x_93, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_93, 1);
lean_inc(x_145);
lean_dec(x_93);
x_20 = x_144;
x_21 = x_145;
goto block_49;
}
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_1);
x_146 = lean_ctor_get(x_86, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_86, 1);
lean_inc(x_147);
lean_dec(x_86);
x_20 = x_146;
x_21 = x_147;
goto block_49;
}
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_1);
x_148 = lean_ctor_get(x_82, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_82, 1);
lean_inc(x_149);
lean_dec(x_82);
x_20 = x_148;
x_21 = x_149;
goto block_49;
}
}
else
{
uint8_t x_150; 
lean_dec(x_80);
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_79);
if (x_150 == 0)
{
lean_object* x_151; uint8_t x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_79, 0);
lean_dec(x_151);
x_152 = 0;
x_153 = lean_box(x_152);
lean_ctor_set(x_79, 0, x_153);
x_10 = x_79;
goto block_19;
}
else
{
lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_79, 1);
lean_inc(x_154);
lean_dec(x_79);
x_155 = 0;
x_156 = lean_box(x_155);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
x_10 = x_157;
goto block_19;
}
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec(x_65);
lean_dec(x_54);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_ctor_get(x_79, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_79, 1);
lean_inc(x_159);
lean_dec(x_79);
x_20 = x_158;
x_21 = x_159;
goto block_49;
}
}
else
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_54);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_ctor_get(x_60, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_60, 1);
lean_inc(x_161);
lean_dec(x_60);
x_20 = x_160;
x_21 = x_161;
goto block_49;
}
}
else
{
lean_object* x_162; lean_object* x_163; 
lean_dec(x_54);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_57, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_57, 1);
lean_inc(x_163);
lean_dec(x_57);
x_20 = x_162;
x_21 = x_163;
goto block_49;
}
}
else
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_164 = lean_ctor_get(x_53, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_53, 1);
lean_inc(x_165);
lean_dec(x_53);
x_20 = x_164;
x_21 = x_165;
goto block_49;
}
block_19:
{
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
block_49:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_22 = l_Lean_Meta_acyclic_go___closed__6;
x_38 = lean_st_ref_get(x_8, x_21);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 3);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*1);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = 0;
x_23 = x_43;
x_24 = x_42;
goto block_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_dec(x_38);
x_45 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at___private_Lean_Meta_Basic_0__Lean_Meta_processPostponedStep___spec__14(x_22, x_5, x_6, x_7, x_8, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_unbox(x_46);
lean_dec(x_46);
x_23 = x_48;
x_24 = x_47;
goto block_37;
}
block_37:
{
lean_object* x_25; 
x_25 = l_Lean_Meta_acyclic_go___closed__7;
if (x_23 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_apply_6(x_25, x_26, x_5, x_6, x_7, x_8, x_24);
x_10 = x_27;
goto block_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_28 = l_Lean_Exception_toMessageData(x_20);
x_29 = l_Lean_Meta_acyclic_go___closed__9;
x_30 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = l_Lean_Meta_acyclic_go___closed__11;
x_32 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__1(x_22, x_32, x_5, x_6, x_7, x_8, x_24);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_apply_6(x_25, x_34, x_5, x_6, x_7, x_8, x_35);
x_10 = x_36;
goto block_19;
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
x_1 = lean_mk_string_from_bytes("Eq", 2);
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
x_1 = lean_mk_string_from_bytes("type: ", 6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_779_(lean_object* x_1) {
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
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_779_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
