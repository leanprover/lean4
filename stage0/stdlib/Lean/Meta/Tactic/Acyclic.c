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
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__15;
static lean_object* l_Lean_MVarId_acyclic_go___closed__30;
static lean_object* l_Lean_MVarId_acyclic_go___closed__13;
static lean_object* l_Lean_MVarId_acyclic_go___closed__18;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__3;
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__3;
static lean_object* l_Lean_MVarId_acyclic_go___closed__27;
static lean_object* l_Lean_MVarId_acyclic_go___closed__25;
uint32_t l_UInt32_ofNatTruncate(lean_object*);
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__2;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__20;
lean_object* l_Lean_Meta_isConstructorApp_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__10;
static lean_object* l_Lean_MVarId_acyclic_go___closed__22;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__9;
static lean_object* l_Lean_MVarId_acyclic_go___closed__17;
static lean_object* l_Lean_MVarId_acyclic_go___closed__32;
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__12;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__34;
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__8;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__1;
lean_object* l_Lean_Exception_toMessageData(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__36;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__29;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__12;
static lean_object* l_Lean_MVarId_acyclic___lambda__2___closed__1;
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__1;
static lean_object* l_Lean_MVarId_acyclic_go___closed__19;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__23;
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__6;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__26;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTarget(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__7;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__5;
static lean_object* l_Lean_MVarId_acyclic_go___closed__9;
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__13;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__14;
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__10;
extern lean_object* l_Lean_Meta_simpExtension;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__11;
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__31;
lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic___lambda__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844_(lean_object*);
lean_object* l_Lean_Meta_mkLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic___lambda__1___closed__1;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__33;
static lean_object* l_Lean_MVarId_acyclic_go___closed__14;
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__16;
static lean_object* l_Lean_MVarId_acyclic_go___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__11;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__21;
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__4;
static lean_object* l_Lean_MVarId_acyclic___lambda__2___closed__2;
static uint32_t l_Lean_MVarId_acyclic_go___closed__15;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__16;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__24;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__7;
static lean_object* l_Lean_MVarId_acyclic_go___closed__6;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__8;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__35;
static lean_object* l_Lean_MVarId_acyclic_go___closed__28;
static lean_object* l_Lean_MVarId_acyclic_go___closed__5;
static lean_object* l_Lean_MVarId_acyclic_go___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Expr_isFVar(x_1);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
x_12 = l_Lean_Expr_occurs(x_1, x_2);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_16; 
x_16 = l_Lean_Meta_isConstructorApp_x27(x_2, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tactic", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("acyclic", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_MVarId_acyclic_go___closed__1;
x_2 = l_Lean_MVarId_acyclic_go___closed__2;
x_3 = l_Lean_MVarId_acyclic_go___closed__3;
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic_go___lambda__1___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed with\n", 12, 12);
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
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("SizeOf", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sizeOf", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__10;
x_2 = l_Lean_MVarId_acyclic_go___closed__11;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtension;
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 19);
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
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 9, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 10, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 11, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 12, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 13, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 14, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 15, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 16, x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 17, x_4);
lean_ctor_set_uint8(x_6, sizeof(void*)*2 + 18, x_4);
return x_6;
}
}
static uint32_t _init_l_Lean_MVarId_acyclic_go___closed__15() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_UInt32_ofNatTruncate(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_acyclic_go___closed__16;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_MVarId_acyclic_go___closed__17;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__19;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__21() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_MVarId_acyclic_go___closed__18;
x_3 = l_Lean_MVarId_acyclic_go___closed__20;
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__20;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__24;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__26() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_MVarId_acyclic_go___closed__25;
x_3 = l_Lean_MVarId_acyclic_go___closed__24;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__20;
x_2 = l_Lean_MVarId_acyclic_go___closed__26;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__23;
x_2 = l_Lean_MVarId_acyclic_go___closed__27;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__29() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt_of_lt_of_eq", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__29;
x_2 = l_Lean_MVarId_acyclic_go___closed__30;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt_irrefl", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__29;
x_2 = l_Lean_MVarId_acyclic_go___closed__32;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic_go___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("succeeded", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__35;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_box(0);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_3);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_array_mk(x_82);
x_84 = l_Lean_MVarId_acyclic_go___closed__12;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_85 = l_Lean_Meta_mkAppM(x_84, x_83, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_ctor_get(x_85, 1);
lean_ctor_set_tag(x_85, 1);
lean_ctor_set(x_85, 1, x_81);
lean_ctor_set(x_85, 0, x_4);
x_89 = lean_array_mk(x_85);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_90 = l_Lean_Meta_mkAppM(x_84, x_89, x_5, x_6, x_7, x_8, x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_87);
x_93 = l_Lean_Meta_mkLT(x_87, x_91, x_5, x_6, x_7, x_8, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_box(0);
lean_inc(x_5);
x_97 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_94, x_96, x_5, x_6, x_7, x_8, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_MVarId_acyclic_go___closed__13;
x_101 = l_Lean_Meta_SimpExtension_getTheorems(x_100, x_7, x_8, x_99);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint32_t x_107; lean_object* x_108; uint32_t x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_103 = lean_ctor_get(x_101, 1);
x_104 = l_Lean_Expr_mvarId_x21(x_98);
lean_ctor_set_tag(x_101, 1);
lean_ctor_set(x_101, 1, x_81);
x_105 = lean_array_mk(x_101);
x_106 = lean_box(0);
x_107 = 0;
x_108 = l_Lean_MVarId_acyclic_go___closed__14;
x_109 = l_Lean_MVarId_acyclic_go___closed__15;
x_110 = l_Lean_MVarId_acyclic_go___closed__21;
x_111 = lean_unsigned_to_nat(0u);
x_112 = 0;
x_113 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_105);
lean_ctor_set(x_113, 2, x_110);
lean_ctor_set(x_113, 3, x_106);
lean_ctor_set(x_113, 4, x_111);
lean_ctor_set_uint32(x_113, sizeof(void*)*5, x_109);
lean_ctor_set_uint32(x_113, sizeof(void*)*5 + 4, x_107);
lean_ctor_set_uint8(x_113, sizeof(void*)*5 + 8, x_112);
x_114 = l_Lean_MVarId_acyclic_go___closed__22;
x_115 = 1;
x_116 = l_Lean_MVarId_acyclic_go___closed__28;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_117 = l_Lean_Meta_simpTarget(x_104, x_113, x_114, x_106, x_115, x_116, x_5, x_6, x_7, x_8, x_103);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
lean_dec(x_117);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_121 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_120);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
x_125 = l_Lean_Expr_appFn_x21(x_87);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_126 = l_Lean_Meta_mkCongrArg(x_125, x_123, x_5, x_6, x_7, x_8, x_124);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_128 = lean_ctor_get(x_126, 1);
lean_ctor_set_tag(x_126, 1);
lean_ctor_set(x_126, 1, x_81);
lean_ctor_set_tag(x_121, 1);
lean_ctor_set(x_121, 1, x_126);
lean_ctor_set(x_121, 0, x_98);
x_129 = lean_array_mk(x_121);
x_130 = l_Lean_MVarId_acyclic_go___closed__31;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_131 = l_Lean_Meta_mkAppM(x_130, x_129, x_5, x_6, x_7, x_8, x_128);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_131, 1);
lean_ctor_set_tag(x_131, 1);
lean_ctor_set(x_131, 1, x_81);
lean_ctor_set(x_131, 0, x_87);
x_135 = lean_array_mk(x_131);
x_136 = l_Lean_MVarId_acyclic_go___closed__33;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_137 = l_Lean_Meta_mkAppM(x_136, x_135, x_5, x_6, x_7, x_8, x_134);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
lean_inc(x_1);
x_140 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = l_Lean_Expr_app___override(x_138, x_133);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_144 = l_Lean_Meta_mkFalseElim(x_141, x_143, x_5, x_6, x_7, x_8, x_142);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_145, x_5, x_6, x_7, x_8, x_146);
x_148 = lean_ctor_get(x_147, 1);
lean_inc(x_148);
lean_dec(x_147);
x_149 = l_Lean_MVarId_acyclic_go___closed__4;
x_150 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_149, x_5, x_6, x_7, x_8, x_148);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = l_Lean_MVarId_acyclic_go___closed__34;
x_154 = lean_unbox(x_151);
lean_dec(x_151);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_156 = lean_apply_6(x_153, x_155, x_5, x_6, x_7, x_8, x_152);
if (lean_obj_tag(x_156) == 0)
{
uint8_t x_157; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_157 = !lean_is_exclusive(x_156);
if (x_157 == 0)
{
return x_156;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_156, 0);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_156);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_156, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_156, 1);
lean_inc(x_162);
lean_dec(x_156);
x_10 = x_161;
x_11 = x_162;
goto block_80;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_163 = l_Lean_MVarId_acyclic_go___closed__36;
x_164 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_149, x_163, x_5, x_6, x_7, x_8, x_152);
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_167 = lean_apply_6(x_153, x_165, x_5, x_6, x_7, x_8, x_166);
if (lean_obj_tag(x_167) == 0)
{
uint8_t x_168; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_168 = !lean_is_exclusive(x_167);
if (x_168 == 0)
{
return x_167;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_167, 0);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_167);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_167, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_167, 1);
lean_inc(x_173);
lean_dec(x_167);
x_10 = x_172;
x_11 = x_173;
goto block_80;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_1);
x_174 = lean_ctor_get(x_144, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_144, 1);
lean_inc(x_175);
lean_dec(x_144);
x_10 = x_174;
x_11 = x_175;
goto block_80;
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_138);
lean_dec(x_133);
lean_dec(x_1);
x_176 = lean_ctor_get(x_140, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_140, 1);
lean_inc(x_177);
lean_dec(x_140);
x_10 = x_176;
x_11 = x_177;
goto block_80;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_133);
lean_dec(x_1);
x_178 = lean_ctor_get(x_137, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_137, 1);
lean_inc(x_179);
lean_dec(x_137);
x_10 = x_178;
x_11 = x_179;
goto block_80;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_180 = lean_ctor_get(x_131, 0);
x_181 = lean_ctor_get(x_131, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_131);
x_182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_182, 0, x_87);
lean_ctor_set(x_182, 1, x_81);
x_183 = lean_array_mk(x_182);
x_184 = l_Lean_MVarId_acyclic_go___closed__33;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_185 = l_Lean_Meta_mkAppM(x_184, x_183, x_5, x_6, x_7, x_8, x_181);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_1);
x_188 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Expr_app___override(x_186, x_180);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_192 = l_Lean_Meta_mkFalseElim(x_189, x_191, x_5, x_6, x_7, x_8, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_193, x_5, x_6, x_7, x_8, x_194);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
lean_dec(x_195);
x_197 = l_Lean_MVarId_acyclic_go___closed__4;
x_198 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_197, x_5, x_6, x_7, x_8, x_196);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = l_Lean_MVarId_acyclic_go___closed__34;
x_202 = lean_unbox(x_199);
lean_dec(x_199);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_204 = lean_apply_6(x_201, x_203, x_5, x_6, x_7, x_8, x_200);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_204, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_204, 1);
lean_inc(x_210);
lean_dec(x_204);
x_10 = x_209;
x_11 = x_210;
goto block_80;
}
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = l_Lean_MVarId_acyclic_go___closed__36;
x_212 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_197, x_211, x_5, x_6, x_7, x_8, x_200);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_215 = lean_apply_6(x_201, x_213, x_5, x_6, x_7, x_8, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; 
x_220 = lean_ctor_get(x_215, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_215, 1);
lean_inc(x_221);
lean_dec(x_215);
x_10 = x_220;
x_11 = x_221;
goto block_80;
}
}
}
else
{
lean_object* x_222; lean_object* x_223; 
lean_dec(x_1);
x_222 = lean_ctor_get(x_192, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_192, 1);
lean_inc(x_223);
lean_dec(x_192);
x_10 = x_222;
x_11 = x_223;
goto block_80;
}
}
else
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_1);
x_224 = lean_ctor_get(x_188, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_188, 1);
lean_inc(x_225);
lean_dec(x_188);
x_10 = x_224;
x_11 = x_225;
goto block_80;
}
}
else
{
lean_object* x_226; lean_object* x_227; 
lean_dec(x_180);
lean_dec(x_1);
x_226 = lean_ctor_get(x_185, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_185, 1);
lean_inc(x_227);
lean_dec(x_185);
x_10 = x_226;
x_11 = x_227;
goto block_80;
}
}
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_87);
lean_dec(x_1);
x_228 = lean_ctor_get(x_131, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_131, 1);
lean_inc(x_229);
lean_dec(x_131);
x_10 = x_228;
x_11 = x_229;
goto block_80;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_230 = lean_ctor_get(x_126, 0);
x_231 = lean_ctor_get(x_126, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_126);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_81);
lean_ctor_set_tag(x_121, 1);
lean_ctor_set(x_121, 1, x_232);
lean_ctor_set(x_121, 0, x_98);
x_233 = lean_array_mk(x_121);
x_234 = l_Lean_MVarId_acyclic_go___closed__31;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_235 = l_Lean_Meta_mkAppM(x_234, x_233, x_5, x_6, x_7, x_8, x_231);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_238;
 lean_ctor_set_tag(x_239, 1);
}
lean_ctor_set(x_239, 0, x_87);
lean_ctor_set(x_239, 1, x_81);
x_240 = lean_array_mk(x_239);
x_241 = l_Lean_MVarId_acyclic_go___closed__33;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_242 = l_Lean_Meta_mkAppM(x_241, x_240, x_5, x_6, x_7, x_8, x_237);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
lean_inc(x_1);
x_245 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = l_Lean_Expr_app___override(x_243, x_236);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_249 = l_Lean_Meta_mkFalseElim(x_246, x_248, x_5, x_6, x_7, x_8, x_247);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
x_252 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_250, x_5, x_6, x_7, x_8, x_251);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = l_Lean_MVarId_acyclic_go___closed__4;
x_255 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_254, x_5, x_6, x_7, x_8, x_253);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = l_Lean_MVarId_acyclic_go___closed__34;
x_259 = lean_unbox(x_256);
lean_dec(x_256);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; 
x_260 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_261 = lean_apply_6(x_258, x_260, x_5, x_6, x_7, x_8, x_257);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
if (lean_is_scalar(x_264)) {
 x_265 = lean_alloc_ctor(0, 2, 0);
} else {
 x_265 = x_264;
}
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_263);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_261, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_261, 1);
lean_inc(x_267);
lean_dec(x_261);
x_10 = x_266;
x_11 = x_267;
goto block_80;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_268 = l_Lean_MVarId_acyclic_go___closed__36;
x_269 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_254, x_268, x_5, x_6, x_7, x_8, x_257);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_272 = lean_apply_6(x_258, x_270, x_5, x_6, x_7, x_8, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; lean_object* x_278; 
x_277 = lean_ctor_get(x_272, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_272, 1);
lean_inc(x_278);
lean_dec(x_272);
x_10 = x_277;
x_11 = x_278;
goto block_80;
}
}
}
else
{
lean_object* x_279; lean_object* x_280; 
lean_dec(x_1);
x_279 = lean_ctor_get(x_249, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_249, 1);
lean_inc(x_280);
lean_dec(x_249);
x_10 = x_279;
x_11 = x_280;
goto block_80;
}
}
else
{
lean_object* x_281; lean_object* x_282; 
lean_dec(x_243);
lean_dec(x_236);
lean_dec(x_1);
x_281 = lean_ctor_get(x_245, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_245, 1);
lean_inc(x_282);
lean_dec(x_245);
x_10 = x_281;
x_11 = x_282;
goto block_80;
}
}
else
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_236);
lean_dec(x_1);
x_283 = lean_ctor_get(x_242, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_242, 1);
lean_inc(x_284);
lean_dec(x_242);
x_10 = x_283;
x_11 = x_284;
goto block_80;
}
}
else
{
lean_object* x_285; lean_object* x_286; 
lean_dec(x_87);
lean_dec(x_1);
x_285 = lean_ctor_get(x_235, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_235, 1);
lean_inc(x_286);
lean_dec(x_235);
x_10 = x_285;
x_11 = x_286;
goto block_80;
}
}
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_free_object(x_121);
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_1);
x_287 = lean_ctor_get(x_126, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_126, 1);
lean_inc(x_288);
lean_dec(x_126);
x_10 = x_287;
x_11 = x_288;
goto block_80;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_289 = lean_ctor_get(x_121, 0);
x_290 = lean_ctor_get(x_121, 1);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_121);
x_291 = l_Lean_Expr_appFn_x21(x_87);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_292 = l_Lean_Meta_mkCongrArg(x_291, x_289, x_5, x_6, x_7, x_8, x_290);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_295 = x_292;
} else {
 lean_dec_ref(x_292);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
 lean_ctor_set_tag(x_296, 1);
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_81);
x_297 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_297, 0, x_98);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_array_mk(x_297);
x_299 = l_Lean_MVarId_acyclic_go___closed__31;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_300 = l_Lean_Meta_mkAppM(x_299, x_298, x_5, x_6, x_7, x_8, x_294);
if (lean_obj_tag(x_300) == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_303 = x_300;
} else {
 lean_dec_ref(x_300);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
 lean_ctor_set_tag(x_304, 1);
}
lean_ctor_set(x_304, 0, x_87);
lean_ctor_set(x_304, 1, x_81);
x_305 = lean_array_mk(x_304);
x_306 = l_Lean_MVarId_acyclic_go___closed__33;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_307 = l_Lean_Meta_mkAppM(x_306, x_305, x_5, x_6, x_7, x_8, x_302);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
lean_inc(x_1);
x_310 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_309);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = l_Lean_Expr_app___override(x_308, x_301);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_314 = l_Lean_Meta_mkFalseElim(x_311, x_313, x_5, x_6, x_7, x_8, x_312);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_315, x_5, x_6, x_7, x_8, x_316);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
lean_dec(x_317);
x_319 = l_Lean_MVarId_acyclic_go___closed__4;
x_320 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_319, x_5, x_6, x_7, x_8, x_318);
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
x_323 = l_Lean_MVarId_acyclic_go___closed__34;
x_324 = lean_unbox(x_321);
lean_dec(x_321);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; 
x_325 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_326 = lean_apply_6(x_323, x_325, x_5, x_6, x_7, x_8, x_322);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_327 = lean_ctor_get(x_326, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_326, 1);
lean_inc(x_328);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 lean_ctor_release(x_326, 1);
 x_329 = x_326;
} else {
 lean_dec_ref(x_326);
 x_329 = lean_box(0);
}
if (lean_is_scalar(x_329)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_329;
}
lean_ctor_set(x_330, 0, x_327);
lean_ctor_set(x_330, 1, x_328);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_326, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_326, 1);
lean_inc(x_332);
lean_dec(x_326);
x_10 = x_331;
x_11 = x_332;
goto block_80;
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_333 = l_Lean_MVarId_acyclic_go___closed__36;
x_334 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_319, x_333, x_5, x_6, x_7, x_8, x_322);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_337 = lean_apply_6(x_323, x_335, x_5, x_6, x_7, x_8, x_336);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_340 = x_337;
} else {
 lean_dec_ref(x_337);
 x_340 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_340;
}
lean_ctor_set(x_341, 0, x_338);
lean_ctor_set(x_341, 1, x_339);
return x_341;
}
else
{
lean_object* x_342; lean_object* x_343; 
x_342 = lean_ctor_get(x_337, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_337, 1);
lean_inc(x_343);
lean_dec(x_337);
x_10 = x_342;
x_11 = x_343;
goto block_80;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_1);
x_344 = lean_ctor_get(x_314, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_314, 1);
lean_inc(x_345);
lean_dec(x_314);
x_10 = x_344;
x_11 = x_345;
goto block_80;
}
}
else
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_308);
lean_dec(x_301);
lean_dec(x_1);
x_346 = lean_ctor_get(x_310, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_310, 1);
lean_inc(x_347);
lean_dec(x_310);
x_10 = x_346;
x_11 = x_347;
goto block_80;
}
}
else
{
lean_object* x_348; lean_object* x_349; 
lean_dec(x_301);
lean_dec(x_1);
x_348 = lean_ctor_get(x_307, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_307, 1);
lean_inc(x_349);
lean_dec(x_307);
x_10 = x_348;
x_11 = x_349;
goto block_80;
}
}
else
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_87);
lean_dec(x_1);
x_350 = lean_ctor_get(x_300, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_300, 1);
lean_inc(x_351);
lean_dec(x_300);
x_10 = x_350;
x_11 = x_351;
goto block_80;
}
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_1);
x_352 = lean_ctor_get(x_292, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_292, 1);
lean_inc(x_353);
lean_dec(x_292);
x_10 = x_352;
x_11 = x_353;
goto block_80;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_1);
x_354 = lean_ctor_get(x_121, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_121, 1);
lean_inc(x_355);
lean_dec(x_121);
x_10 = x_354;
x_11 = x_355;
goto block_80;
}
}
else
{
uint8_t x_356; 
lean_dec(x_119);
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_356 = !lean_is_exclusive(x_117);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_117, 0);
lean_dec(x_357);
x_358 = lean_box(x_112);
lean_ctor_set(x_117, 0, x_358);
return x_117;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_117, 1);
lean_inc(x_359);
lean_dec(x_117);
x_360 = lean_box(x_112);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_360);
lean_ctor_set(x_361, 1, x_359);
return x_361;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; 
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_2);
lean_dec(x_1);
x_362 = lean_ctor_get(x_117, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_117, 1);
lean_inc(x_363);
lean_dec(x_117);
x_10 = x_362;
x_11 = x_363;
goto block_80;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; uint32_t x_370; lean_object* x_371; uint32_t x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; uint8_t x_378; lean_object* x_379; lean_object* x_380; 
x_364 = lean_ctor_get(x_101, 0);
x_365 = lean_ctor_get(x_101, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_101);
x_366 = l_Lean_Expr_mvarId_x21(x_98);
x_367 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_367, 0, x_364);
lean_ctor_set(x_367, 1, x_81);
x_368 = lean_array_mk(x_367);
x_369 = lean_box(0);
x_370 = 0;
x_371 = l_Lean_MVarId_acyclic_go___closed__14;
x_372 = l_Lean_MVarId_acyclic_go___closed__15;
x_373 = l_Lean_MVarId_acyclic_go___closed__21;
x_374 = lean_unsigned_to_nat(0u);
x_375 = 0;
x_376 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_376, 0, x_371);
lean_ctor_set(x_376, 1, x_368);
lean_ctor_set(x_376, 2, x_373);
lean_ctor_set(x_376, 3, x_369);
lean_ctor_set(x_376, 4, x_374);
lean_ctor_set_uint32(x_376, sizeof(void*)*5, x_372);
lean_ctor_set_uint32(x_376, sizeof(void*)*5 + 4, x_370);
lean_ctor_set_uint8(x_376, sizeof(void*)*5 + 8, x_375);
x_377 = l_Lean_MVarId_acyclic_go___closed__22;
x_378 = 1;
x_379 = l_Lean_MVarId_acyclic_go___closed__28;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_380 = l_Lean_Meta_simpTarget(x_366, x_376, x_377, x_369, x_378, x_379, x_5, x_6, x_7, x_8, x_365);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec(x_381);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_380, 1);
lean_inc(x_383);
lean_dec(x_380);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_384 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_383);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_384, 1);
lean_inc(x_386);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 lean_ctor_release(x_384, 1);
 x_387 = x_384;
} else {
 lean_dec_ref(x_384);
 x_387 = lean_box(0);
}
x_388 = l_Lean_Expr_appFn_x21(x_87);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_389 = l_Lean_Meta_mkCongrArg(x_388, x_385, x_5, x_6, x_7, x_8, x_386);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_392 = x_389;
} else {
 lean_dec_ref(x_389);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 2, 0);
} else {
 x_393 = x_392;
 lean_ctor_set_tag(x_393, 1);
}
lean_ctor_set(x_393, 0, x_390);
lean_ctor_set(x_393, 1, x_81);
if (lean_is_scalar(x_387)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_387;
 lean_ctor_set_tag(x_394, 1);
}
lean_ctor_set(x_394, 0, x_98);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_array_mk(x_394);
x_396 = l_Lean_MVarId_acyclic_go___closed__31;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_397 = l_Lean_Meta_mkAppM(x_396, x_395, x_5, x_6, x_7, x_8, x_391);
if (lean_obj_tag(x_397) == 0)
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_398 = lean_ctor_get(x_397, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_397, 1);
lean_inc(x_399);
if (lean_is_exclusive(x_397)) {
 lean_ctor_release(x_397, 0);
 lean_ctor_release(x_397, 1);
 x_400 = x_397;
} else {
 lean_dec_ref(x_397);
 x_400 = lean_box(0);
}
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 2, 0);
} else {
 x_401 = x_400;
 lean_ctor_set_tag(x_401, 1);
}
lean_ctor_set(x_401, 0, x_87);
lean_ctor_set(x_401, 1, x_81);
x_402 = lean_array_mk(x_401);
x_403 = l_Lean_MVarId_acyclic_go___closed__33;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_404 = l_Lean_Meta_mkAppM(x_403, x_402, x_5, x_6, x_7, x_8, x_399);
if (lean_obj_tag(x_404) == 0)
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_404, 1);
lean_inc(x_406);
lean_dec(x_404);
lean_inc(x_1);
x_407 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_406);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = l_Lean_Expr_app___override(x_405, x_398);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_411 = l_Lean_Meta_mkFalseElim(x_408, x_410, x_5, x_6, x_7, x_8, x_409);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
lean_dec(x_411);
x_414 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_412, x_5, x_6, x_7, x_8, x_413);
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
x_416 = l_Lean_MVarId_acyclic_go___closed__4;
x_417 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_416, x_5, x_6, x_7, x_8, x_415);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
lean_dec(x_417);
x_420 = l_Lean_MVarId_acyclic_go___closed__34;
x_421 = lean_unbox(x_418);
lean_dec(x_418);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; 
x_422 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_423 = lean_apply_6(x_420, x_422, x_5, x_6, x_7, x_8, x_419);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_426 = x_423;
} else {
 lean_dec_ref(x_423);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_427 = lean_alloc_ctor(0, 2, 0);
} else {
 x_427 = x_426;
}
lean_ctor_set(x_427, 0, x_424);
lean_ctor_set(x_427, 1, x_425);
return x_427;
}
else
{
lean_object* x_428; lean_object* x_429; 
x_428 = lean_ctor_get(x_423, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_423, 1);
lean_inc(x_429);
lean_dec(x_423);
x_10 = x_428;
x_11 = x_429;
goto block_80;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_430 = l_Lean_MVarId_acyclic_go___closed__36;
x_431 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_416, x_430, x_5, x_6, x_7, x_8, x_419);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_434 = lean_apply_6(x_420, x_432, x_5, x_6, x_7, x_8, x_433);
if (lean_obj_tag(x_434) == 0)
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_437 = x_434;
} else {
 lean_dec_ref(x_434);
 x_437 = lean_box(0);
}
if (lean_is_scalar(x_437)) {
 x_438 = lean_alloc_ctor(0, 2, 0);
} else {
 x_438 = x_437;
}
lean_ctor_set(x_438, 0, x_435);
lean_ctor_set(x_438, 1, x_436);
return x_438;
}
else
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_434, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_434, 1);
lean_inc(x_440);
lean_dec(x_434);
x_10 = x_439;
x_11 = x_440;
goto block_80;
}
}
}
else
{
lean_object* x_441; lean_object* x_442; 
lean_dec(x_1);
x_441 = lean_ctor_get(x_411, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_411, 1);
lean_inc(x_442);
lean_dec(x_411);
x_10 = x_441;
x_11 = x_442;
goto block_80;
}
}
else
{
lean_object* x_443; lean_object* x_444; 
lean_dec(x_405);
lean_dec(x_398);
lean_dec(x_1);
x_443 = lean_ctor_get(x_407, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_407, 1);
lean_inc(x_444);
lean_dec(x_407);
x_10 = x_443;
x_11 = x_444;
goto block_80;
}
}
else
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_398);
lean_dec(x_1);
x_445 = lean_ctor_get(x_404, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_404, 1);
lean_inc(x_446);
lean_dec(x_404);
x_10 = x_445;
x_11 = x_446;
goto block_80;
}
}
else
{
lean_object* x_447; lean_object* x_448; 
lean_dec(x_87);
lean_dec(x_1);
x_447 = lean_ctor_get(x_397, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_397, 1);
lean_inc(x_448);
lean_dec(x_397);
x_10 = x_447;
x_11 = x_448;
goto block_80;
}
}
else
{
lean_object* x_449; lean_object* x_450; 
lean_dec(x_387);
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_1);
x_449 = lean_ctor_get(x_389, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_389, 1);
lean_inc(x_450);
lean_dec(x_389);
x_10 = x_449;
x_11 = x_450;
goto block_80;
}
}
else
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_1);
x_451 = lean_ctor_get(x_384, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_384, 1);
lean_inc(x_452);
lean_dec(x_384);
x_10 = x_451;
x_11 = x_452;
goto block_80;
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_382);
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_453 = lean_ctor_get(x_380, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_454 = x_380;
} else {
 lean_dec_ref(x_380);
 x_454 = lean_box(0);
}
x_455 = lean_box(x_375);
if (lean_is_scalar(x_454)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_454;
}
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_453);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; 
lean_dec(x_98);
lean_dec(x_87);
lean_dec(x_2);
lean_dec(x_1);
x_457 = lean_ctor_get(x_380, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_380, 1);
lean_inc(x_458);
lean_dec(x_380);
x_10 = x_457;
x_11 = x_458;
goto block_80;
}
}
}
else
{
lean_object* x_459; lean_object* x_460; 
lean_dec(x_87);
lean_dec(x_2);
lean_dec(x_1);
x_459 = lean_ctor_get(x_93, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_93, 1);
lean_inc(x_460);
lean_dec(x_93);
x_10 = x_459;
x_11 = x_460;
goto block_80;
}
}
else
{
lean_object* x_461; lean_object* x_462; 
lean_dec(x_87);
lean_dec(x_2);
lean_dec(x_1);
x_461 = lean_ctor_get(x_90, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_90, 1);
lean_inc(x_462);
lean_dec(x_90);
x_10 = x_461;
x_11 = x_462;
goto block_80;
}
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_463 = lean_ctor_get(x_85, 0);
x_464 = lean_ctor_get(x_85, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_85);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_4);
lean_ctor_set(x_465, 1, x_81);
x_466 = lean_array_mk(x_465);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_467 = l_Lean_Meta_mkAppM(x_84, x_466, x_5, x_6, x_7, x_8, x_464);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_467, 1);
lean_inc(x_469);
lean_dec(x_467);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_463);
x_470 = l_Lean_Meta_mkLT(x_463, x_468, x_5, x_6, x_7, x_8, x_469);
if (lean_obj_tag(x_470) == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint32_t x_486; lean_object* x_487; uint32_t x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; lean_object* x_495; lean_object* x_496; 
x_471 = lean_ctor_get(x_470, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_470, 1);
lean_inc(x_472);
lean_dec(x_470);
x_473 = lean_box(0);
lean_inc(x_5);
x_474 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_471, x_473, x_5, x_6, x_7, x_8, x_472);
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
x_477 = l_Lean_MVarId_acyclic_go___closed__13;
x_478 = l_Lean_Meta_SimpExtension_getTheorems(x_477, x_7, x_8, x_476);
x_479 = lean_ctor_get(x_478, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_478, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_478)) {
 lean_ctor_release(x_478, 0);
 lean_ctor_release(x_478, 1);
 x_481 = x_478;
} else {
 lean_dec_ref(x_478);
 x_481 = lean_box(0);
}
x_482 = l_Lean_Expr_mvarId_x21(x_475);
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_483 = x_481;
 lean_ctor_set_tag(x_483, 1);
}
lean_ctor_set(x_483, 0, x_479);
lean_ctor_set(x_483, 1, x_81);
x_484 = lean_array_mk(x_483);
x_485 = lean_box(0);
x_486 = 0;
x_487 = l_Lean_MVarId_acyclic_go___closed__14;
x_488 = l_Lean_MVarId_acyclic_go___closed__15;
x_489 = l_Lean_MVarId_acyclic_go___closed__21;
x_490 = lean_unsigned_to_nat(0u);
x_491 = 0;
x_492 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_492, 0, x_487);
lean_ctor_set(x_492, 1, x_484);
lean_ctor_set(x_492, 2, x_489);
lean_ctor_set(x_492, 3, x_485);
lean_ctor_set(x_492, 4, x_490);
lean_ctor_set_uint32(x_492, sizeof(void*)*5, x_488);
lean_ctor_set_uint32(x_492, sizeof(void*)*5 + 4, x_486);
lean_ctor_set_uint8(x_492, sizeof(void*)*5 + 8, x_491);
x_493 = l_Lean_MVarId_acyclic_go___closed__22;
x_494 = 1;
x_495 = l_Lean_MVarId_acyclic_go___closed__28;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_496 = l_Lean_Meta_simpTarget(x_482, x_492, x_493, x_485, x_494, x_495, x_5, x_6, x_7, x_8, x_480);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
lean_dec(x_497);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; lean_object* x_500; 
x_499 = lean_ctor_get(x_496, 1);
lean_inc(x_499);
lean_dec(x_496);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_500 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_499);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_503 = x_500;
} else {
 lean_dec_ref(x_500);
 x_503 = lean_box(0);
}
x_504 = l_Lean_Expr_appFn_x21(x_463);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_505 = l_Lean_Meta_mkCongrArg(x_504, x_501, x_5, x_6, x_7, x_8, x_502);
if (lean_obj_tag(x_505) == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_505)) {
 lean_ctor_release(x_505, 0);
 lean_ctor_release(x_505, 1);
 x_508 = x_505;
} else {
 lean_dec_ref(x_505);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_509 = x_508;
 lean_ctor_set_tag(x_509, 1);
}
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_81);
if (lean_is_scalar(x_503)) {
 x_510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_510 = x_503;
 lean_ctor_set_tag(x_510, 1);
}
lean_ctor_set(x_510, 0, x_475);
lean_ctor_set(x_510, 1, x_509);
x_511 = lean_array_mk(x_510);
x_512 = l_Lean_MVarId_acyclic_go___closed__31;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_513 = l_Lean_Meta_mkAppM(x_512, x_511, x_5, x_6, x_7, x_8, x_507);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
if (lean_is_exclusive(x_513)) {
 lean_ctor_release(x_513, 0);
 lean_ctor_release(x_513, 1);
 x_516 = x_513;
} else {
 lean_dec_ref(x_513);
 x_516 = lean_box(0);
}
if (lean_is_scalar(x_516)) {
 x_517 = lean_alloc_ctor(1, 2, 0);
} else {
 x_517 = x_516;
 lean_ctor_set_tag(x_517, 1);
}
lean_ctor_set(x_517, 0, x_463);
lean_ctor_set(x_517, 1, x_81);
x_518 = lean_array_mk(x_517);
x_519 = l_Lean_MVarId_acyclic_go___closed__33;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_520 = l_Lean_Meta_mkAppM(x_519, x_518, x_5, x_6, x_7, x_8, x_515);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
lean_dec(x_520);
lean_inc(x_1);
x_523 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_522);
if (lean_obj_tag(x_523) == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_524 = lean_ctor_get(x_523, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_523, 1);
lean_inc(x_525);
lean_dec(x_523);
x_526 = l_Lean_Expr_app___override(x_521, x_514);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_527 = l_Lean_Meta_mkFalseElim(x_524, x_526, x_5, x_6, x_7, x_8, x_525);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; uint8_t x_537; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
x_530 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_528, x_5, x_6, x_7, x_8, x_529);
x_531 = lean_ctor_get(x_530, 1);
lean_inc(x_531);
lean_dec(x_530);
x_532 = l_Lean_MVarId_acyclic_go___closed__4;
x_533 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_532, x_5, x_6, x_7, x_8, x_531);
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
x_536 = l_Lean_MVarId_acyclic_go___closed__34;
x_537 = lean_unbox(x_534);
lean_dec(x_534);
if (x_537 == 0)
{
lean_object* x_538; lean_object* x_539; 
x_538 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_539 = lean_apply_6(x_536, x_538, x_5, x_6, x_7, x_8, x_535);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_542 = x_539;
} else {
 lean_dec_ref(x_539);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(0, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
else
{
lean_object* x_544; lean_object* x_545; 
x_544 = lean_ctor_get(x_539, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_539, 1);
lean_inc(x_545);
lean_dec(x_539);
x_10 = x_544;
x_11 = x_545;
goto block_80;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_546 = l_Lean_MVarId_acyclic_go___closed__36;
x_547 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_532, x_546, x_5, x_6, x_7, x_8, x_535);
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 1);
lean_inc(x_549);
lean_dec(x_547);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_550 = lean_apply_6(x_536, x_548, x_5, x_6, x_7, x_8, x_549);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_550)) {
 lean_ctor_release(x_550, 0);
 lean_ctor_release(x_550, 1);
 x_553 = x_550;
} else {
 lean_dec_ref(x_550);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(0, 2, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_551);
lean_ctor_set(x_554, 1, x_552);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_ctor_get(x_550, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_550, 1);
lean_inc(x_556);
lean_dec(x_550);
x_10 = x_555;
x_11 = x_556;
goto block_80;
}
}
}
else
{
lean_object* x_557; lean_object* x_558; 
lean_dec(x_1);
x_557 = lean_ctor_get(x_527, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_527, 1);
lean_inc(x_558);
lean_dec(x_527);
x_10 = x_557;
x_11 = x_558;
goto block_80;
}
}
else
{
lean_object* x_559; lean_object* x_560; 
lean_dec(x_521);
lean_dec(x_514);
lean_dec(x_1);
x_559 = lean_ctor_get(x_523, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_523, 1);
lean_inc(x_560);
lean_dec(x_523);
x_10 = x_559;
x_11 = x_560;
goto block_80;
}
}
else
{
lean_object* x_561; lean_object* x_562; 
lean_dec(x_514);
lean_dec(x_1);
x_561 = lean_ctor_get(x_520, 0);
lean_inc(x_561);
x_562 = lean_ctor_get(x_520, 1);
lean_inc(x_562);
lean_dec(x_520);
x_10 = x_561;
x_11 = x_562;
goto block_80;
}
}
else
{
lean_object* x_563; lean_object* x_564; 
lean_dec(x_463);
lean_dec(x_1);
x_563 = lean_ctor_get(x_513, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_513, 1);
lean_inc(x_564);
lean_dec(x_513);
x_10 = x_563;
x_11 = x_564;
goto block_80;
}
}
else
{
lean_object* x_565; lean_object* x_566; 
lean_dec(x_503);
lean_dec(x_475);
lean_dec(x_463);
lean_dec(x_1);
x_565 = lean_ctor_get(x_505, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_505, 1);
lean_inc(x_566);
lean_dec(x_505);
x_10 = x_565;
x_11 = x_566;
goto block_80;
}
}
else
{
lean_object* x_567; lean_object* x_568; 
lean_dec(x_475);
lean_dec(x_463);
lean_dec(x_1);
x_567 = lean_ctor_get(x_500, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_500, 1);
lean_inc(x_568);
lean_dec(x_500);
x_10 = x_567;
x_11 = x_568;
goto block_80;
}
}
else
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec(x_498);
lean_dec(x_475);
lean_dec(x_463);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_569 = lean_ctor_get(x_496, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_570 = x_496;
} else {
 lean_dec_ref(x_496);
 x_570 = lean_box(0);
}
x_571 = lean_box(x_491);
if (lean_is_scalar(x_570)) {
 x_572 = lean_alloc_ctor(0, 2, 0);
} else {
 x_572 = x_570;
}
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_569);
return x_572;
}
}
else
{
lean_object* x_573; lean_object* x_574; 
lean_dec(x_475);
lean_dec(x_463);
lean_dec(x_2);
lean_dec(x_1);
x_573 = lean_ctor_get(x_496, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_496, 1);
lean_inc(x_574);
lean_dec(x_496);
x_10 = x_573;
x_11 = x_574;
goto block_80;
}
}
else
{
lean_object* x_575; lean_object* x_576; 
lean_dec(x_463);
lean_dec(x_2);
lean_dec(x_1);
x_575 = lean_ctor_get(x_470, 0);
lean_inc(x_575);
x_576 = lean_ctor_get(x_470, 1);
lean_inc(x_576);
lean_dec(x_470);
x_10 = x_575;
x_11 = x_576;
goto block_80;
}
}
else
{
lean_object* x_577; lean_object* x_578; 
lean_dec(x_463);
lean_dec(x_2);
lean_dec(x_1);
x_577 = lean_ctor_get(x_467, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_467, 1);
lean_inc(x_578);
lean_dec(x_467);
x_10 = x_577;
x_11 = x_578;
goto block_80;
}
}
}
else
{
lean_object* x_579; lean_object* x_580; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_579 = lean_ctor_get(x_85, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_85, 1);
lean_inc(x_580);
lean_dec(x_85);
x_10 = x_579;
x_11 = x_580;
goto block_80;
}
block_80:
{
uint8_t x_12; 
x_12 = l_Lean_Exception_isInterrupt(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lean_Exception_isRuntime(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_MVarId_acyclic_go___closed__4;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_14, x_5, x_6, x_7, x_8, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l_Lean_MVarId_acyclic_go___closed__5;
x_20 = lean_unbox(x_17);
lean_dec(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_15);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = lean_apply_6(x_19, x_21, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_22);
if (x_27 == 0)
{
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 0);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_22);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = l_Lean_Exception_toMessageData(x_10);
x_32 = l_Lean_MVarId_acyclic_go___closed__7;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_31);
lean_ctor_set(x_15, 0, x_32);
x_33 = l_Lean_MVarId_acyclic_go___closed__9;
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_15);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_14, x_34, x_5, x_6, x_7, x_8, x_18);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_apply_6(x_19, x_36, x_5, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_38);
if (x_43 == 0)
{
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_15, 0);
x_48 = lean_ctor_get(x_15, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_15);
x_49 = l_Lean_MVarId_acyclic_go___closed__5;
x_50 = lean_unbox(x_47);
lean_dec(x_47);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_10);
x_51 = lean_box(0);
x_52 = lean_apply_6(x_49, x_51, x_5, x_6, x_7, x_8, x_48);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_55 = x_52;
} else {
 lean_dec_ref(x_52);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_52, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_59 = x_52;
} else {
 lean_dec_ref(x_52);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_61 = l_Lean_Exception_toMessageData(x_10);
x_62 = l_Lean_MVarId_acyclic_go___closed__7;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_MVarId_acyclic_go___closed__9;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_14, x_65, x_5, x_6, x_7, x_8, x_48);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_apply_6(x_49, x_67, x_5, x_6, x_7, x_8, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
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
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_76 = x_69;
} else {
 lean_dec_ref(x_69);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_10);
lean_ctor_set(x_78, 1, x_11);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_10);
lean_ctor_set(x_79, 1, x_11);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_acyclic_go___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_MVarId_acyclic_go___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_acyclic___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_MVarId_acyclic___lambda__1___closed__2;
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
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Lean_Expr_appFn_x21(x_1);
x_17 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
x_18 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_17);
x_19 = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(x_17, x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_17);
lean_inc(x_18);
x_23 = l___private_Lean_Meta_Tactic_Acyclic_0__Lean_MVarId_isTarget(x_18, x_17, x_5, x_6, x_7, x_8, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; uint8_t x_25; 
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
x_38 = l_Lean_MVarId_acyclic_go(x_3, x_36, x_18, x_17, x_5, x_6, x_7, x_8, x_37);
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
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_23);
if (x_43 == 0)
{
return x_23;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_23, 0);
x_45 = lean_ctor_get(x_23, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_23);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_dec(x_19);
x_48 = l_Lean_MVarId_acyclic_go(x_3, x_2, x_17, x_18, x_5, x_6, x_7, x_8, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
return x_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("type: ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic___lambda__2___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_MVarId_acyclic_go___closed__4;
x_15 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_14, x_3, x_4, x_5, x_6, x_13);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = l_Lean_MVarId_acyclic___lambda__1(x_12, x_1, x_2, x_19, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_12);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_15, 1);
x_23 = lean_ctor_get(x_15, 0);
lean_dec(x_23);
lean_inc(x_12);
x_24 = l_Lean_MessageData_ofExpr(x_12);
x_25 = l_Lean_MVarId_acyclic___lambda__2___closed__2;
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_24);
lean_ctor_set(x_15, 0, x_25);
x_26 = l_Lean_MVarId_acyclic_go___closed__9;
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_15);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_14, x_27, x_3, x_4, x_5, x_6, x_22);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = l_Lean_MVarId_acyclic___lambda__1(x_12, x_1, x_2, x_29, x_3, x_4, x_5, x_6, x_30);
lean_dec(x_29);
lean_dec(x_12);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
lean_inc(x_12);
x_33 = l_Lean_MessageData_ofExpr(x_12);
x_34 = l_Lean_MVarId_acyclic___lambda__2___closed__2;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_MVarId_acyclic_go___closed__9;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_14, x_37, x_3, x_4, x_5, x_6, x_32);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_MVarId_acyclic___lambda__1(x_12, x_1, x_2, x_39, x_3, x_4, x_5, x_6, x_40);
lean_dec(x_39);
lean_dec(x_12);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
return x_11;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_11, 0);
x_44 = lean_ctor_get(x_11, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_11);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_8);
if (x_46 == 0)
{
return x_8;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_8, 0);
x_48 = lean_ctor_get(x_8, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_8);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic___lambda__2), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_acyclic___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("MVarId", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__2;
x_2 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initFn", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__4;
x_2 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__5;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_@", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__6;
x_2 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__7;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__8;
x_2 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__9;
x_2 = l_Lean_MVarId_acyclic_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__10;
x_2 = l_Lean_MVarId_acyclic_go___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Acyclic", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__11;
x_2 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__12;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_hyg", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__13;
x_2 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__14;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__15;
x_2 = lean_unsigned_to_nat(844u);
x_3 = l_Lean_Name_num___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_MVarId_acyclic_go___closed__4;
x_3 = 0;
x_4 = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__16;
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
l_Lean_MVarId_acyclic___lambda__1___closed__1 = _init_l_Lean_MVarId_acyclic___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_acyclic___lambda__1___closed__1);
l_Lean_MVarId_acyclic___lambda__1___closed__2 = _init_l_Lean_MVarId_acyclic___lambda__1___closed__2();
lean_mark_persistent(l_Lean_MVarId_acyclic___lambda__1___closed__2);
l_Lean_MVarId_acyclic___lambda__2___closed__1 = _init_l_Lean_MVarId_acyclic___lambda__2___closed__1();
lean_mark_persistent(l_Lean_MVarId_acyclic___lambda__2___closed__1);
l_Lean_MVarId_acyclic___lambda__2___closed__2 = _init_l_Lean_MVarId_acyclic___lambda__2___closed__2();
lean_mark_persistent(l_Lean_MVarId_acyclic___lambda__2___closed__2);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__1 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__1();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__1);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__2 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__2();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__2);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__3 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__3();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__3);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__4 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__4();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__4);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__5 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__5();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__5);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__6 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__6();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__6);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__7 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__7();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__7);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__8 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__8();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__8);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__9 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__9();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__9);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__10 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__10();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__10);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__11 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__11();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__11);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__12 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__12();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__12);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__13 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__13();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__13);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__14 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__14();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__14);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__15 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__15();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__15);
l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__16 = _init_l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__16();
lean_mark_persistent(l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__16);
if (builtin) {res = l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
