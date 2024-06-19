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
static lean_object* l_Lean_MVarId_acyclic_go___closed__38;
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
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__32;
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__12;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__34;
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
lean_object* l_Lean_Meta_instBEqOrigin___boxed(lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_occurs(lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__21;
lean_object* l_Lean_Meta_instHashableOrigin___boxed(lean_object*);
extern lean_object* l_Lean_Meta_Simp_defaultMaxSteps;
static lean_object* l_Lean_MVarId_initFn____x40_Lean_Meta_Tactic_Acyclic___hyg_844____closed__4;
static lean_object* l_Lean_MVarId_acyclic___lambda__2___closed__2;
static lean_object* l_Lean_MVarId_acyclic_go___closed__15;
lean_object* l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint32_t l_Lean_MVarId_acyclic_go___closed__16;
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__24;
static lean_object* l_Lean_MVarId_acyclic_go___closed__39;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_acyclic_go___closed__7;
static lean_object* l_Lean_MVarId_acyclic_go___closed__6;
static lean_object* l_Lean_MVarId_acyclic_go___closed__37;
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
lean_inc(x_2);
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
x_1 = lean_mk_string_from_bytes("Meta", 4);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Tactic", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("acyclic", 7);
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
x_1 = lean_mk_string_from_bytes("failed with\n", 12);
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
x_1 = lean_mk_string_from_bytes("", 0);
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
x_1 = lean_mk_string_from_bytes("SizeOf", 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("sizeOf", 6);
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
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_simpExtension;
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_Simp_defaultMaxSteps;
x_2 = lean_unsigned_to_nat(2u);
x_3 = 0;
x_4 = 1;
x_5 = 0;
x_6 = lean_alloc_ctor(0, 2, 18);
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
return x_6;
}
}
static uint32_t _init_l_Lean_MVarId_acyclic_go___closed__16() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_UInt32_ofNatTruncate(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__19;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__21() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lean_MVarId_acyclic_go___closed__17;
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
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableOrigin___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__19;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__26;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__28() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_MVarId_acyclic_go___closed__27;
x_3 = l_Lean_MVarId_acyclic_go___closed__26;
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
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_MVarId_acyclic_go___closed__25;
x_2 = l_Lean_MVarId_acyclic_go___closed__20;
x_3 = l_Lean_MVarId_acyclic_go___closed__28;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__25;
x_2 = l_Lean_MVarId_acyclic_go___closed__29;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("Nat", 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__32() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt_of_lt_of_eq", 14);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__31;
x_2 = l_Lean_MVarId_acyclic_go___closed__32;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__35() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("lt_irrefl", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_MVarId_acyclic_go___closed__31;
x_2 = l_Lean_MVarId_acyclic_go___closed__35;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__37() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_MVarId_acyclic_go___lambda__2___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__38() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("succeeded", 9);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_acyclic_go___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_acyclic_go___closed__38;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_acyclic_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = l_Lean_MVarId_acyclic_go___closed__13;
x_82 = lean_array_push(x_81, x_3);
x_83 = l_Lean_MVarId_acyclic_go___closed__12;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_84 = l_Lean_Meta_mkAppM(x_83, x_82, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_array_push(x_81, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_88 = l_Lean_Meta_mkAppM(x_83, x_87, x_5, x_6, x_7, x_8, x_86);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_85);
x_91 = l_Lean_Meta_mkLT(x_85, x_89, x_5, x_6, x_7, x_8, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint32_t x_105; lean_object* x_106; uint32_t x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_box(0);
lean_inc(x_5);
x_95 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_92, x_94, x_5, x_6, x_7, x_8, x_93);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_MVarId_acyclic_go___closed__14;
x_99 = l_Lean_Meta_SimpExtension_getTheorems(x_98, x_7, x_8, x_97);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Expr_mvarId_x21(x_96);
x_103 = lean_array_push(x_81, x_100);
x_104 = lean_box(0);
x_105 = 0;
x_106 = l_Lean_MVarId_acyclic_go___closed__15;
x_107 = l_Lean_MVarId_acyclic_go___closed__16;
x_108 = l_Lean_MVarId_acyclic_go___closed__21;
x_109 = lean_unsigned_to_nat(0u);
x_110 = 0;
x_111 = lean_alloc_ctor(0, 5, 9);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_103);
lean_ctor_set(x_111, 2, x_108);
lean_ctor_set(x_111, 3, x_104);
lean_ctor_set(x_111, 4, x_109);
lean_ctor_set_uint32(x_111, sizeof(void*)*5, x_107);
lean_ctor_set_uint32(x_111, sizeof(void*)*5 + 4, x_105);
lean_ctor_set_uint8(x_111, sizeof(void*)*5 + 8, x_110);
x_112 = l_Lean_MVarId_acyclic_go___closed__22;
x_113 = 1;
x_114 = l_Lean_MVarId_acyclic_go___closed__30;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_115 = l_Lean_Meta_simpTarget(x_102, x_111, x_112, x_104, x_113, x_114, x_5, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_119 = l_Lean_Meta_mkEqSymm(x_2, x_5, x_6, x_7, x_8, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lean_Expr_appFn_x21(x_85);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_123 = l_Lean_Meta_mkCongrArg(x_122, x_120, x_5, x_6, x_7, x_8, x_121);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_MVarId_acyclic_go___closed__34;
x_127 = lean_array_push(x_126, x_96);
x_128 = lean_array_push(x_127, x_124);
x_129 = l_Lean_MVarId_acyclic_go___closed__33;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_130 = l_Lean_Meta_mkAppM(x_129, x_128, x_5, x_6, x_7, x_8, x_125);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_array_push(x_81, x_85);
x_134 = l_Lean_MVarId_acyclic_go___closed__36;
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_135 = l_Lean_Meta_mkAppM(x_134, x_133, x_5, x_6, x_7, x_8, x_132);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_1);
x_138 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = l_Lean_Expr_app___override(x_136, x_131);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_142 = l_Lean_Meta_mkFalseElim(x_139, x_141, x_5, x_6, x_7, x_8, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_143, x_5, x_6, x_7, x_8, x_144);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_147 = l_Lean_MVarId_acyclic_go___closed__4;
x_148 = l_Lean_isTracingEnabledFor___at_Lean_Meta_processPostponed_loop___spec__1(x_147, x_5, x_6, x_7, x_8, x_146);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
x_151 = l_Lean_MVarId_acyclic_go___closed__37;
x_152 = lean_unbox(x_149);
lean_dec(x_149);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_box(0);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_154 = lean_apply_6(x_151, x_153, x_5, x_6, x_7, x_8, x_150);
if (lean_obj_tag(x_154) == 0)
{
uint8_t x_155; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_155 = !lean_is_exclusive(x_154);
if (x_155 == 0)
{
return x_154;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_154, 0);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_154);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_154, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_154, 1);
lean_inc(x_160);
lean_dec(x_154);
x_10 = x_159;
x_11 = x_160;
goto block_80;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_161 = l_Lean_MVarId_acyclic_go___closed__39;
x_162 = l_Lean_addTrace___at_Lean_Meta_processPostponed_loop___spec__2(x_147, x_161, x_5, x_6, x_7, x_8, x_150);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_165 = lean_apply_6(x_151, x_163, x_5, x_6, x_7, x_8, x_164);
if (lean_obj_tag(x_165) == 0)
{
uint8_t x_166; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
return x_165;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_165);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_165, 1);
lean_inc(x_171);
lean_dec(x_165);
x_10 = x_170;
x_11 = x_171;
goto block_80;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_1);
x_172 = lean_ctor_get(x_142, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_142, 1);
lean_inc(x_173);
lean_dec(x_142);
x_10 = x_172;
x_11 = x_173;
goto block_80;
}
}
else
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_136);
lean_dec(x_131);
lean_dec(x_1);
x_174 = lean_ctor_get(x_138, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_138, 1);
lean_inc(x_175);
lean_dec(x_138);
x_10 = x_174;
x_11 = x_175;
goto block_80;
}
}
else
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_131);
lean_dec(x_1);
x_176 = lean_ctor_get(x_135, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_135, 1);
lean_inc(x_177);
lean_dec(x_135);
x_10 = x_176;
x_11 = x_177;
goto block_80;
}
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_85);
lean_dec(x_1);
x_178 = lean_ctor_get(x_130, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_130, 1);
lean_inc(x_179);
lean_dec(x_130);
x_10 = x_178;
x_11 = x_179;
goto block_80;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_96);
lean_dec(x_85);
lean_dec(x_1);
x_180 = lean_ctor_get(x_123, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_123, 1);
lean_inc(x_181);
lean_dec(x_123);
x_10 = x_180;
x_11 = x_181;
goto block_80;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_96);
lean_dec(x_85);
lean_dec(x_1);
x_182 = lean_ctor_get(x_119, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_119, 1);
lean_inc(x_183);
lean_dec(x_119);
x_10 = x_182;
x_11 = x_183;
goto block_80;
}
}
else
{
uint8_t x_184; 
lean_dec(x_117);
lean_dec(x_96);
lean_dec(x_85);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_184 = !lean_is_exclusive(x_115);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_115, 0);
lean_dec(x_185);
x_186 = lean_box(x_110);
lean_ctor_set(x_115, 0, x_186);
return x_115;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_115, 1);
lean_inc(x_187);
lean_dec(x_115);
x_188 = lean_box(x_110);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_96);
lean_dec(x_85);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_ctor_get(x_115, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_115, 1);
lean_inc(x_191);
lean_dec(x_115);
x_10 = x_190;
x_11 = x_191;
goto block_80;
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_85);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_ctor_get(x_91, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_91, 1);
lean_inc(x_193);
lean_dec(x_91);
x_10 = x_192;
x_11 = x_193;
goto block_80;
}
}
else
{
lean_object* x_194; lean_object* x_195; 
lean_dec(x_85);
lean_dec(x_2);
lean_dec(x_1);
x_194 = lean_ctor_get(x_88, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_88, 1);
lean_inc(x_195);
lean_dec(x_88);
x_10 = x_194;
x_11 = x_195;
goto block_80;
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_196 = lean_ctor_get(x_84, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_84, 1);
lean_inc(x_197);
lean_dec(x_84);
x_10 = x_196;
x_11 = x_197;
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
x_1 = lean_mk_string_from_bytes("Eq", 2);
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
x_1 = lean_mk_string_from_bytes("type: ", 6);
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
x_1 = lean_mk_string_from_bytes("Lean", 4);
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
x_1 = lean_mk_string_from_bytes("MVarId", 6);
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
x_1 = lean_mk_string_from_bytes("initFn", 6);
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
x_1 = lean_mk_string_from_bytes("_@", 2);
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
x_1 = lean_mk_string_from_bytes("Acyclic", 7);
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
x_1 = lean_mk_string_from_bytes("_hyg", 4);
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
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__15);
l_Lean_MVarId_acyclic_go___closed__16 = _init_l_Lean_MVarId_acyclic_go___closed__16();
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
l_Lean_MVarId_acyclic_go___closed__38 = _init_l_Lean_MVarId_acyclic_go___closed__38();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__38);
l_Lean_MVarId_acyclic_go___closed__39 = _init_l_Lean_MVarId_acyclic_go___closed__39();
lean_mark_persistent(l_Lean_MVarId_acyclic_go___closed__39);
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
