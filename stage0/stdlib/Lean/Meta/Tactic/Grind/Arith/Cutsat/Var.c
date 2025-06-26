// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
// Imports: Lean.Meta.IntInstTesters Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
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
lean_object* l_Lean_Meta_isInstHAddInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__0;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8;
lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isZero(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__10;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0;
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__12;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2;
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsCutsatTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3;
lean_object* l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("internalize", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ↦ #", 6, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_mk_var(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_15, x_1);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
lean_free_object(x_11);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_14);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_22 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_21, x_8, x_20);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = !lean_is_exclusive(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_285; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_285 = lean_unbox(x_25);
lean_dec(x_25);
if (x_285 == 0)
{
lean_free_object(x_22);
lean_free_object(x_17);
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_26;
goto block_284;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_286 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_287 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_287);
lean_ctor_set(x_22, 0, x_286);
x_288 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_288);
lean_ctor_set(x_17, 0, x_22);
lean_inc(x_27);
x_289 = l_Nat_reprFast(x_27);
x_290 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_290, 0, x_289);
x_291 = l_Lean_MessageData_ofFormat(x_290);
x_292 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_292, 0, x_17);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_286);
x_294 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_293, x_6, x_7, x_8, x_9, x_26);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
lean_dec(x_294);
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_295;
goto block_284;
}
block_284:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_st_ref_take(x_28, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 14);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_38, 14);
lean_dec(x_43);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_39, 1);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
x_49 = lean_ctor_get(x_40, 5);
x_50 = lean_ctor_get(x_40, 6);
x_51 = lean_ctor_get(x_40, 7);
x_52 = lean_ctor_get(x_40, 8);
x_53 = lean_ctor_get(x_40, 9);
x_54 = lean_ctor_get(x_40, 11);
lean_inc(x_1);
x_55 = l_Lean_PersistentArray_push___redArg(x_47, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_56 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_48, x_1, x_27);
x_57 = lean_box(0);
x_58 = l_Lean_PersistentArray_push___redArg(x_49, x_57);
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_60 = l_Lean_PersistentArray_push___redArg(x_50, x_59);
x_61 = l_Lean_PersistentArray_push___redArg(x_51, x_59);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_63 = l_Lean_PersistentArray_push___redArg(x_52, x_62);
x_64 = lean_box(0);
x_65 = l_Lean_PersistentArray_push___redArg(x_53, x_64);
x_66 = lean_box(0);
x_67 = l_Lean_PersistentArray_push___redArg(x_54, x_66);
lean_ctor_set(x_40, 11, x_67);
lean_ctor_set(x_40, 9, x_65);
lean_ctor_set(x_40, 8, x_63);
lean_ctor_set(x_40, 7, x_61);
lean_ctor_set(x_40, 6, x_60);
lean_ctor_set(x_40, 5, x_58);
lean_ctor_set(x_40, 1, x_56);
lean_ctor_set(x_40, 0, x_55);
x_68 = lean_st_ref_set(x_28, x_38, x_41);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_70 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_1);
x_72 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
x_74 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_27);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_27);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_27);
x_79 = !lean_is_exclusive(x_74);
if (x_79 == 0)
{
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_74, 0);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_74);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_72);
if (x_83 == 0)
{
return x_72;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_72, 0);
x_85 = lean_ctor_get(x_72, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_72);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_70);
if (x_87 == 0)
{
return x_70;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_70, 0);
x_89 = lean_ctor_get(x_70, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_70);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_91 = lean_ctor_get(x_40, 0);
x_92 = lean_ctor_get(x_40, 1);
x_93 = lean_ctor_get(x_40, 2);
x_94 = lean_ctor_get(x_40, 3);
x_95 = lean_ctor_get(x_40, 4);
x_96 = lean_ctor_get(x_40, 5);
x_97 = lean_ctor_get(x_40, 6);
x_98 = lean_ctor_get(x_40, 7);
x_99 = lean_ctor_get(x_40, 8);
x_100 = lean_ctor_get(x_40, 9);
x_101 = lean_ctor_get(x_40, 10);
x_102 = lean_ctor_get(x_40, 11);
x_103 = lean_ctor_get(x_40, 12);
x_104 = lean_ctor_get(x_40, 13);
x_105 = lean_ctor_get_uint8(x_40, sizeof(void*)*18);
x_106 = lean_ctor_get(x_40, 14);
x_107 = lean_ctor_get(x_40, 15);
x_108 = lean_ctor_get(x_40, 16);
x_109 = lean_ctor_get(x_40, 17);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_40);
lean_inc(x_1);
x_110 = l_Lean_PersistentArray_push___redArg(x_91, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_111 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_92, x_1, x_27);
x_112 = lean_box(0);
x_113 = l_Lean_PersistentArray_push___redArg(x_96, x_112);
x_114 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_115 = l_Lean_PersistentArray_push___redArg(x_97, x_114);
x_116 = l_Lean_PersistentArray_push___redArg(x_98, x_114);
x_117 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_118 = l_Lean_PersistentArray_push___redArg(x_99, x_117);
x_119 = lean_box(0);
x_120 = l_Lean_PersistentArray_push___redArg(x_100, x_119);
x_121 = lean_box(0);
x_122 = l_Lean_PersistentArray_push___redArg(x_102, x_121);
x_123 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_123, 0, x_110);
lean_ctor_set(x_123, 1, x_111);
lean_ctor_set(x_123, 2, x_93);
lean_ctor_set(x_123, 3, x_94);
lean_ctor_set(x_123, 4, x_95);
lean_ctor_set(x_123, 5, x_113);
lean_ctor_set(x_123, 6, x_115);
lean_ctor_set(x_123, 7, x_116);
lean_ctor_set(x_123, 8, x_118);
lean_ctor_set(x_123, 9, x_120);
lean_ctor_set(x_123, 10, x_101);
lean_ctor_set(x_123, 11, x_122);
lean_ctor_set(x_123, 12, x_103);
lean_ctor_set(x_123, 13, x_104);
lean_ctor_set(x_123, 14, x_106);
lean_ctor_set(x_123, 15, x_107);
lean_ctor_set(x_123, 16, x_108);
lean_ctor_set(x_123, 17, x_109);
lean_ctor_set_uint8(x_123, sizeof(void*)*18, x_105);
lean_ctor_set(x_39, 1, x_123);
x_124 = lean_st_ref_set(x_28, x_38, x_41);
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_126 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 1);
lean_inc(x_127);
lean_dec(x_126);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_1);
x_128 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_132 = x_130;
} else {
 lean_dec_ref(x_130);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_27);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_27);
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_136 = x_130;
} else {
 lean_dec_ref(x_130);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_138 = lean_ctor_get(x_128, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_128, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_140 = x_128;
} else {
 lean_dec_ref(x_128);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(1, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_142 = lean_ctor_get(x_126, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_126, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_144 = x_126;
} else {
 lean_dec_ref(x_126);
 x_144 = lean_box(0);
}
if (lean_is_scalar(x_144)) {
 x_145 = lean_alloc_ctor(1, 2, 0);
} else {
 x_145 = x_144;
}
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_143);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_146 = lean_ctor_get(x_39, 0);
x_147 = lean_ctor_get(x_39, 2);
x_148 = lean_ctor_get(x_39, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_39);
x_149 = lean_ctor_get(x_40, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_40, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_40, 2);
lean_inc(x_151);
x_152 = lean_ctor_get(x_40, 3);
lean_inc(x_152);
x_153 = lean_ctor_get(x_40, 4);
lean_inc(x_153);
x_154 = lean_ctor_get(x_40, 5);
lean_inc(x_154);
x_155 = lean_ctor_get(x_40, 6);
lean_inc(x_155);
x_156 = lean_ctor_get(x_40, 7);
lean_inc(x_156);
x_157 = lean_ctor_get(x_40, 8);
lean_inc(x_157);
x_158 = lean_ctor_get(x_40, 9);
lean_inc(x_158);
x_159 = lean_ctor_get(x_40, 10);
lean_inc(x_159);
x_160 = lean_ctor_get(x_40, 11);
lean_inc(x_160);
x_161 = lean_ctor_get(x_40, 12);
lean_inc(x_161);
x_162 = lean_ctor_get(x_40, 13);
lean_inc(x_162);
x_163 = lean_ctor_get_uint8(x_40, sizeof(void*)*18);
x_164 = lean_ctor_get(x_40, 14);
lean_inc(x_164);
x_165 = lean_ctor_get(x_40, 15);
lean_inc(x_165);
x_166 = lean_ctor_get(x_40, 16);
lean_inc(x_166);
x_167 = lean_ctor_get(x_40, 17);
lean_inc(x_167);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 lean_ctor_release(x_40, 7);
 lean_ctor_release(x_40, 8);
 lean_ctor_release(x_40, 9);
 lean_ctor_release(x_40, 10);
 lean_ctor_release(x_40, 11);
 lean_ctor_release(x_40, 12);
 lean_ctor_release(x_40, 13);
 lean_ctor_release(x_40, 14);
 lean_ctor_release(x_40, 15);
 lean_ctor_release(x_40, 16);
 lean_ctor_release(x_40, 17);
 x_168 = x_40;
} else {
 lean_dec_ref(x_40);
 x_168 = lean_box(0);
}
lean_inc(x_1);
x_169 = l_Lean_PersistentArray_push___redArg(x_149, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_170 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_150, x_1, x_27);
x_171 = lean_box(0);
x_172 = l_Lean_PersistentArray_push___redArg(x_154, x_171);
x_173 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_174 = l_Lean_PersistentArray_push___redArg(x_155, x_173);
x_175 = l_Lean_PersistentArray_push___redArg(x_156, x_173);
x_176 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_177 = l_Lean_PersistentArray_push___redArg(x_157, x_176);
x_178 = lean_box(0);
x_179 = l_Lean_PersistentArray_push___redArg(x_158, x_178);
x_180 = lean_box(0);
x_181 = l_Lean_PersistentArray_push___redArg(x_160, x_180);
if (lean_is_scalar(x_168)) {
 x_182 = lean_alloc_ctor(0, 18, 1);
} else {
 x_182 = x_168;
}
lean_ctor_set(x_182, 0, x_169);
lean_ctor_set(x_182, 1, x_170);
lean_ctor_set(x_182, 2, x_151);
lean_ctor_set(x_182, 3, x_152);
lean_ctor_set(x_182, 4, x_153);
lean_ctor_set(x_182, 5, x_172);
lean_ctor_set(x_182, 6, x_174);
lean_ctor_set(x_182, 7, x_175);
lean_ctor_set(x_182, 8, x_177);
lean_ctor_set(x_182, 9, x_179);
lean_ctor_set(x_182, 10, x_159);
lean_ctor_set(x_182, 11, x_181);
lean_ctor_set(x_182, 12, x_161);
lean_ctor_set(x_182, 13, x_162);
lean_ctor_set(x_182, 14, x_164);
lean_ctor_set(x_182, 15, x_165);
lean_ctor_set(x_182, 16, x_166);
lean_ctor_set(x_182, 17, x_167);
lean_ctor_set_uint8(x_182, sizeof(void*)*18, x_163);
x_183 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_183, 0, x_146);
lean_ctor_set(x_183, 1, x_182);
lean_ctor_set(x_183, 2, x_147);
lean_ctor_set(x_183, 3, x_148);
lean_ctor_set(x_38, 14, x_183);
x_184 = lean_st_ref_set(x_28, x_38, x_41);
x_185 = lean_ctor_get(x_184, 1);
lean_inc(x_185);
lean_dec(x_184);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_186 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_1);
x_188 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
x_190 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_192 = x_190;
} else {
 lean_dec_ref(x_190);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_27);
lean_ctor_set(x_193, 1, x_191);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec(x_27);
x_194 = lean_ctor_get(x_190, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_190, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_196 = x_190;
} else {
 lean_dec_ref(x_190);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(1, 2, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_195);
return x_197;
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_198 = lean_ctor_get(x_188, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_188, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_200 = x_188;
} else {
 lean_dec_ref(x_188);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 2, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_202 = lean_ctor_get(x_186, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_186, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_204 = x_186;
} else {
 lean_dec_ref(x_186);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_206 = lean_ctor_get(x_38, 0);
x_207 = lean_ctor_get(x_38, 1);
x_208 = lean_ctor_get(x_38, 2);
x_209 = lean_ctor_get(x_38, 3);
x_210 = lean_ctor_get(x_38, 4);
x_211 = lean_ctor_get(x_38, 5);
x_212 = lean_ctor_get(x_38, 6);
x_213 = lean_ctor_get(x_38, 7);
x_214 = lean_ctor_get_uint8(x_38, sizeof(void*)*16);
x_215 = lean_ctor_get(x_38, 8);
x_216 = lean_ctor_get(x_38, 9);
x_217 = lean_ctor_get(x_38, 10);
x_218 = lean_ctor_get(x_38, 11);
x_219 = lean_ctor_get(x_38, 12);
x_220 = lean_ctor_get(x_38, 13);
x_221 = lean_ctor_get(x_38, 15);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_38);
x_222 = lean_ctor_get(x_39, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_39, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_39, 3);
lean_inc(x_224);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 x_225 = x_39;
} else {
 lean_dec_ref(x_39);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_40, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_40, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_40, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_40, 3);
lean_inc(x_229);
x_230 = lean_ctor_get(x_40, 4);
lean_inc(x_230);
x_231 = lean_ctor_get(x_40, 5);
lean_inc(x_231);
x_232 = lean_ctor_get(x_40, 6);
lean_inc(x_232);
x_233 = lean_ctor_get(x_40, 7);
lean_inc(x_233);
x_234 = lean_ctor_get(x_40, 8);
lean_inc(x_234);
x_235 = lean_ctor_get(x_40, 9);
lean_inc(x_235);
x_236 = lean_ctor_get(x_40, 10);
lean_inc(x_236);
x_237 = lean_ctor_get(x_40, 11);
lean_inc(x_237);
x_238 = lean_ctor_get(x_40, 12);
lean_inc(x_238);
x_239 = lean_ctor_get(x_40, 13);
lean_inc(x_239);
x_240 = lean_ctor_get_uint8(x_40, sizeof(void*)*18);
x_241 = lean_ctor_get(x_40, 14);
lean_inc(x_241);
x_242 = lean_ctor_get(x_40, 15);
lean_inc(x_242);
x_243 = lean_ctor_get(x_40, 16);
lean_inc(x_243);
x_244 = lean_ctor_get(x_40, 17);
lean_inc(x_244);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 lean_ctor_release(x_40, 2);
 lean_ctor_release(x_40, 3);
 lean_ctor_release(x_40, 4);
 lean_ctor_release(x_40, 5);
 lean_ctor_release(x_40, 6);
 lean_ctor_release(x_40, 7);
 lean_ctor_release(x_40, 8);
 lean_ctor_release(x_40, 9);
 lean_ctor_release(x_40, 10);
 lean_ctor_release(x_40, 11);
 lean_ctor_release(x_40, 12);
 lean_ctor_release(x_40, 13);
 lean_ctor_release(x_40, 14);
 lean_ctor_release(x_40, 15);
 lean_ctor_release(x_40, 16);
 lean_ctor_release(x_40, 17);
 x_245 = x_40;
} else {
 lean_dec_ref(x_40);
 x_245 = lean_box(0);
}
lean_inc(x_1);
x_246 = l_Lean_PersistentArray_push___redArg(x_226, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_247 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_227, x_1, x_27);
x_248 = lean_box(0);
x_249 = l_Lean_PersistentArray_push___redArg(x_231, x_248);
x_250 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_251 = l_Lean_PersistentArray_push___redArg(x_232, x_250);
x_252 = l_Lean_PersistentArray_push___redArg(x_233, x_250);
x_253 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_254 = l_Lean_PersistentArray_push___redArg(x_234, x_253);
x_255 = lean_box(0);
x_256 = l_Lean_PersistentArray_push___redArg(x_235, x_255);
x_257 = lean_box(0);
x_258 = l_Lean_PersistentArray_push___redArg(x_237, x_257);
if (lean_is_scalar(x_245)) {
 x_259 = lean_alloc_ctor(0, 18, 1);
} else {
 x_259 = x_245;
}
lean_ctor_set(x_259, 0, x_246);
lean_ctor_set(x_259, 1, x_247);
lean_ctor_set(x_259, 2, x_228);
lean_ctor_set(x_259, 3, x_229);
lean_ctor_set(x_259, 4, x_230);
lean_ctor_set(x_259, 5, x_249);
lean_ctor_set(x_259, 6, x_251);
lean_ctor_set(x_259, 7, x_252);
lean_ctor_set(x_259, 8, x_254);
lean_ctor_set(x_259, 9, x_256);
lean_ctor_set(x_259, 10, x_236);
lean_ctor_set(x_259, 11, x_258);
lean_ctor_set(x_259, 12, x_238);
lean_ctor_set(x_259, 13, x_239);
lean_ctor_set(x_259, 14, x_241);
lean_ctor_set(x_259, 15, x_242);
lean_ctor_set(x_259, 16, x_243);
lean_ctor_set(x_259, 17, x_244);
lean_ctor_set_uint8(x_259, sizeof(void*)*18, x_240);
if (lean_is_scalar(x_225)) {
 x_260 = lean_alloc_ctor(0, 4, 0);
} else {
 x_260 = x_225;
}
lean_ctor_set(x_260, 0, x_222);
lean_ctor_set(x_260, 1, x_259);
lean_ctor_set(x_260, 2, x_223);
lean_ctor_set(x_260, 3, x_224);
x_261 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_261, 0, x_206);
lean_ctor_set(x_261, 1, x_207);
lean_ctor_set(x_261, 2, x_208);
lean_ctor_set(x_261, 3, x_209);
lean_ctor_set(x_261, 4, x_210);
lean_ctor_set(x_261, 5, x_211);
lean_ctor_set(x_261, 6, x_212);
lean_ctor_set(x_261, 7, x_213);
lean_ctor_set(x_261, 8, x_215);
lean_ctor_set(x_261, 9, x_216);
lean_ctor_set(x_261, 10, x_217);
lean_ctor_set(x_261, 11, x_218);
lean_ctor_set(x_261, 12, x_219);
lean_ctor_set(x_261, 13, x_220);
lean_ctor_set(x_261, 14, x_260);
lean_ctor_set(x_261, 15, x_221);
lean_ctor_set_uint8(x_261, sizeof(void*)*16, x_214);
x_262 = lean_st_ref_set(x_28, x_261, x_41);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_264 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
lean_dec(x_264);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_1);
x_266 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; 
x_267 = lean_ctor_get(x_266, 1);
lean_inc(x_267);
lean_dec(x_266);
x_268 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_267);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_268, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_270 = x_268;
} else {
 lean_dec_ref(x_268);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_27);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_27);
x_272 = lean_ctor_get(x_268, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_268, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_268)) {
 lean_ctor_release(x_268, 0);
 lean_ctor_release(x_268, 1);
 x_274 = x_268;
} else {
 lean_dec_ref(x_268);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_276 = lean_ctor_get(x_266, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_266, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_278 = x_266;
} else {
 lean_dec_ref(x_266);
 x_278 = lean_box(0);
}
if (lean_is_scalar(x_278)) {
 x_279 = lean_alloc_ctor(1, 2, 0);
} else {
 x_279 = x_278;
}
lean_ctor_set(x_279, 0, x_276);
lean_ctor_set(x_279, 1, x_277);
return x_279;
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_1);
x_280 = lean_ctor_get(x_264, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_264, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_282 = x_264;
} else {
 lean_dec_ref(x_264);
 x_282 = lean_box(0);
}
if (lean_is_scalar(x_282)) {
 x_283 = lean_alloc_ctor(1, 2, 0);
} else {
 x_283 = x_282;
}
lean_ctor_set(x_283, 0, x_280);
lean_ctor_set(x_283, 1, x_281);
return x_283;
}
}
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_393; 
x_296 = lean_ctor_get(x_22, 0);
x_297 = lean_ctor_get(x_22, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_22);
x_298 = lean_ctor_get(x_23, 2);
lean_inc(x_298);
lean_dec(x_23);
x_393 = lean_unbox(x_296);
lean_dec(x_296);
if (x_393 == 0)
{
lean_free_object(x_17);
x_299 = x_2;
x_300 = x_3;
x_301 = x_4;
x_302 = x_5;
x_303 = x_6;
x_304 = x_7;
x_305 = x_8;
x_306 = x_9;
x_307 = x_297;
goto block_392;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_394 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_395 = l_Lean_MessageData_ofExpr(x_1);
x_396 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_397);
lean_ctor_set(x_17, 0, x_396);
lean_inc(x_298);
x_398 = l_Nat_reprFast(x_298);
x_399 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_399, 0, x_398);
x_400 = l_Lean_MessageData_ofFormat(x_399);
x_401 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_401, 0, x_17);
lean_ctor_set(x_401, 1, x_400);
x_402 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_394);
x_403 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_402, x_6, x_7, x_8, x_9, x_297);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_299 = x_2;
x_300 = x_3;
x_301 = x_4;
x_302 = x_5;
x_303 = x_6;
x_304 = x_7;
x_305 = x_8;
x_306 = x_9;
x_307 = x_404;
goto block_392;
}
block_392:
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_308 = lean_st_ref_take(x_299, x_307);
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_309, 14);
lean_inc(x_310);
x_311 = lean_ctor_get(x_310, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_308, 1);
lean_inc(x_312);
lean_dec(x_308);
x_313 = lean_ctor_get(x_309, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_309, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_309, 2);
lean_inc(x_315);
x_316 = lean_ctor_get(x_309, 3);
lean_inc(x_316);
x_317 = lean_ctor_get(x_309, 4);
lean_inc(x_317);
x_318 = lean_ctor_get(x_309, 5);
lean_inc(x_318);
x_319 = lean_ctor_get(x_309, 6);
lean_inc(x_319);
x_320 = lean_ctor_get(x_309, 7);
lean_inc(x_320);
x_321 = lean_ctor_get_uint8(x_309, sizeof(void*)*16);
x_322 = lean_ctor_get(x_309, 8);
lean_inc(x_322);
x_323 = lean_ctor_get(x_309, 9);
lean_inc(x_323);
x_324 = lean_ctor_get(x_309, 10);
lean_inc(x_324);
x_325 = lean_ctor_get(x_309, 11);
lean_inc(x_325);
x_326 = lean_ctor_get(x_309, 12);
lean_inc(x_326);
x_327 = lean_ctor_get(x_309, 13);
lean_inc(x_327);
x_328 = lean_ctor_get(x_309, 15);
lean_inc(x_328);
if (lean_is_exclusive(x_309)) {
 lean_ctor_release(x_309, 0);
 lean_ctor_release(x_309, 1);
 lean_ctor_release(x_309, 2);
 lean_ctor_release(x_309, 3);
 lean_ctor_release(x_309, 4);
 lean_ctor_release(x_309, 5);
 lean_ctor_release(x_309, 6);
 lean_ctor_release(x_309, 7);
 lean_ctor_release(x_309, 8);
 lean_ctor_release(x_309, 9);
 lean_ctor_release(x_309, 10);
 lean_ctor_release(x_309, 11);
 lean_ctor_release(x_309, 12);
 lean_ctor_release(x_309, 13);
 lean_ctor_release(x_309, 14);
 lean_ctor_release(x_309, 15);
 x_329 = x_309;
} else {
 lean_dec_ref(x_309);
 x_329 = lean_box(0);
}
x_330 = lean_ctor_get(x_310, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_310, 2);
lean_inc(x_331);
x_332 = lean_ctor_get(x_310, 3);
lean_inc(x_332);
if (lean_is_exclusive(x_310)) {
 lean_ctor_release(x_310, 0);
 lean_ctor_release(x_310, 1);
 lean_ctor_release(x_310, 2);
 lean_ctor_release(x_310, 3);
 x_333 = x_310;
} else {
 lean_dec_ref(x_310);
 x_333 = lean_box(0);
}
x_334 = lean_ctor_get(x_311, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_311, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_311, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_311, 3);
lean_inc(x_337);
x_338 = lean_ctor_get(x_311, 4);
lean_inc(x_338);
x_339 = lean_ctor_get(x_311, 5);
lean_inc(x_339);
x_340 = lean_ctor_get(x_311, 6);
lean_inc(x_340);
x_341 = lean_ctor_get(x_311, 7);
lean_inc(x_341);
x_342 = lean_ctor_get(x_311, 8);
lean_inc(x_342);
x_343 = lean_ctor_get(x_311, 9);
lean_inc(x_343);
x_344 = lean_ctor_get(x_311, 10);
lean_inc(x_344);
x_345 = lean_ctor_get(x_311, 11);
lean_inc(x_345);
x_346 = lean_ctor_get(x_311, 12);
lean_inc(x_346);
x_347 = lean_ctor_get(x_311, 13);
lean_inc(x_347);
x_348 = lean_ctor_get_uint8(x_311, sizeof(void*)*18);
x_349 = lean_ctor_get(x_311, 14);
lean_inc(x_349);
x_350 = lean_ctor_get(x_311, 15);
lean_inc(x_350);
x_351 = lean_ctor_get(x_311, 16);
lean_inc(x_351);
x_352 = lean_ctor_get(x_311, 17);
lean_inc(x_352);
if (lean_is_exclusive(x_311)) {
 lean_ctor_release(x_311, 0);
 lean_ctor_release(x_311, 1);
 lean_ctor_release(x_311, 2);
 lean_ctor_release(x_311, 3);
 lean_ctor_release(x_311, 4);
 lean_ctor_release(x_311, 5);
 lean_ctor_release(x_311, 6);
 lean_ctor_release(x_311, 7);
 lean_ctor_release(x_311, 8);
 lean_ctor_release(x_311, 9);
 lean_ctor_release(x_311, 10);
 lean_ctor_release(x_311, 11);
 lean_ctor_release(x_311, 12);
 lean_ctor_release(x_311, 13);
 lean_ctor_release(x_311, 14);
 lean_ctor_release(x_311, 15);
 lean_ctor_release(x_311, 16);
 lean_ctor_release(x_311, 17);
 x_353 = x_311;
} else {
 lean_dec_ref(x_311);
 x_353 = lean_box(0);
}
lean_inc(x_1);
x_354 = l_Lean_PersistentArray_push___redArg(x_334, x_1);
lean_inc(x_298);
lean_inc(x_1);
x_355 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_335, x_1, x_298);
x_356 = lean_box(0);
x_357 = l_Lean_PersistentArray_push___redArg(x_339, x_356);
x_358 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_359 = l_Lean_PersistentArray_push___redArg(x_340, x_358);
x_360 = l_Lean_PersistentArray_push___redArg(x_341, x_358);
x_361 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_362 = l_Lean_PersistentArray_push___redArg(x_342, x_361);
x_363 = lean_box(0);
x_364 = l_Lean_PersistentArray_push___redArg(x_343, x_363);
x_365 = lean_box(0);
x_366 = l_Lean_PersistentArray_push___redArg(x_345, x_365);
if (lean_is_scalar(x_353)) {
 x_367 = lean_alloc_ctor(0, 18, 1);
} else {
 x_367 = x_353;
}
lean_ctor_set(x_367, 0, x_354);
lean_ctor_set(x_367, 1, x_355);
lean_ctor_set(x_367, 2, x_336);
lean_ctor_set(x_367, 3, x_337);
lean_ctor_set(x_367, 4, x_338);
lean_ctor_set(x_367, 5, x_357);
lean_ctor_set(x_367, 6, x_359);
lean_ctor_set(x_367, 7, x_360);
lean_ctor_set(x_367, 8, x_362);
lean_ctor_set(x_367, 9, x_364);
lean_ctor_set(x_367, 10, x_344);
lean_ctor_set(x_367, 11, x_366);
lean_ctor_set(x_367, 12, x_346);
lean_ctor_set(x_367, 13, x_347);
lean_ctor_set(x_367, 14, x_349);
lean_ctor_set(x_367, 15, x_350);
lean_ctor_set(x_367, 16, x_351);
lean_ctor_set(x_367, 17, x_352);
lean_ctor_set_uint8(x_367, sizeof(void*)*18, x_348);
if (lean_is_scalar(x_333)) {
 x_368 = lean_alloc_ctor(0, 4, 0);
} else {
 x_368 = x_333;
}
lean_ctor_set(x_368, 0, x_330);
lean_ctor_set(x_368, 1, x_367);
lean_ctor_set(x_368, 2, x_331);
lean_ctor_set(x_368, 3, x_332);
if (lean_is_scalar(x_329)) {
 x_369 = lean_alloc_ctor(0, 16, 1);
} else {
 x_369 = x_329;
}
lean_ctor_set(x_369, 0, x_313);
lean_ctor_set(x_369, 1, x_314);
lean_ctor_set(x_369, 2, x_315);
lean_ctor_set(x_369, 3, x_316);
lean_ctor_set(x_369, 4, x_317);
lean_ctor_set(x_369, 5, x_318);
lean_ctor_set(x_369, 6, x_319);
lean_ctor_set(x_369, 7, x_320);
lean_ctor_set(x_369, 8, x_322);
lean_ctor_set(x_369, 9, x_323);
lean_ctor_set(x_369, 10, x_324);
lean_ctor_set(x_369, 11, x_325);
lean_ctor_set(x_369, 12, x_326);
lean_ctor_set(x_369, 13, x_327);
lean_ctor_set(x_369, 14, x_368);
lean_ctor_set(x_369, 15, x_328);
lean_ctor_set_uint8(x_369, sizeof(void*)*16, x_321);
x_370 = lean_st_ref_set(x_299, x_369, x_312);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec(x_370);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_1);
x_372 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_299, x_300, x_301, x_302, x_303, x_304, x_305, x_306, x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
lean_dec(x_372);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_1);
x_374 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_298, x_299, x_300, x_301, x_302, x_303, x_304, x_305, x_306, x_373);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; 
x_375 = lean_ctor_get(x_374, 1);
lean_inc(x_375);
lean_dec(x_374);
x_376 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_299, x_300, x_301, x_302, x_303, x_304, x_305, x_306, x_375);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_378 = x_376;
} else {
 lean_dec_ref(x_376);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(0, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_298);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_298);
x_380 = lean_ctor_get(x_376, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_376, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_382 = x_376;
} else {
 lean_dec_ref(x_376);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_1);
x_384 = lean_ctor_get(x_374, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_374, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_374)) {
 lean_ctor_release(x_374, 0);
 lean_ctor_release(x_374, 1);
 x_386 = x_374;
} else {
 lean_dec_ref(x_374);
 x_386 = lean_box(0);
}
if (lean_is_scalar(x_386)) {
 x_387 = lean_alloc_ctor(1, 2, 0);
} else {
 x_387 = x_386;
}
lean_ctor_set(x_387, 0, x_384);
lean_ctor_set(x_387, 1, x_385);
return x_387;
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_1);
x_388 = lean_ctor_get(x_372, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_372, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_390 = x_372;
} else {
 lean_dec_ref(x_372);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; uint8_t x_508; 
x_405 = lean_ctor_get(x_17, 0);
x_406 = lean_ctor_get(x_17, 1);
lean_inc(x_406);
lean_inc(x_405);
lean_dec(x_17);
x_407 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_408 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_407, x_8, x_406);
x_409 = lean_ctor_get(x_405, 0);
lean_inc(x_409);
lean_dec(x_405);
x_410 = lean_ctor_get(x_408, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_408, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_412 = x_408;
} else {
 lean_dec_ref(x_408);
 x_412 = lean_box(0);
}
x_413 = lean_ctor_get(x_409, 2);
lean_inc(x_413);
lean_dec(x_409);
x_508 = lean_unbox(x_410);
lean_dec(x_410);
if (x_508 == 0)
{
lean_dec(x_412);
x_414 = x_2;
x_415 = x_3;
x_416 = x_4;
x_417 = x_5;
x_418 = x_6;
x_419 = x_7;
x_420 = x_8;
x_421 = x_9;
x_422 = x_411;
goto block_507;
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_509 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_510 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_412)) {
 x_511 = lean_alloc_ctor(7, 2, 0);
} else {
 x_511 = x_412;
 lean_ctor_set_tag(x_511, 7);
}
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
x_512 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
x_513 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
lean_inc(x_413);
x_514 = l_Nat_reprFast(x_413);
x_515 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_515, 0, x_514);
x_516 = l_Lean_MessageData_ofFormat(x_515);
x_517 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_517, 0, x_513);
lean_ctor_set(x_517, 1, x_516);
x_518 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_518, 1, x_509);
x_519 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_407, x_518, x_6, x_7, x_8, x_9, x_411);
x_520 = lean_ctor_get(x_519, 1);
lean_inc(x_520);
lean_dec(x_519);
x_414 = x_2;
x_415 = x_3;
x_416 = x_4;
x_417 = x_5;
x_418 = x_6;
x_419 = x_7;
x_420 = x_8;
x_421 = x_9;
x_422 = x_520;
goto block_507;
}
block_507:
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_423 = lean_st_ref_take(x_414, x_422);
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_424, 14);
lean_inc(x_425);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_423, 1);
lean_inc(x_427);
lean_dec(x_423);
x_428 = lean_ctor_get(x_424, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_424, 1);
lean_inc(x_429);
x_430 = lean_ctor_get(x_424, 2);
lean_inc(x_430);
x_431 = lean_ctor_get(x_424, 3);
lean_inc(x_431);
x_432 = lean_ctor_get(x_424, 4);
lean_inc(x_432);
x_433 = lean_ctor_get(x_424, 5);
lean_inc(x_433);
x_434 = lean_ctor_get(x_424, 6);
lean_inc(x_434);
x_435 = lean_ctor_get(x_424, 7);
lean_inc(x_435);
x_436 = lean_ctor_get_uint8(x_424, sizeof(void*)*16);
x_437 = lean_ctor_get(x_424, 8);
lean_inc(x_437);
x_438 = lean_ctor_get(x_424, 9);
lean_inc(x_438);
x_439 = lean_ctor_get(x_424, 10);
lean_inc(x_439);
x_440 = lean_ctor_get(x_424, 11);
lean_inc(x_440);
x_441 = lean_ctor_get(x_424, 12);
lean_inc(x_441);
x_442 = lean_ctor_get(x_424, 13);
lean_inc(x_442);
x_443 = lean_ctor_get(x_424, 15);
lean_inc(x_443);
if (lean_is_exclusive(x_424)) {
 lean_ctor_release(x_424, 0);
 lean_ctor_release(x_424, 1);
 lean_ctor_release(x_424, 2);
 lean_ctor_release(x_424, 3);
 lean_ctor_release(x_424, 4);
 lean_ctor_release(x_424, 5);
 lean_ctor_release(x_424, 6);
 lean_ctor_release(x_424, 7);
 lean_ctor_release(x_424, 8);
 lean_ctor_release(x_424, 9);
 lean_ctor_release(x_424, 10);
 lean_ctor_release(x_424, 11);
 lean_ctor_release(x_424, 12);
 lean_ctor_release(x_424, 13);
 lean_ctor_release(x_424, 14);
 lean_ctor_release(x_424, 15);
 x_444 = x_424;
} else {
 lean_dec_ref(x_424);
 x_444 = lean_box(0);
}
x_445 = lean_ctor_get(x_425, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_425, 2);
lean_inc(x_446);
x_447 = lean_ctor_get(x_425, 3);
lean_inc(x_447);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 lean_ctor_release(x_425, 1);
 lean_ctor_release(x_425, 2);
 lean_ctor_release(x_425, 3);
 x_448 = x_425;
} else {
 lean_dec_ref(x_425);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_426, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_426, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_426, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_426, 3);
lean_inc(x_452);
x_453 = lean_ctor_get(x_426, 4);
lean_inc(x_453);
x_454 = lean_ctor_get(x_426, 5);
lean_inc(x_454);
x_455 = lean_ctor_get(x_426, 6);
lean_inc(x_455);
x_456 = lean_ctor_get(x_426, 7);
lean_inc(x_456);
x_457 = lean_ctor_get(x_426, 8);
lean_inc(x_457);
x_458 = lean_ctor_get(x_426, 9);
lean_inc(x_458);
x_459 = lean_ctor_get(x_426, 10);
lean_inc(x_459);
x_460 = lean_ctor_get(x_426, 11);
lean_inc(x_460);
x_461 = lean_ctor_get(x_426, 12);
lean_inc(x_461);
x_462 = lean_ctor_get(x_426, 13);
lean_inc(x_462);
x_463 = lean_ctor_get_uint8(x_426, sizeof(void*)*18);
x_464 = lean_ctor_get(x_426, 14);
lean_inc(x_464);
x_465 = lean_ctor_get(x_426, 15);
lean_inc(x_465);
x_466 = lean_ctor_get(x_426, 16);
lean_inc(x_466);
x_467 = lean_ctor_get(x_426, 17);
lean_inc(x_467);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 lean_ctor_release(x_426, 2);
 lean_ctor_release(x_426, 3);
 lean_ctor_release(x_426, 4);
 lean_ctor_release(x_426, 5);
 lean_ctor_release(x_426, 6);
 lean_ctor_release(x_426, 7);
 lean_ctor_release(x_426, 8);
 lean_ctor_release(x_426, 9);
 lean_ctor_release(x_426, 10);
 lean_ctor_release(x_426, 11);
 lean_ctor_release(x_426, 12);
 lean_ctor_release(x_426, 13);
 lean_ctor_release(x_426, 14);
 lean_ctor_release(x_426, 15);
 lean_ctor_release(x_426, 16);
 lean_ctor_release(x_426, 17);
 x_468 = x_426;
} else {
 lean_dec_ref(x_426);
 x_468 = lean_box(0);
}
lean_inc(x_1);
x_469 = l_Lean_PersistentArray_push___redArg(x_449, x_1);
lean_inc(x_413);
lean_inc(x_1);
x_470 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_450, x_1, x_413);
x_471 = lean_box(0);
x_472 = l_Lean_PersistentArray_push___redArg(x_454, x_471);
x_473 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_474 = l_Lean_PersistentArray_push___redArg(x_455, x_473);
x_475 = l_Lean_PersistentArray_push___redArg(x_456, x_473);
x_476 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_477 = l_Lean_PersistentArray_push___redArg(x_457, x_476);
x_478 = lean_box(0);
x_479 = l_Lean_PersistentArray_push___redArg(x_458, x_478);
x_480 = lean_box(0);
x_481 = l_Lean_PersistentArray_push___redArg(x_460, x_480);
if (lean_is_scalar(x_468)) {
 x_482 = lean_alloc_ctor(0, 18, 1);
} else {
 x_482 = x_468;
}
lean_ctor_set(x_482, 0, x_469);
lean_ctor_set(x_482, 1, x_470);
lean_ctor_set(x_482, 2, x_451);
lean_ctor_set(x_482, 3, x_452);
lean_ctor_set(x_482, 4, x_453);
lean_ctor_set(x_482, 5, x_472);
lean_ctor_set(x_482, 6, x_474);
lean_ctor_set(x_482, 7, x_475);
lean_ctor_set(x_482, 8, x_477);
lean_ctor_set(x_482, 9, x_479);
lean_ctor_set(x_482, 10, x_459);
lean_ctor_set(x_482, 11, x_481);
lean_ctor_set(x_482, 12, x_461);
lean_ctor_set(x_482, 13, x_462);
lean_ctor_set(x_482, 14, x_464);
lean_ctor_set(x_482, 15, x_465);
lean_ctor_set(x_482, 16, x_466);
lean_ctor_set(x_482, 17, x_467);
lean_ctor_set_uint8(x_482, sizeof(void*)*18, x_463);
if (lean_is_scalar(x_448)) {
 x_483 = lean_alloc_ctor(0, 4, 0);
} else {
 x_483 = x_448;
}
lean_ctor_set(x_483, 0, x_445);
lean_ctor_set(x_483, 1, x_482);
lean_ctor_set(x_483, 2, x_446);
lean_ctor_set(x_483, 3, x_447);
if (lean_is_scalar(x_444)) {
 x_484 = lean_alloc_ctor(0, 16, 1);
} else {
 x_484 = x_444;
}
lean_ctor_set(x_484, 0, x_428);
lean_ctor_set(x_484, 1, x_429);
lean_ctor_set(x_484, 2, x_430);
lean_ctor_set(x_484, 3, x_431);
lean_ctor_set(x_484, 4, x_432);
lean_ctor_set(x_484, 5, x_433);
lean_ctor_set(x_484, 6, x_434);
lean_ctor_set(x_484, 7, x_435);
lean_ctor_set(x_484, 8, x_437);
lean_ctor_set(x_484, 9, x_438);
lean_ctor_set(x_484, 10, x_439);
lean_ctor_set(x_484, 11, x_440);
lean_ctor_set(x_484, 12, x_441);
lean_ctor_set(x_484, 13, x_442);
lean_ctor_set(x_484, 14, x_483);
lean_ctor_set(x_484, 15, x_443);
lean_ctor_set_uint8(x_484, sizeof(void*)*16, x_436);
x_485 = lean_st_ref_set(x_414, x_484, x_427);
x_486 = lean_ctor_get(x_485, 1);
lean_inc(x_486);
lean_dec(x_485);
lean_inc(x_421);
lean_inc(x_420);
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_1);
x_487 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_414, x_415, x_416, x_417, x_418, x_419, x_420, x_421, x_486);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; lean_object* x_489; 
x_488 = lean_ctor_get(x_487, 1);
lean_inc(x_488);
lean_dec(x_487);
lean_inc(x_421);
lean_inc(x_420);
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_1);
x_489 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_413, x_414, x_415, x_416, x_417, x_418, x_419, x_420, x_421, x_488);
if (lean_obj_tag(x_489) == 0)
{
lean_object* x_490; lean_object* x_491; 
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
lean_dec(x_489);
x_491 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_414, x_415, x_416, x_417, x_418, x_419, x_420, x_421, x_490);
if (lean_obj_tag(x_491) == 0)
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_491, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_493 = x_491;
} else {
 lean_dec_ref(x_491);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(0, 2, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_413);
lean_ctor_set(x_494, 1, x_492);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_413);
x_495 = lean_ctor_get(x_491, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_491, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_491)) {
 lean_ctor_release(x_491, 0);
 lean_ctor_release(x_491, 1);
 x_497 = x_491;
} else {
 lean_dec_ref(x_491);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_496);
return x_498;
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_1);
x_499 = lean_ctor_get(x_489, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_489, 1);
lean_inc(x_500);
if (lean_is_exclusive(x_489)) {
 lean_ctor_release(x_489, 0);
 lean_ctor_release(x_489, 1);
 x_501 = x_489;
} else {
 lean_dec_ref(x_489);
 x_501 = lean_box(0);
}
if (lean_is_scalar(x_501)) {
 x_502 = lean_alloc_ctor(1, 2, 0);
} else {
 x_502 = x_501;
}
lean_ctor_set(x_502, 0, x_499);
lean_ctor_set(x_502, 1, x_500);
return x_502;
}
}
else
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_1);
x_503 = lean_ctor_get(x_487, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_487, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_505 = x_487;
} else {
 lean_dec_ref(x_487);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_503);
lean_ctor_set(x_506, 1, x_504);
return x_506;
}
}
}
}
else
{
lean_object* x_521; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_521 = lean_ctor_get(x_16, 0);
lean_inc(x_521);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_521);
return x_11;
}
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_ctor_get(x_11, 0);
x_523 = lean_ctor_get(x_11, 1);
lean_inc(x_523);
lean_inc(x_522);
lean_dec(x_11);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
lean_inc(x_1);
x_525 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_524, x_1);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_631; 
x_526 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_523);
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_529 = x_526;
} else {
 lean_dec_ref(x_526);
 x_529 = lean_box(0);
}
x_530 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_531 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_530, x_8, x_528);
x_532 = lean_ctor_get(x_527, 0);
lean_inc(x_532);
lean_dec(x_527);
x_533 = lean_ctor_get(x_531, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_531, 1);
lean_inc(x_534);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_535 = x_531;
} else {
 lean_dec_ref(x_531);
 x_535 = lean_box(0);
}
x_536 = lean_ctor_get(x_532, 2);
lean_inc(x_536);
lean_dec(x_532);
x_631 = lean_unbox(x_533);
lean_dec(x_533);
if (x_631 == 0)
{
lean_dec(x_535);
lean_dec(x_529);
x_537 = x_2;
x_538 = x_3;
x_539 = x_4;
x_540 = x_5;
x_541 = x_6;
x_542 = x_7;
x_543 = x_8;
x_544 = x_9;
x_545 = x_534;
goto block_630;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_632 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_633 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_535)) {
 x_634 = lean_alloc_ctor(7, 2, 0);
} else {
 x_634 = x_535;
 lean_ctor_set_tag(x_634, 7);
}
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
x_635 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
if (lean_is_scalar(x_529)) {
 x_636 = lean_alloc_ctor(7, 2, 0);
} else {
 x_636 = x_529;
 lean_ctor_set_tag(x_636, 7);
}
lean_ctor_set(x_636, 0, x_634);
lean_ctor_set(x_636, 1, x_635);
lean_inc(x_536);
x_637 = l_Nat_reprFast(x_536);
x_638 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_638, 0, x_637);
x_639 = l_Lean_MessageData_ofFormat(x_638);
x_640 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_640, 0, x_636);
lean_ctor_set(x_640, 1, x_639);
x_641 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_632);
x_642 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_530, x_641, x_6, x_7, x_8, x_9, x_534);
x_643 = lean_ctor_get(x_642, 1);
lean_inc(x_643);
lean_dec(x_642);
x_537 = x_2;
x_538 = x_3;
x_539 = x_4;
x_540 = x_5;
x_541 = x_6;
x_542 = x_7;
x_543 = x_8;
x_544 = x_9;
x_545 = x_643;
goto block_630;
}
block_630:
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; uint8_t x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_546 = lean_st_ref_take(x_537, x_545);
x_547 = lean_ctor_get(x_546, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_547, 14);
lean_inc(x_548);
x_549 = lean_ctor_get(x_548, 1);
lean_inc(x_549);
x_550 = lean_ctor_get(x_546, 1);
lean_inc(x_550);
lean_dec(x_546);
x_551 = lean_ctor_get(x_547, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_547, 1);
lean_inc(x_552);
x_553 = lean_ctor_get(x_547, 2);
lean_inc(x_553);
x_554 = lean_ctor_get(x_547, 3);
lean_inc(x_554);
x_555 = lean_ctor_get(x_547, 4);
lean_inc(x_555);
x_556 = lean_ctor_get(x_547, 5);
lean_inc(x_556);
x_557 = lean_ctor_get(x_547, 6);
lean_inc(x_557);
x_558 = lean_ctor_get(x_547, 7);
lean_inc(x_558);
x_559 = lean_ctor_get_uint8(x_547, sizeof(void*)*16);
x_560 = lean_ctor_get(x_547, 8);
lean_inc(x_560);
x_561 = lean_ctor_get(x_547, 9);
lean_inc(x_561);
x_562 = lean_ctor_get(x_547, 10);
lean_inc(x_562);
x_563 = lean_ctor_get(x_547, 11);
lean_inc(x_563);
x_564 = lean_ctor_get(x_547, 12);
lean_inc(x_564);
x_565 = lean_ctor_get(x_547, 13);
lean_inc(x_565);
x_566 = lean_ctor_get(x_547, 15);
lean_inc(x_566);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 lean_ctor_release(x_547, 2);
 lean_ctor_release(x_547, 3);
 lean_ctor_release(x_547, 4);
 lean_ctor_release(x_547, 5);
 lean_ctor_release(x_547, 6);
 lean_ctor_release(x_547, 7);
 lean_ctor_release(x_547, 8);
 lean_ctor_release(x_547, 9);
 lean_ctor_release(x_547, 10);
 lean_ctor_release(x_547, 11);
 lean_ctor_release(x_547, 12);
 lean_ctor_release(x_547, 13);
 lean_ctor_release(x_547, 14);
 lean_ctor_release(x_547, 15);
 x_567 = x_547;
} else {
 lean_dec_ref(x_547);
 x_567 = lean_box(0);
}
x_568 = lean_ctor_get(x_548, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_548, 2);
lean_inc(x_569);
x_570 = lean_ctor_get(x_548, 3);
lean_inc(x_570);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 lean_ctor_release(x_548, 2);
 lean_ctor_release(x_548, 3);
 x_571 = x_548;
} else {
 lean_dec_ref(x_548);
 x_571 = lean_box(0);
}
x_572 = lean_ctor_get(x_549, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_549, 1);
lean_inc(x_573);
x_574 = lean_ctor_get(x_549, 2);
lean_inc(x_574);
x_575 = lean_ctor_get(x_549, 3);
lean_inc(x_575);
x_576 = lean_ctor_get(x_549, 4);
lean_inc(x_576);
x_577 = lean_ctor_get(x_549, 5);
lean_inc(x_577);
x_578 = lean_ctor_get(x_549, 6);
lean_inc(x_578);
x_579 = lean_ctor_get(x_549, 7);
lean_inc(x_579);
x_580 = lean_ctor_get(x_549, 8);
lean_inc(x_580);
x_581 = lean_ctor_get(x_549, 9);
lean_inc(x_581);
x_582 = lean_ctor_get(x_549, 10);
lean_inc(x_582);
x_583 = lean_ctor_get(x_549, 11);
lean_inc(x_583);
x_584 = lean_ctor_get(x_549, 12);
lean_inc(x_584);
x_585 = lean_ctor_get(x_549, 13);
lean_inc(x_585);
x_586 = lean_ctor_get_uint8(x_549, sizeof(void*)*18);
x_587 = lean_ctor_get(x_549, 14);
lean_inc(x_587);
x_588 = lean_ctor_get(x_549, 15);
lean_inc(x_588);
x_589 = lean_ctor_get(x_549, 16);
lean_inc(x_589);
x_590 = lean_ctor_get(x_549, 17);
lean_inc(x_590);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 lean_ctor_release(x_549, 2);
 lean_ctor_release(x_549, 3);
 lean_ctor_release(x_549, 4);
 lean_ctor_release(x_549, 5);
 lean_ctor_release(x_549, 6);
 lean_ctor_release(x_549, 7);
 lean_ctor_release(x_549, 8);
 lean_ctor_release(x_549, 9);
 lean_ctor_release(x_549, 10);
 lean_ctor_release(x_549, 11);
 lean_ctor_release(x_549, 12);
 lean_ctor_release(x_549, 13);
 lean_ctor_release(x_549, 14);
 lean_ctor_release(x_549, 15);
 lean_ctor_release(x_549, 16);
 lean_ctor_release(x_549, 17);
 x_591 = x_549;
} else {
 lean_dec_ref(x_549);
 x_591 = lean_box(0);
}
lean_inc(x_1);
x_592 = l_Lean_PersistentArray_push___redArg(x_572, x_1);
lean_inc(x_536);
lean_inc(x_1);
x_593 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_573, x_1, x_536);
x_594 = lean_box(0);
x_595 = l_Lean_PersistentArray_push___redArg(x_577, x_594);
x_596 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_597 = l_Lean_PersistentArray_push___redArg(x_578, x_596);
x_598 = l_Lean_PersistentArray_push___redArg(x_579, x_596);
x_599 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_600 = l_Lean_PersistentArray_push___redArg(x_580, x_599);
x_601 = lean_box(0);
x_602 = l_Lean_PersistentArray_push___redArg(x_581, x_601);
x_603 = lean_box(0);
x_604 = l_Lean_PersistentArray_push___redArg(x_583, x_603);
if (lean_is_scalar(x_591)) {
 x_605 = lean_alloc_ctor(0, 18, 1);
} else {
 x_605 = x_591;
}
lean_ctor_set(x_605, 0, x_592);
lean_ctor_set(x_605, 1, x_593);
lean_ctor_set(x_605, 2, x_574);
lean_ctor_set(x_605, 3, x_575);
lean_ctor_set(x_605, 4, x_576);
lean_ctor_set(x_605, 5, x_595);
lean_ctor_set(x_605, 6, x_597);
lean_ctor_set(x_605, 7, x_598);
lean_ctor_set(x_605, 8, x_600);
lean_ctor_set(x_605, 9, x_602);
lean_ctor_set(x_605, 10, x_582);
lean_ctor_set(x_605, 11, x_604);
lean_ctor_set(x_605, 12, x_584);
lean_ctor_set(x_605, 13, x_585);
lean_ctor_set(x_605, 14, x_587);
lean_ctor_set(x_605, 15, x_588);
lean_ctor_set(x_605, 16, x_589);
lean_ctor_set(x_605, 17, x_590);
lean_ctor_set_uint8(x_605, sizeof(void*)*18, x_586);
if (lean_is_scalar(x_571)) {
 x_606 = lean_alloc_ctor(0, 4, 0);
} else {
 x_606 = x_571;
}
lean_ctor_set(x_606, 0, x_568);
lean_ctor_set(x_606, 1, x_605);
lean_ctor_set(x_606, 2, x_569);
lean_ctor_set(x_606, 3, x_570);
if (lean_is_scalar(x_567)) {
 x_607 = lean_alloc_ctor(0, 16, 1);
} else {
 x_607 = x_567;
}
lean_ctor_set(x_607, 0, x_551);
lean_ctor_set(x_607, 1, x_552);
lean_ctor_set(x_607, 2, x_553);
lean_ctor_set(x_607, 3, x_554);
lean_ctor_set(x_607, 4, x_555);
lean_ctor_set(x_607, 5, x_556);
lean_ctor_set(x_607, 6, x_557);
lean_ctor_set(x_607, 7, x_558);
lean_ctor_set(x_607, 8, x_560);
lean_ctor_set(x_607, 9, x_561);
lean_ctor_set(x_607, 10, x_562);
lean_ctor_set(x_607, 11, x_563);
lean_ctor_set(x_607, 12, x_564);
lean_ctor_set(x_607, 13, x_565);
lean_ctor_set(x_607, 14, x_606);
lean_ctor_set(x_607, 15, x_566);
lean_ctor_set_uint8(x_607, sizeof(void*)*16, x_559);
x_608 = lean_st_ref_set(x_537, x_607, x_550);
x_609 = lean_ctor_get(x_608, 1);
lean_inc(x_609);
lean_dec(x_608);
lean_inc(x_544);
lean_inc(x_543);
lean_inc(x_542);
lean_inc(x_541);
lean_inc(x_540);
lean_inc(x_539);
lean_inc(x_538);
lean_inc(x_537);
lean_inc(x_1);
x_610 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_537, x_538, x_539, x_540, x_541, x_542, x_543, x_544, x_609);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_ctor_get(x_610, 1);
lean_inc(x_611);
lean_dec(x_610);
lean_inc(x_544);
lean_inc(x_543);
lean_inc(x_542);
lean_inc(x_541);
lean_inc(x_540);
lean_inc(x_539);
lean_inc(x_538);
lean_inc(x_537);
lean_inc(x_536);
lean_inc(x_1);
x_612 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_536, x_537, x_538, x_539, x_540, x_541, x_542, x_543, x_544, x_611);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; 
x_613 = lean_ctor_get(x_612, 1);
lean_inc(x_613);
lean_dec(x_612);
x_614 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_537, x_538, x_539, x_540, x_541, x_542, x_543, x_544, x_613);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_614, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_616 = x_614;
} else {
 lean_dec_ref(x_614);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(0, 2, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_536);
lean_ctor_set(x_617, 1, x_615);
return x_617;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_536);
x_618 = lean_ctor_get(x_614, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_614, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_620 = x_614;
} else {
 lean_dec_ref(x_614);
 x_620 = lean_box(0);
}
if (lean_is_scalar(x_620)) {
 x_621 = lean_alloc_ctor(1, 2, 0);
} else {
 x_621 = x_620;
}
lean_ctor_set(x_621, 0, x_618);
lean_ctor_set(x_621, 1, x_619);
return x_621;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_1);
x_622 = lean_ctor_get(x_612, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_612, 1);
lean_inc(x_623);
if (lean_is_exclusive(x_612)) {
 lean_ctor_release(x_612, 0);
 lean_ctor_release(x_612, 1);
 x_624 = x_612;
} else {
 lean_dec_ref(x_612);
 x_624 = lean_box(0);
}
if (lean_is_scalar(x_624)) {
 x_625 = lean_alloc_ctor(1, 2, 0);
} else {
 x_625 = x_624;
}
lean_ctor_set(x_625, 0, x_622);
lean_ctor_set(x_625, 1, x_623);
return x_625;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_1);
x_626 = lean_ctor_get(x_610, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_610, 1);
lean_inc(x_627);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 x_628 = x_610;
} else {
 lean_dec_ref(x_610);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 2, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_626);
lean_ctor_set(x_629, 1, x_627);
return x_629;
}
}
}
else
{
lean_object* x_644; lean_object* x_645; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_644 = lean_ctor_get(x_525, 0);
lean_inc(x_644);
lean_dec(x_525);
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_523);
return x_645;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2;
x_11 = l_Lean_Meta_isExprDefEq(x_8, x_10, x_2, x_3, x_4, x_5, x_9);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = !lean_is_exclusive(x_7);
if (x_12 == 0)
{
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get(x_7, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_7);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isInt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hAdd", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("found term with non-standard instance", 37, 37);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_22 = l_Lean_Expr_cleanupAnnotations(x_16);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_36 = l_Lean_Expr_isApp(x_35);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_35);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2;
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_18);
x_40 = l_Lean_Meta_isInstHAddInt___redArg(x_30, x_7, x_17);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_27);
lean_dec(x_24);
if (x_2 == 0)
{
lean_object* x_43; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_11 = x_43;
goto block_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
lean_dec(x_40);
x_45 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*6 + 11);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_11 = x_48;
goto block_14;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_45);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_45, 1);
x_51 = lean_ctor_get(x_45, 0);
lean_dec(x_51);
x_52 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4;
x_53 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_45, 7);
lean_ctor_set(x_45, 1, x_53);
lean_ctor_set(x_45, 0, x_52);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_45);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_Grind_reportIssue(x_55, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
x_11 = x_57;
goto block_14;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec(x_45);
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4;
x_60 = l_Lean_indentExpr(x_1);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_Meta_Grind_reportIssue(x_63, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_11 = x_65;
goto block_14;
}
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_40);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_40, 0);
lean_dec(x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_27);
lean_ctor_set(x_68, 1, x_24);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_40, 0, x_69);
return x_40;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_40, 1);
lean_inc(x_70);
lean_dec(x_40);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_27);
lean_ctor_set(x_71, 1, x_24);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_box(1);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hMul", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_22 = l_Lean_Expr_cleanupAnnotations(x_16);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_36 = l_Lean_Expr_isApp(x_35);
if (x_36 == 0)
{
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = l_Lean_Expr_appFnCleanup___redArg(x_35);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__2;
x_39 = l_Lean_Expr_isConstOf(x_37, x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
lean_dec(x_18);
x_40 = l_Lean_Meta_isInstHMulInt___redArg(x_30, x_7, x_17);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_dec(x_27);
lean_dec(x_24);
if (x_2 == 0)
{
lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_11 = x_43;
goto block_14;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_40);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_40, 1);
x_46 = lean_ctor_get(x_40, 0);
lean_dec(x_46);
x_47 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_45);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get_uint8(x_48, sizeof(void*)*6 + 11);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_free_object(x_40);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec(x_47);
x_11 = x_50;
goto block_14;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_47, 1);
x_53 = lean_ctor_get(x_47, 0);
lean_dec(x_53);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4;
x_55 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_47, 7);
lean_ctor_set(x_47, 1, x_55);
lean_ctor_set(x_47, 0, x_54);
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_56);
lean_ctor_set(x_40, 0, x_47);
x_57 = l_Lean_Meta_Grind_reportIssue(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_52);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_11 = x_58;
goto block_14;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_47, 1);
lean_inc(x_59);
lean_dec(x_47);
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4;
x_61 = l_Lean_indentExpr(x_1);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_63);
lean_ctor_set(x_40, 0, x_62);
x_64 = l_Lean_Meta_Grind_reportIssue(x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_59);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_11 = x_65;
goto block_14;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_40, 1);
lean_inc(x_66);
lean_dec(x_40);
x_67 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get_uint8(x_68, sizeof(void*)*6 + 11);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_11 = x_70;
goto block_14;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_72 = x_67;
} else {
 lean_dec_ref(x_67);
 x_72 = lean_box(0);
}
x_73 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4;
x_74 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(7, 2, 0);
} else {
 x_75 = x_72;
 lean_ctor_set_tag(x_75, 7);
}
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Meta_Grind_reportIssue(x_77, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_71);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_11 = x_79;
goto block_14;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_40);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_40, 1);
x_82 = lean_ctor_get(x_40, 0);
lean_dec(x_82);
x_83 = l_Lean_Meta_getIntValue_x3f(x_27, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
lean_free_object(x_40);
lean_dec(x_24);
x_85 = !lean_is_exclusive(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 0);
lean_dec(x_86);
x_87 = lean_box(0);
lean_ctor_set(x_83, 0, x_87);
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 1);
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_83);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; 
x_92 = lean_ctor_get(x_83, 0);
lean_dec(x_92);
x_93 = !lean_is_exclusive(x_84);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_84, 0);
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_40, 0, x_94);
lean_ctor_set(x_84, 0, x_40);
return x_83;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_84, 0);
lean_inc(x_95);
lean_dec(x_84);
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_40, 0, x_95);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_40);
lean_ctor_set(x_83, 0, x_96);
return x_83;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_ctor_get(x_83, 1);
lean_inc(x_97);
lean_dec(x_83);
x_98 = lean_ctor_get(x_84, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 x_99 = x_84;
} else {
 lean_dec_ref(x_84);
 x_99 = lean_box(0);
}
lean_ctor_set(x_40, 1, x_24);
lean_ctor_set(x_40, 0, x_98);
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(1, 1, 0);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_40);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_free_object(x_40);
lean_dec(x_24);
x_102 = !lean_is_exclusive(x_83);
if (x_102 == 0)
{
return x_83;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_83, 0);
x_104 = lean_ctor_get(x_83, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_83);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_40, 1);
lean_inc(x_106);
lean_dec(x_40);
x_107 = l_Lean_Meta_getIntValue_x3f(x_27, x_6, x_7, x_8, x_9, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_24);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_box(0);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_107, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_108, 0);
lean_inc(x_115);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 x_116 = x_108;
} else {
 lean_dec_ref(x_108);
 x_116 = lean_box(0);
}
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_24);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(1, 1, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
if (lean_is_scalar(x_114)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_114;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_113);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_24);
x_120 = lean_ctor_get(x_107, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_107, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_122 = x_107;
} else {
 lean_dec_ref(x_107);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
}
}
}
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_10);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_13);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_box(1);
lean_ctor_set(x_12, 0, x_20);
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_Arith_Cutsat_isMul___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_isMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isMul(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("monomial expected, found numeral", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\ninternalizing as variable", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = lean_box(1);
x_37 = lean_unbox(x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_37, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_41 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_43;
goto block_35;
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_41);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_ctor_get(x_41, 1);
x_46 = lean_ctor_get(x_41, 0);
lean_dec(x_46);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = l_Int_Linear_Poly_isZero(x_2);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_free_object(x_42);
lean_dec(x_48);
lean_free_object(x_41);
x_50 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_45);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*6 + 11);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_53;
goto block_35;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_55 = lean_ctor_get(x_50, 1);
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
x_57 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
lean_inc(x_1);
x_58 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_58);
lean_ctor_set(x_50, 0, x_57);
x_59 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_50);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Meta_Grind_reportIssue(x_60, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_55);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_62;
goto block_35;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_50, 1);
lean_inc(x_63);
lean_dec(x_50);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
lean_inc(x_1);
x_65 = l_Lean_indentExpr(x_1);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_Grind_reportIssue(x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_70;
goto block_35;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set_tag(x_42, 0);
return x_41;
}
}
else
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_42, 0);
lean_inc(x_71);
lean_dec(x_42);
x_72 = l_Int_Linear_Poly_isZero(x_2);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_71);
lean_free_object(x_41);
x_73 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_45);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_74, sizeof(void*)*6 + 11);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_76;
goto block_35;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_78 = x_73;
} else {
 lean_dec_ref(x_73);
 x_78 = lean_box(0);
}
x_79 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
lean_inc(x_1);
x_80 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_78)) {
 x_81 = lean_alloc_ctor(7, 2, 0);
} else {
 x_81 = x_78;
 lean_ctor_set_tag(x_81, 7);
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_Meta_Grind_reportIssue(x_83, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_77);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_85;
goto block_35;
}
}
else
{
lean_object* x_86; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_86, 0, x_71);
lean_ctor_set(x_41, 0, x_86);
return x_41;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_ctor_get(x_41, 1);
lean_inc(x_87);
lean_dec(x_41);
x_88 = lean_ctor_get(x_42, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_89 = x_42;
} else {
 lean_dec_ref(x_42);
 x_89 = lean_box(0);
}
x_90 = l_Int_Linear_Poly_isZero(x_2);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_89);
lean_dec(x_88);
x_91 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_87);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_92, sizeof(void*)*6 + 11);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_94;
goto block_35;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_96 = x_91;
} else {
 lean_dec_ref(x_91);
 x_96 = lean_box(0);
}
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
lean_inc(x_1);
x_98 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_96)) {
 x_99 = lean_alloc_ctor(7, 2, 0);
} else {
 x_99 = x_96;
 lean_ctor_set_tag(x_99, 7);
}
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Meta_Grind_reportIssue(x_101, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_95);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_103;
goto block_35;
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_89)) {
 x_104 = lean_alloc_ctor(0, 1, 0);
} else {
 x_104 = x_89;
 lean_ctor_set_tag(x_104, 0);
}
lean_ctor_set(x_104, 0, x_88);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_87);
return x_105;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_41);
if (x_106 == 0)
{
return x_41;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_41, 0);
x_108 = lean_ctor_get(x_41, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_41);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_1);
x_110 = lean_ctor_get(x_39, 0);
lean_inc(x_110);
lean_dec(x_39);
x_111 = lean_ctor_get(x_38, 1);
lean_inc(x_111);
lean_dec(x_38);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_grind_cutsat_mk_var(x_113, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_111);
if (lean_obj_tag(x_114) == 0)
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_114, 0);
x_117 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_2);
lean_ctor_set(x_114, 0, x_117);
return x_114;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_114, 0);
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_114);
x_120 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_120, 0, x_112);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_2);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
else
{
uint8_t x_122; 
lean_dec(x_112);
lean_dec(x_2);
x_122 = !lean_is_exclusive(x_114);
if (x_122 == 0)
{
return x_114;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_114, 0);
x_124 = lean_ctor_get(x_114, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_114);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_38);
if (x_126 == 0)
{
return x_38;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_38, 0);
x_128 = lean_ctor_get(x_38, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_38);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
block_35:
{
lean_object* x_21; 
x_21 = lean_grind_cutsat_mk_var(x_1, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0;
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_2);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0;
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
lean_inc(x_1);
x_14 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_1 = x_20;
x_2 = x_23;
x_11 = x_24;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1;
x_17 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_21, x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly_go(x_20, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
return x_26;
}
else
{
lean_dec(x_20);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
}
}
}
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_IntInstTesters(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__8);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__10 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__10);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__12 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__12);
l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13 = _init_l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13);
l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isInt___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
