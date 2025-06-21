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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_282; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_282 = lean_unbox(x_25);
lean_dec(x_25);
if (x_282 == 0)
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
goto block_281;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_283 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_284 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_284);
lean_ctor_set(x_22, 0, x_283);
x_285 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_285);
lean_ctor_set(x_17, 0, x_22);
lean_inc(x_27);
x_286 = l_Nat_reprFast(x_27);
x_287 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_287, 0, x_286);
x_288 = l_Lean_MessageData_ofFormat(x_287);
x_289 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_289, 0, x_17);
lean_ctor_set(x_289, 1, x_288);
x_290 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_283);
x_291 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_290, x_6, x_7, x_8, x_9, x_26);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec(x_291);
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_292;
goto block_281;
}
block_281:
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
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
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
x_105 = lean_ctor_get_uint8(x_40, sizeof(void*)*17);
x_106 = lean_ctor_get(x_40, 14);
x_107 = lean_ctor_get(x_40, 15);
x_108 = lean_ctor_get(x_40, 16);
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
x_109 = l_Lean_PersistentArray_push___redArg(x_91, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_110 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_92, x_1, x_27);
x_111 = lean_box(0);
x_112 = l_Lean_PersistentArray_push___redArg(x_96, x_111);
x_113 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_114 = l_Lean_PersistentArray_push___redArg(x_97, x_113);
x_115 = l_Lean_PersistentArray_push___redArg(x_98, x_113);
x_116 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_117 = l_Lean_PersistentArray_push___redArg(x_99, x_116);
x_118 = lean_box(0);
x_119 = l_Lean_PersistentArray_push___redArg(x_100, x_118);
x_120 = lean_box(0);
x_121 = l_Lean_PersistentArray_push___redArg(x_102, x_120);
x_122 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_122, 0, x_109);
lean_ctor_set(x_122, 1, x_110);
lean_ctor_set(x_122, 2, x_93);
lean_ctor_set(x_122, 3, x_94);
lean_ctor_set(x_122, 4, x_95);
lean_ctor_set(x_122, 5, x_112);
lean_ctor_set(x_122, 6, x_114);
lean_ctor_set(x_122, 7, x_115);
lean_ctor_set(x_122, 8, x_117);
lean_ctor_set(x_122, 9, x_119);
lean_ctor_set(x_122, 10, x_101);
lean_ctor_set(x_122, 11, x_121);
lean_ctor_set(x_122, 12, x_103);
lean_ctor_set(x_122, 13, x_104);
lean_ctor_set(x_122, 14, x_106);
lean_ctor_set(x_122, 15, x_107);
lean_ctor_set(x_122, 16, x_108);
lean_ctor_set_uint8(x_122, sizeof(void*)*17, x_105);
lean_ctor_set(x_39, 1, x_122);
x_123 = lean_st_ref_set(x_28, x_38, x_41);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_125 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
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
x_127 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_27);
lean_ctor_set(x_132, 1, x_130);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_27);
x_133 = lean_ctor_get(x_129, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_129, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_135 = x_129;
} else {
 lean_dec_ref(x_129);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
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
x_137 = lean_ctor_get(x_127, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_127, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_139 = x_127;
} else {
 lean_dec_ref(x_127);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
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
x_141 = lean_ctor_get(x_125, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_125, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_143 = x_125;
} else {
 lean_dec_ref(x_125);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_145 = lean_ctor_get(x_39, 0);
x_146 = lean_ctor_get(x_39, 2);
x_147 = lean_ctor_get(x_39, 3);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_39);
x_148 = lean_ctor_get(x_40, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_40, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_40, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_40, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_40, 4);
lean_inc(x_152);
x_153 = lean_ctor_get(x_40, 5);
lean_inc(x_153);
x_154 = lean_ctor_get(x_40, 6);
lean_inc(x_154);
x_155 = lean_ctor_get(x_40, 7);
lean_inc(x_155);
x_156 = lean_ctor_get(x_40, 8);
lean_inc(x_156);
x_157 = lean_ctor_get(x_40, 9);
lean_inc(x_157);
x_158 = lean_ctor_get(x_40, 10);
lean_inc(x_158);
x_159 = lean_ctor_get(x_40, 11);
lean_inc(x_159);
x_160 = lean_ctor_get(x_40, 12);
lean_inc(x_160);
x_161 = lean_ctor_get(x_40, 13);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_40, sizeof(void*)*17);
x_163 = lean_ctor_get(x_40, 14);
lean_inc(x_163);
x_164 = lean_ctor_get(x_40, 15);
lean_inc(x_164);
x_165 = lean_ctor_get(x_40, 16);
lean_inc(x_165);
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
 x_166 = x_40;
} else {
 lean_dec_ref(x_40);
 x_166 = lean_box(0);
}
lean_inc(x_1);
x_167 = l_Lean_PersistentArray_push___redArg(x_148, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_168 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_149, x_1, x_27);
x_169 = lean_box(0);
x_170 = l_Lean_PersistentArray_push___redArg(x_153, x_169);
x_171 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_172 = l_Lean_PersistentArray_push___redArg(x_154, x_171);
x_173 = l_Lean_PersistentArray_push___redArg(x_155, x_171);
x_174 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_175 = l_Lean_PersistentArray_push___redArg(x_156, x_174);
x_176 = lean_box(0);
x_177 = l_Lean_PersistentArray_push___redArg(x_157, x_176);
x_178 = lean_box(0);
x_179 = l_Lean_PersistentArray_push___redArg(x_159, x_178);
if (lean_is_scalar(x_166)) {
 x_180 = lean_alloc_ctor(0, 17, 1);
} else {
 x_180 = x_166;
}
lean_ctor_set(x_180, 0, x_167);
lean_ctor_set(x_180, 1, x_168);
lean_ctor_set(x_180, 2, x_150);
lean_ctor_set(x_180, 3, x_151);
lean_ctor_set(x_180, 4, x_152);
lean_ctor_set(x_180, 5, x_170);
lean_ctor_set(x_180, 6, x_172);
lean_ctor_set(x_180, 7, x_173);
lean_ctor_set(x_180, 8, x_175);
lean_ctor_set(x_180, 9, x_177);
lean_ctor_set(x_180, 10, x_158);
lean_ctor_set(x_180, 11, x_179);
lean_ctor_set(x_180, 12, x_160);
lean_ctor_set(x_180, 13, x_161);
lean_ctor_set(x_180, 14, x_163);
lean_ctor_set(x_180, 15, x_164);
lean_ctor_set(x_180, 16, x_165);
lean_ctor_set_uint8(x_180, sizeof(void*)*17, x_162);
x_181 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_181, 0, x_145);
lean_ctor_set(x_181, 1, x_180);
lean_ctor_set(x_181, 2, x_146);
lean_ctor_set(x_181, 3, x_147);
lean_ctor_set(x_38, 14, x_181);
x_182 = lean_st_ref_set(x_28, x_38, x_41);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_184 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_183);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; 
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
lean_inc(x_27);
lean_inc(x_1);
x_186 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_ctor_get(x_186, 1);
lean_inc(x_187);
lean_dec(x_186);
x_188 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(0, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_27);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_27);
x_192 = lean_ctor_get(x_188, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_188, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_194 = x_188;
} else {
 lean_dec_ref(x_188);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_192);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
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
x_196 = lean_ctor_get(x_186, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_186, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_198 = x_186;
} else {
 lean_dec_ref(x_186);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
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
x_200 = lean_ctor_get(x_184, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_184, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_202 = x_184;
} else {
 lean_dec_ref(x_184);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(1, 2, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_201);
return x_203;
}
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_204 = lean_ctor_get(x_38, 0);
x_205 = lean_ctor_get(x_38, 1);
x_206 = lean_ctor_get(x_38, 2);
x_207 = lean_ctor_get(x_38, 3);
x_208 = lean_ctor_get(x_38, 4);
x_209 = lean_ctor_get(x_38, 5);
x_210 = lean_ctor_get(x_38, 6);
x_211 = lean_ctor_get(x_38, 7);
x_212 = lean_ctor_get_uint8(x_38, sizeof(void*)*16);
x_213 = lean_ctor_get(x_38, 8);
x_214 = lean_ctor_get(x_38, 9);
x_215 = lean_ctor_get(x_38, 10);
x_216 = lean_ctor_get(x_38, 11);
x_217 = lean_ctor_get(x_38, 12);
x_218 = lean_ctor_get(x_38, 13);
x_219 = lean_ctor_get(x_38, 15);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_38);
x_220 = lean_ctor_get(x_39, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_39, 2);
lean_inc(x_221);
x_222 = lean_ctor_get(x_39, 3);
lean_inc(x_222);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 x_223 = x_39;
} else {
 lean_dec_ref(x_39);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_40, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_40, 1);
lean_inc(x_225);
x_226 = lean_ctor_get(x_40, 2);
lean_inc(x_226);
x_227 = lean_ctor_get(x_40, 3);
lean_inc(x_227);
x_228 = lean_ctor_get(x_40, 4);
lean_inc(x_228);
x_229 = lean_ctor_get(x_40, 5);
lean_inc(x_229);
x_230 = lean_ctor_get(x_40, 6);
lean_inc(x_230);
x_231 = lean_ctor_get(x_40, 7);
lean_inc(x_231);
x_232 = lean_ctor_get(x_40, 8);
lean_inc(x_232);
x_233 = lean_ctor_get(x_40, 9);
lean_inc(x_233);
x_234 = lean_ctor_get(x_40, 10);
lean_inc(x_234);
x_235 = lean_ctor_get(x_40, 11);
lean_inc(x_235);
x_236 = lean_ctor_get(x_40, 12);
lean_inc(x_236);
x_237 = lean_ctor_get(x_40, 13);
lean_inc(x_237);
x_238 = lean_ctor_get_uint8(x_40, sizeof(void*)*17);
x_239 = lean_ctor_get(x_40, 14);
lean_inc(x_239);
x_240 = lean_ctor_get(x_40, 15);
lean_inc(x_240);
x_241 = lean_ctor_get(x_40, 16);
lean_inc(x_241);
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
 x_242 = x_40;
} else {
 lean_dec_ref(x_40);
 x_242 = lean_box(0);
}
lean_inc(x_1);
x_243 = l_Lean_PersistentArray_push___redArg(x_224, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_244 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_225, x_1, x_27);
x_245 = lean_box(0);
x_246 = l_Lean_PersistentArray_push___redArg(x_229, x_245);
x_247 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_248 = l_Lean_PersistentArray_push___redArg(x_230, x_247);
x_249 = l_Lean_PersistentArray_push___redArg(x_231, x_247);
x_250 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_251 = l_Lean_PersistentArray_push___redArg(x_232, x_250);
x_252 = lean_box(0);
x_253 = l_Lean_PersistentArray_push___redArg(x_233, x_252);
x_254 = lean_box(0);
x_255 = l_Lean_PersistentArray_push___redArg(x_235, x_254);
if (lean_is_scalar(x_242)) {
 x_256 = lean_alloc_ctor(0, 17, 1);
} else {
 x_256 = x_242;
}
lean_ctor_set(x_256, 0, x_243);
lean_ctor_set(x_256, 1, x_244);
lean_ctor_set(x_256, 2, x_226);
lean_ctor_set(x_256, 3, x_227);
lean_ctor_set(x_256, 4, x_228);
lean_ctor_set(x_256, 5, x_246);
lean_ctor_set(x_256, 6, x_248);
lean_ctor_set(x_256, 7, x_249);
lean_ctor_set(x_256, 8, x_251);
lean_ctor_set(x_256, 9, x_253);
lean_ctor_set(x_256, 10, x_234);
lean_ctor_set(x_256, 11, x_255);
lean_ctor_set(x_256, 12, x_236);
lean_ctor_set(x_256, 13, x_237);
lean_ctor_set(x_256, 14, x_239);
lean_ctor_set(x_256, 15, x_240);
lean_ctor_set(x_256, 16, x_241);
lean_ctor_set_uint8(x_256, sizeof(void*)*17, x_238);
if (lean_is_scalar(x_223)) {
 x_257 = lean_alloc_ctor(0, 4, 0);
} else {
 x_257 = x_223;
}
lean_ctor_set(x_257, 0, x_220);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set(x_257, 2, x_221);
lean_ctor_set(x_257, 3, x_222);
x_258 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_258, 0, x_204);
lean_ctor_set(x_258, 1, x_205);
lean_ctor_set(x_258, 2, x_206);
lean_ctor_set(x_258, 3, x_207);
lean_ctor_set(x_258, 4, x_208);
lean_ctor_set(x_258, 5, x_209);
lean_ctor_set(x_258, 6, x_210);
lean_ctor_set(x_258, 7, x_211);
lean_ctor_set(x_258, 8, x_213);
lean_ctor_set(x_258, 9, x_214);
lean_ctor_set(x_258, 10, x_215);
lean_ctor_set(x_258, 11, x_216);
lean_ctor_set(x_258, 12, x_217);
lean_ctor_set(x_258, 13, x_218);
lean_ctor_set(x_258, 14, x_257);
lean_ctor_set(x_258, 15, x_219);
lean_ctor_set_uint8(x_258, sizeof(void*)*16, x_212);
x_259 = lean_st_ref_set(x_28, x_258, x_41);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_261 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_260);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; 
x_262 = lean_ctor_get(x_261, 1);
lean_inc(x_262);
lean_dec(x_261);
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
x_263 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_262);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; 
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
lean_dec(x_263);
x_265 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_264);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_267 = x_265;
} else {
 lean_dec_ref(x_265);
 x_267 = lean_box(0);
}
if (lean_is_scalar(x_267)) {
 x_268 = lean_alloc_ctor(0, 2, 0);
} else {
 x_268 = x_267;
}
lean_ctor_set(x_268, 0, x_27);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_27);
x_269 = lean_ctor_get(x_265, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_265, 1);
lean_inc(x_270);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_271 = x_265;
} else {
 lean_dec_ref(x_265);
 x_271 = lean_box(0);
}
if (lean_is_scalar(x_271)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_271;
}
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_270);
return x_272;
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
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
x_273 = lean_ctor_get(x_263, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_263, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_275 = x_263;
} else {
 lean_dec_ref(x_263);
 x_275 = lean_box(0);
}
if (lean_is_scalar(x_275)) {
 x_276 = lean_alloc_ctor(1, 2, 0);
} else {
 x_276 = x_275;
}
lean_ctor_set(x_276, 0, x_273);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
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
x_277 = lean_ctor_get(x_261, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_261, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_279 = x_261;
} else {
 lean_dec_ref(x_261);
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
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_389; 
x_293 = lean_ctor_get(x_22, 0);
x_294 = lean_ctor_get(x_22, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_22);
x_295 = lean_ctor_get(x_23, 2);
lean_inc(x_295);
lean_dec(x_23);
x_389 = lean_unbox(x_293);
lean_dec(x_293);
if (x_389 == 0)
{
lean_free_object(x_17);
x_296 = x_2;
x_297 = x_3;
x_298 = x_4;
x_299 = x_5;
x_300 = x_6;
x_301 = x_7;
x_302 = x_8;
x_303 = x_9;
x_304 = x_294;
goto block_388;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_390 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_391 = l_Lean_MessageData_ofExpr(x_1);
x_392 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
x_393 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_393);
lean_ctor_set(x_17, 0, x_392);
lean_inc(x_295);
x_394 = l_Nat_reprFast(x_295);
x_395 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_395, 0, x_394);
x_396 = l_Lean_MessageData_ofFormat(x_395);
x_397 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_397, 0, x_17);
lean_ctor_set(x_397, 1, x_396);
x_398 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_390);
x_399 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_398, x_6, x_7, x_8, x_9, x_294);
x_400 = lean_ctor_get(x_399, 1);
lean_inc(x_400);
lean_dec(x_399);
x_296 = x_2;
x_297 = x_3;
x_298 = x_4;
x_299 = x_5;
x_300 = x_6;
x_301 = x_7;
x_302 = x_8;
x_303 = x_9;
x_304 = x_400;
goto block_388;
}
block_388:
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; uint8_t x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_305 = lean_st_ref_take(x_296, x_304);
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_306, 14);
lean_inc(x_307);
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
lean_dec(x_305);
x_310 = lean_ctor_get(x_306, 0);
lean_inc(x_310);
x_311 = lean_ctor_get(x_306, 1);
lean_inc(x_311);
x_312 = lean_ctor_get(x_306, 2);
lean_inc(x_312);
x_313 = lean_ctor_get(x_306, 3);
lean_inc(x_313);
x_314 = lean_ctor_get(x_306, 4);
lean_inc(x_314);
x_315 = lean_ctor_get(x_306, 5);
lean_inc(x_315);
x_316 = lean_ctor_get(x_306, 6);
lean_inc(x_316);
x_317 = lean_ctor_get(x_306, 7);
lean_inc(x_317);
x_318 = lean_ctor_get_uint8(x_306, sizeof(void*)*16);
x_319 = lean_ctor_get(x_306, 8);
lean_inc(x_319);
x_320 = lean_ctor_get(x_306, 9);
lean_inc(x_320);
x_321 = lean_ctor_get(x_306, 10);
lean_inc(x_321);
x_322 = lean_ctor_get(x_306, 11);
lean_inc(x_322);
x_323 = lean_ctor_get(x_306, 12);
lean_inc(x_323);
x_324 = lean_ctor_get(x_306, 13);
lean_inc(x_324);
x_325 = lean_ctor_get(x_306, 15);
lean_inc(x_325);
if (lean_is_exclusive(x_306)) {
 lean_ctor_release(x_306, 0);
 lean_ctor_release(x_306, 1);
 lean_ctor_release(x_306, 2);
 lean_ctor_release(x_306, 3);
 lean_ctor_release(x_306, 4);
 lean_ctor_release(x_306, 5);
 lean_ctor_release(x_306, 6);
 lean_ctor_release(x_306, 7);
 lean_ctor_release(x_306, 8);
 lean_ctor_release(x_306, 9);
 lean_ctor_release(x_306, 10);
 lean_ctor_release(x_306, 11);
 lean_ctor_release(x_306, 12);
 lean_ctor_release(x_306, 13);
 lean_ctor_release(x_306, 14);
 lean_ctor_release(x_306, 15);
 x_326 = x_306;
} else {
 lean_dec_ref(x_306);
 x_326 = lean_box(0);
}
x_327 = lean_ctor_get(x_307, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_307, 2);
lean_inc(x_328);
x_329 = lean_ctor_get(x_307, 3);
lean_inc(x_329);
if (lean_is_exclusive(x_307)) {
 lean_ctor_release(x_307, 0);
 lean_ctor_release(x_307, 1);
 lean_ctor_release(x_307, 2);
 lean_ctor_release(x_307, 3);
 x_330 = x_307;
} else {
 lean_dec_ref(x_307);
 x_330 = lean_box(0);
}
x_331 = lean_ctor_get(x_308, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_308, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_308, 2);
lean_inc(x_333);
x_334 = lean_ctor_get(x_308, 3);
lean_inc(x_334);
x_335 = lean_ctor_get(x_308, 4);
lean_inc(x_335);
x_336 = lean_ctor_get(x_308, 5);
lean_inc(x_336);
x_337 = lean_ctor_get(x_308, 6);
lean_inc(x_337);
x_338 = lean_ctor_get(x_308, 7);
lean_inc(x_338);
x_339 = lean_ctor_get(x_308, 8);
lean_inc(x_339);
x_340 = lean_ctor_get(x_308, 9);
lean_inc(x_340);
x_341 = lean_ctor_get(x_308, 10);
lean_inc(x_341);
x_342 = lean_ctor_get(x_308, 11);
lean_inc(x_342);
x_343 = lean_ctor_get(x_308, 12);
lean_inc(x_343);
x_344 = lean_ctor_get(x_308, 13);
lean_inc(x_344);
x_345 = lean_ctor_get_uint8(x_308, sizeof(void*)*17);
x_346 = lean_ctor_get(x_308, 14);
lean_inc(x_346);
x_347 = lean_ctor_get(x_308, 15);
lean_inc(x_347);
x_348 = lean_ctor_get(x_308, 16);
lean_inc(x_348);
if (lean_is_exclusive(x_308)) {
 lean_ctor_release(x_308, 0);
 lean_ctor_release(x_308, 1);
 lean_ctor_release(x_308, 2);
 lean_ctor_release(x_308, 3);
 lean_ctor_release(x_308, 4);
 lean_ctor_release(x_308, 5);
 lean_ctor_release(x_308, 6);
 lean_ctor_release(x_308, 7);
 lean_ctor_release(x_308, 8);
 lean_ctor_release(x_308, 9);
 lean_ctor_release(x_308, 10);
 lean_ctor_release(x_308, 11);
 lean_ctor_release(x_308, 12);
 lean_ctor_release(x_308, 13);
 lean_ctor_release(x_308, 14);
 lean_ctor_release(x_308, 15);
 lean_ctor_release(x_308, 16);
 x_349 = x_308;
} else {
 lean_dec_ref(x_308);
 x_349 = lean_box(0);
}
lean_inc(x_1);
x_350 = l_Lean_PersistentArray_push___redArg(x_331, x_1);
lean_inc(x_295);
lean_inc(x_1);
x_351 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_332, x_1, x_295);
x_352 = lean_box(0);
x_353 = l_Lean_PersistentArray_push___redArg(x_336, x_352);
x_354 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_355 = l_Lean_PersistentArray_push___redArg(x_337, x_354);
x_356 = l_Lean_PersistentArray_push___redArg(x_338, x_354);
x_357 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_358 = l_Lean_PersistentArray_push___redArg(x_339, x_357);
x_359 = lean_box(0);
x_360 = l_Lean_PersistentArray_push___redArg(x_340, x_359);
x_361 = lean_box(0);
x_362 = l_Lean_PersistentArray_push___redArg(x_342, x_361);
if (lean_is_scalar(x_349)) {
 x_363 = lean_alloc_ctor(0, 17, 1);
} else {
 x_363 = x_349;
}
lean_ctor_set(x_363, 0, x_350);
lean_ctor_set(x_363, 1, x_351);
lean_ctor_set(x_363, 2, x_333);
lean_ctor_set(x_363, 3, x_334);
lean_ctor_set(x_363, 4, x_335);
lean_ctor_set(x_363, 5, x_353);
lean_ctor_set(x_363, 6, x_355);
lean_ctor_set(x_363, 7, x_356);
lean_ctor_set(x_363, 8, x_358);
lean_ctor_set(x_363, 9, x_360);
lean_ctor_set(x_363, 10, x_341);
lean_ctor_set(x_363, 11, x_362);
lean_ctor_set(x_363, 12, x_343);
lean_ctor_set(x_363, 13, x_344);
lean_ctor_set(x_363, 14, x_346);
lean_ctor_set(x_363, 15, x_347);
lean_ctor_set(x_363, 16, x_348);
lean_ctor_set_uint8(x_363, sizeof(void*)*17, x_345);
if (lean_is_scalar(x_330)) {
 x_364 = lean_alloc_ctor(0, 4, 0);
} else {
 x_364 = x_330;
}
lean_ctor_set(x_364, 0, x_327);
lean_ctor_set(x_364, 1, x_363);
lean_ctor_set(x_364, 2, x_328);
lean_ctor_set(x_364, 3, x_329);
if (lean_is_scalar(x_326)) {
 x_365 = lean_alloc_ctor(0, 16, 1);
} else {
 x_365 = x_326;
}
lean_ctor_set(x_365, 0, x_310);
lean_ctor_set(x_365, 1, x_311);
lean_ctor_set(x_365, 2, x_312);
lean_ctor_set(x_365, 3, x_313);
lean_ctor_set(x_365, 4, x_314);
lean_ctor_set(x_365, 5, x_315);
lean_ctor_set(x_365, 6, x_316);
lean_ctor_set(x_365, 7, x_317);
lean_ctor_set(x_365, 8, x_319);
lean_ctor_set(x_365, 9, x_320);
lean_ctor_set(x_365, 10, x_321);
lean_ctor_set(x_365, 11, x_322);
lean_ctor_set(x_365, 12, x_323);
lean_ctor_set(x_365, 13, x_324);
lean_ctor_set(x_365, 14, x_364);
lean_ctor_set(x_365, 15, x_325);
lean_ctor_set_uint8(x_365, sizeof(void*)*16, x_318);
x_366 = lean_st_ref_set(x_296, x_365, x_309);
x_367 = lean_ctor_get(x_366, 1);
lean_inc(x_367);
lean_dec(x_366);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_1);
x_368 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_296, x_297, x_298, x_299, x_300, x_301, x_302, x_303, x_367);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; 
x_369 = lean_ctor_get(x_368, 1);
lean_inc(x_369);
lean_dec(x_368);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
lean_inc(x_298);
lean_inc(x_297);
lean_inc(x_296);
lean_inc(x_295);
lean_inc(x_1);
x_370 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_295, x_296, x_297, x_298, x_299, x_300, x_301, x_302, x_303, x_369);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec(x_370);
x_372 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_296, x_297, x_298, x_299, x_300, x_301, x_302, x_303, x_371);
if (lean_obj_tag(x_372) == 0)
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_372, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_374 = x_372;
} else {
 lean_dec_ref(x_372);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(0, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_295);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
lean_dec(x_295);
x_376 = lean_ctor_get(x_372, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_372, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 lean_ctor_release(x_372, 1);
 x_378 = x_372;
} else {
 lean_dec_ref(x_372);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_378)) {
 x_379 = lean_alloc_ctor(1, 2, 0);
} else {
 x_379 = x_378;
}
lean_ctor_set(x_379, 0, x_376);
lean_ctor_set(x_379, 1, x_377);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_1);
x_380 = lean_ctor_get(x_370, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_370, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_382 = x_370;
} else {
 lean_dec_ref(x_370);
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
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_299);
lean_dec(x_298);
lean_dec(x_297);
lean_dec(x_296);
lean_dec(x_295);
lean_dec(x_1);
x_384 = lean_ctor_get(x_368, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_368, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_386 = x_368;
} else {
 lean_dec_ref(x_368);
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
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_503; 
x_401 = lean_ctor_get(x_17, 0);
x_402 = lean_ctor_get(x_17, 1);
lean_inc(x_402);
lean_inc(x_401);
lean_dec(x_17);
x_403 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_404 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_403, x_8, x_402);
x_405 = lean_ctor_get(x_401, 0);
lean_inc(x_405);
lean_dec(x_401);
x_406 = lean_ctor_get(x_404, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_404, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_404)) {
 lean_ctor_release(x_404, 0);
 lean_ctor_release(x_404, 1);
 x_408 = x_404;
} else {
 lean_dec_ref(x_404);
 x_408 = lean_box(0);
}
x_409 = lean_ctor_get(x_405, 2);
lean_inc(x_409);
lean_dec(x_405);
x_503 = lean_unbox(x_406);
lean_dec(x_406);
if (x_503 == 0)
{
lean_dec(x_408);
x_410 = x_2;
x_411 = x_3;
x_412 = x_4;
x_413 = x_5;
x_414 = x_6;
x_415 = x_7;
x_416 = x_8;
x_417 = x_9;
x_418 = x_407;
goto block_502;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_504 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_505 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_408)) {
 x_506 = lean_alloc_ctor(7, 2, 0);
} else {
 x_506 = x_408;
 lean_ctor_set_tag(x_506, 7);
}
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
x_507 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
x_508 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
lean_inc(x_409);
x_509 = l_Nat_reprFast(x_409);
x_510 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_510, 0, x_509);
x_511 = l_Lean_MessageData_ofFormat(x_510);
x_512 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_512, 0, x_508);
lean_ctor_set(x_512, 1, x_511);
x_513 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_513, 0, x_512);
lean_ctor_set(x_513, 1, x_504);
x_514 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_403, x_513, x_6, x_7, x_8, x_9, x_407);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec(x_514);
x_410 = x_2;
x_411 = x_3;
x_412 = x_4;
x_413 = x_5;
x_414 = x_6;
x_415 = x_7;
x_416 = x_8;
x_417 = x_9;
x_418 = x_515;
goto block_502;
}
block_502:
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_419 = lean_st_ref_take(x_410, x_418);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
x_421 = lean_ctor_get(x_420, 14);
lean_inc(x_421);
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_419, 1);
lean_inc(x_423);
lean_dec(x_419);
x_424 = lean_ctor_get(x_420, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_420, 1);
lean_inc(x_425);
x_426 = lean_ctor_get(x_420, 2);
lean_inc(x_426);
x_427 = lean_ctor_get(x_420, 3);
lean_inc(x_427);
x_428 = lean_ctor_get(x_420, 4);
lean_inc(x_428);
x_429 = lean_ctor_get(x_420, 5);
lean_inc(x_429);
x_430 = lean_ctor_get(x_420, 6);
lean_inc(x_430);
x_431 = lean_ctor_get(x_420, 7);
lean_inc(x_431);
x_432 = lean_ctor_get_uint8(x_420, sizeof(void*)*16);
x_433 = lean_ctor_get(x_420, 8);
lean_inc(x_433);
x_434 = lean_ctor_get(x_420, 9);
lean_inc(x_434);
x_435 = lean_ctor_get(x_420, 10);
lean_inc(x_435);
x_436 = lean_ctor_get(x_420, 11);
lean_inc(x_436);
x_437 = lean_ctor_get(x_420, 12);
lean_inc(x_437);
x_438 = lean_ctor_get(x_420, 13);
lean_inc(x_438);
x_439 = lean_ctor_get(x_420, 15);
lean_inc(x_439);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 lean_ctor_release(x_420, 4);
 lean_ctor_release(x_420, 5);
 lean_ctor_release(x_420, 6);
 lean_ctor_release(x_420, 7);
 lean_ctor_release(x_420, 8);
 lean_ctor_release(x_420, 9);
 lean_ctor_release(x_420, 10);
 lean_ctor_release(x_420, 11);
 lean_ctor_release(x_420, 12);
 lean_ctor_release(x_420, 13);
 lean_ctor_release(x_420, 14);
 lean_ctor_release(x_420, 15);
 x_440 = x_420;
} else {
 lean_dec_ref(x_420);
 x_440 = lean_box(0);
}
x_441 = lean_ctor_get(x_421, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_421, 2);
lean_inc(x_442);
x_443 = lean_ctor_get(x_421, 3);
lean_inc(x_443);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 x_444 = x_421;
} else {
 lean_dec_ref(x_421);
 x_444 = lean_box(0);
}
x_445 = lean_ctor_get(x_422, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_422, 1);
lean_inc(x_446);
x_447 = lean_ctor_get(x_422, 2);
lean_inc(x_447);
x_448 = lean_ctor_get(x_422, 3);
lean_inc(x_448);
x_449 = lean_ctor_get(x_422, 4);
lean_inc(x_449);
x_450 = lean_ctor_get(x_422, 5);
lean_inc(x_450);
x_451 = lean_ctor_get(x_422, 6);
lean_inc(x_451);
x_452 = lean_ctor_get(x_422, 7);
lean_inc(x_452);
x_453 = lean_ctor_get(x_422, 8);
lean_inc(x_453);
x_454 = lean_ctor_get(x_422, 9);
lean_inc(x_454);
x_455 = lean_ctor_get(x_422, 10);
lean_inc(x_455);
x_456 = lean_ctor_get(x_422, 11);
lean_inc(x_456);
x_457 = lean_ctor_get(x_422, 12);
lean_inc(x_457);
x_458 = lean_ctor_get(x_422, 13);
lean_inc(x_458);
x_459 = lean_ctor_get_uint8(x_422, sizeof(void*)*17);
x_460 = lean_ctor_get(x_422, 14);
lean_inc(x_460);
x_461 = lean_ctor_get(x_422, 15);
lean_inc(x_461);
x_462 = lean_ctor_get(x_422, 16);
lean_inc(x_462);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 lean_ctor_release(x_422, 2);
 lean_ctor_release(x_422, 3);
 lean_ctor_release(x_422, 4);
 lean_ctor_release(x_422, 5);
 lean_ctor_release(x_422, 6);
 lean_ctor_release(x_422, 7);
 lean_ctor_release(x_422, 8);
 lean_ctor_release(x_422, 9);
 lean_ctor_release(x_422, 10);
 lean_ctor_release(x_422, 11);
 lean_ctor_release(x_422, 12);
 lean_ctor_release(x_422, 13);
 lean_ctor_release(x_422, 14);
 lean_ctor_release(x_422, 15);
 lean_ctor_release(x_422, 16);
 x_463 = x_422;
} else {
 lean_dec_ref(x_422);
 x_463 = lean_box(0);
}
lean_inc(x_1);
x_464 = l_Lean_PersistentArray_push___redArg(x_445, x_1);
lean_inc(x_409);
lean_inc(x_1);
x_465 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_446, x_1, x_409);
x_466 = lean_box(0);
x_467 = l_Lean_PersistentArray_push___redArg(x_450, x_466);
x_468 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_469 = l_Lean_PersistentArray_push___redArg(x_451, x_468);
x_470 = l_Lean_PersistentArray_push___redArg(x_452, x_468);
x_471 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_472 = l_Lean_PersistentArray_push___redArg(x_453, x_471);
x_473 = lean_box(0);
x_474 = l_Lean_PersistentArray_push___redArg(x_454, x_473);
x_475 = lean_box(0);
x_476 = l_Lean_PersistentArray_push___redArg(x_456, x_475);
if (lean_is_scalar(x_463)) {
 x_477 = lean_alloc_ctor(0, 17, 1);
} else {
 x_477 = x_463;
}
lean_ctor_set(x_477, 0, x_464);
lean_ctor_set(x_477, 1, x_465);
lean_ctor_set(x_477, 2, x_447);
lean_ctor_set(x_477, 3, x_448);
lean_ctor_set(x_477, 4, x_449);
lean_ctor_set(x_477, 5, x_467);
lean_ctor_set(x_477, 6, x_469);
lean_ctor_set(x_477, 7, x_470);
lean_ctor_set(x_477, 8, x_472);
lean_ctor_set(x_477, 9, x_474);
lean_ctor_set(x_477, 10, x_455);
lean_ctor_set(x_477, 11, x_476);
lean_ctor_set(x_477, 12, x_457);
lean_ctor_set(x_477, 13, x_458);
lean_ctor_set(x_477, 14, x_460);
lean_ctor_set(x_477, 15, x_461);
lean_ctor_set(x_477, 16, x_462);
lean_ctor_set_uint8(x_477, sizeof(void*)*17, x_459);
if (lean_is_scalar(x_444)) {
 x_478 = lean_alloc_ctor(0, 4, 0);
} else {
 x_478 = x_444;
}
lean_ctor_set(x_478, 0, x_441);
lean_ctor_set(x_478, 1, x_477);
lean_ctor_set(x_478, 2, x_442);
lean_ctor_set(x_478, 3, x_443);
if (lean_is_scalar(x_440)) {
 x_479 = lean_alloc_ctor(0, 16, 1);
} else {
 x_479 = x_440;
}
lean_ctor_set(x_479, 0, x_424);
lean_ctor_set(x_479, 1, x_425);
lean_ctor_set(x_479, 2, x_426);
lean_ctor_set(x_479, 3, x_427);
lean_ctor_set(x_479, 4, x_428);
lean_ctor_set(x_479, 5, x_429);
lean_ctor_set(x_479, 6, x_430);
lean_ctor_set(x_479, 7, x_431);
lean_ctor_set(x_479, 8, x_433);
lean_ctor_set(x_479, 9, x_434);
lean_ctor_set(x_479, 10, x_435);
lean_ctor_set(x_479, 11, x_436);
lean_ctor_set(x_479, 12, x_437);
lean_ctor_set(x_479, 13, x_438);
lean_ctor_set(x_479, 14, x_478);
lean_ctor_set(x_479, 15, x_439);
lean_ctor_set_uint8(x_479, sizeof(void*)*16, x_432);
x_480 = lean_st_ref_set(x_410, x_479, x_423);
x_481 = lean_ctor_get(x_480, 1);
lean_inc(x_481);
lean_dec(x_480);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_1);
x_482 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_410, x_411, x_412, x_413, x_414, x_415, x_416, x_417, x_481);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
lean_dec(x_482);
lean_inc(x_417);
lean_inc(x_416);
lean_inc(x_415);
lean_inc(x_414);
lean_inc(x_413);
lean_inc(x_412);
lean_inc(x_411);
lean_inc(x_410);
lean_inc(x_409);
lean_inc(x_1);
x_484 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_409, x_410, x_411, x_412, x_413, x_414, x_415, x_416, x_417, x_483);
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_484, 1);
lean_inc(x_485);
lean_dec(x_484);
x_486 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_410, x_411, x_412, x_413, x_414, x_415, x_416, x_417, x_485);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_487 = lean_ctor_get(x_486, 1);
lean_inc(x_487);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_488 = x_486;
} else {
 lean_dec_ref(x_486);
 x_488 = lean_box(0);
}
if (lean_is_scalar(x_488)) {
 x_489 = lean_alloc_ctor(0, 2, 0);
} else {
 x_489 = x_488;
}
lean_ctor_set(x_489, 0, x_409);
lean_ctor_set(x_489, 1, x_487);
return x_489;
}
else
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
lean_dec(x_409);
x_490 = lean_ctor_get(x_486, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_486, 1);
lean_inc(x_491);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_492 = x_486;
} else {
 lean_dec_ref(x_486);
 x_492 = lean_box(0);
}
if (lean_is_scalar(x_492)) {
 x_493 = lean_alloc_ctor(1, 2, 0);
} else {
 x_493 = x_492;
}
lean_ctor_set(x_493, 0, x_490);
lean_ctor_set(x_493, 1, x_491);
return x_493;
}
}
else
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_1);
x_494 = lean_ctor_get(x_484, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_484, 1);
lean_inc(x_495);
if (lean_is_exclusive(x_484)) {
 lean_ctor_release(x_484, 0);
 lean_ctor_release(x_484, 1);
 x_496 = x_484;
} else {
 lean_dec_ref(x_484);
 x_496 = lean_box(0);
}
if (lean_is_scalar(x_496)) {
 x_497 = lean_alloc_ctor(1, 2, 0);
} else {
 x_497 = x_496;
}
lean_ctor_set(x_497, 0, x_494);
lean_ctor_set(x_497, 1, x_495);
return x_497;
}
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec(x_1);
x_498 = lean_ctor_get(x_482, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_482, 1);
lean_inc(x_499);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 lean_ctor_release(x_482, 1);
 x_500 = x_482;
} else {
 lean_dec_ref(x_482);
 x_500 = lean_box(0);
}
if (lean_is_scalar(x_500)) {
 x_501 = lean_alloc_ctor(1, 2, 0);
} else {
 x_501 = x_500;
}
lean_ctor_set(x_501, 0, x_498);
lean_ctor_set(x_501, 1, x_499);
return x_501;
}
}
}
}
else
{
lean_object* x_516; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_516 = lean_ctor_get(x_16, 0);
lean_inc(x_516);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_516);
return x_11;
}
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_517 = lean_ctor_get(x_11, 0);
x_518 = lean_ctor_get(x_11, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_11);
x_519 = lean_ctor_get(x_517, 1);
lean_inc(x_519);
lean_dec(x_517);
lean_inc(x_1);
x_520 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_519, x_1);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; uint8_t x_625; 
x_521 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_518);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_524 = x_521;
} else {
 lean_dec_ref(x_521);
 x_524 = lean_box(0);
}
x_525 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_526 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_525, x_8, x_523);
x_527 = lean_ctor_get(x_522, 0);
lean_inc(x_527);
lean_dec(x_522);
x_528 = lean_ctor_get(x_526, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_526, 1);
lean_inc(x_529);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 x_530 = x_526;
} else {
 lean_dec_ref(x_526);
 x_530 = lean_box(0);
}
x_531 = lean_ctor_get(x_527, 2);
lean_inc(x_531);
lean_dec(x_527);
x_625 = lean_unbox(x_528);
lean_dec(x_528);
if (x_625 == 0)
{
lean_dec(x_530);
lean_dec(x_524);
x_532 = x_2;
x_533 = x_3;
x_534 = x_4;
x_535 = x_5;
x_536 = x_6;
x_537 = x_7;
x_538 = x_8;
x_539 = x_9;
x_540 = x_529;
goto block_624;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; 
x_626 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_627 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_530)) {
 x_628 = lean_alloc_ctor(7, 2, 0);
} else {
 x_628 = x_530;
 lean_ctor_set_tag(x_628, 7);
}
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
x_629 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
if (lean_is_scalar(x_524)) {
 x_630 = lean_alloc_ctor(7, 2, 0);
} else {
 x_630 = x_524;
 lean_ctor_set_tag(x_630, 7);
}
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
lean_inc(x_531);
x_631 = l_Nat_reprFast(x_531);
x_632 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_632, 0, x_631);
x_633 = l_Lean_MessageData_ofFormat(x_632);
x_634 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_634, 0, x_630);
lean_ctor_set(x_634, 1, x_633);
x_635 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_626);
x_636 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_525, x_635, x_6, x_7, x_8, x_9, x_529);
x_637 = lean_ctor_get(x_636, 1);
lean_inc(x_637);
lean_dec(x_636);
x_532 = x_2;
x_533 = x_3;
x_534 = x_4;
x_535 = x_5;
x_536 = x_6;
x_537 = x_7;
x_538 = x_8;
x_539 = x_9;
x_540 = x_637;
goto block_624;
}
block_624:
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_541 = lean_st_ref_take(x_532, x_540);
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_542, 14);
lean_inc(x_543);
x_544 = lean_ctor_get(x_543, 1);
lean_inc(x_544);
x_545 = lean_ctor_get(x_541, 1);
lean_inc(x_545);
lean_dec(x_541);
x_546 = lean_ctor_get(x_542, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_542, 1);
lean_inc(x_547);
x_548 = lean_ctor_get(x_542, 2);
lean_inc(x_548);
x_549 = lean_ctor_get(x_542, 3);
lean_inc(x_549);
x_550 = lean_ctor_get(x_542, 4);
lean_inc(x_550);
x_551 = lean_ctor_get(x_542, 5);
lean_inc(x_551);
x_552 = lean_ctor_get(x_542, 6);
lean_inc(x_552);
x_553 = lean_ctor_get(x_542, 7);
lean_inc(x_553);
x_554 = lean_ctor_get_uint8(x_542, sizeof(void*)*16);
x_555 = lean_ctor_get(x_542, 8);
lean_inc(x_555);
x_556 = lean_ctor_get(x_542, 9);
lean_inc(x_556);
x_557 = lean_ctor_get(x_542, 10);
lean_inc(x_557);
x_558 = lean_ctor_get(x_542, 11);
lean_inc(x_558);
x_559 = lean_ctor_get(x_542, 12);
lean_inc(x_559);
x_560 = lean_ctor_get(x_542, 13);
lean_inc(x_560);
x_561 = lean_ctor_get(x_542, 15);
lean_inc(x_561);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 lean_ctor_release(x_542, 2);
 lean_ctor_release(x_542, 3);
 lean_ctor_release(x_542, 4);
 lean_ctor_release(x_542, 5);
 lean_ctor_release(x_542, 6);
 lean_ctor_release(x_542, 7);
 lean_ctor_release(x_542, 8);
 lean_ctor_release(x_542, 9);
 lean_ctor_release(x_542, 10);
 lean_ctor_release(x_542, 11);
 lean_ctor_release(x_542, 12);
 lean_ctor_release(x_542, 13);
 lean_ctor_release(x_542, 14);
 lean_ctor_release(x_542, 15);
 x_562 = x_542;
} else {
 lean_dec_ref(x_542);
 x_562 = lean_box(0);
}
x_563 = lean_ctor_get(x_543, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_543, 2);
lean_inc(x_564);
x_565 = lean_ctor_get(x_543, 3);
lean_inc(x_565);
if (lean_is_exclusive(x_543)) {
 lean_ctor_release(x_543, 0);
 lean_ctor_release(x_543, 1);
 lean_ctor_release(x_543, 2);
 lean_ctor_release(x_543, 3);
 x_566 = x_543;
} else {
 lean_dec_ref(x_543);
 x_566 = lean_box(0);
}
x_567 = lean_ctor_get(x_544, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_544, 1);
lean_inc(x_568);
x_569 = lean_ctor_get(x_544, 2);
lean_inc(x_569);
x_570 = lean_ctor_get(x_544, 3);
lean_inc(x_570);
x_571 = lean_ctor_get(x_544, 4);
lean_inc(x_571);
x_572 = lean_ctor_get(x_544, 5);
lean_inc(x_572);
x_573 = lean_ctor_get(x_544, 6);
lean_inc(x_573);
x_574 = lean_ctor_get(x_544, 7);
lean_inc(x_574);
x_575 = lean_ctor_get(x_544, 8);
lean_inc(x_575);
x_576 = lean_ctor_get(x_544, 9);
lean_inc(x_576);
x_577 = lean_ctor_get(x_544, 10);
lean_inc(x_577);
x_578 = lean_ctor_get(x_544, 11);
lean_inc(x_578);
x_579 = lean_ctor_get(x_544, 12);
lean_inc(x_579);
x_580 = lean_ctor_get(x_544, 13);
lean_inc(x_580);
x_581 = lean_ctor_get_uint8(x_544, sizeof(void*)*17);
x_582 = lean_ctor_get(x_544, 14);
lean_inc(x_582);
x_583 = lean_ctor_get(x_544, 15);
lean_inc(x_583);
x_584 = lean_ctor_get(x_544, 16);
lean_inc(x_584);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 lean_ctor_release(x_544, 2);
 lean_ctor_release(x_544, 3);
 lean_ctor_release(x_544, 4);
 lean_ctor_release(x_544, 5);
 lean_ctor_release(x_544, 6);
 lean_ctor_release(x_544, 7);
 lean_ctor_release(x_544, 8);
 lean_ctor_release(x_544, 9);
 lean_ctor_release(x_544, 10);
 lean_ctor_release(x_544, 11);
 lean_ctor_release(x_544, 12);
 lean_ctor_release(x_544, 13);
 lean_ctor_release(x_544, 14);
 lean_ctor_release(x_544, 15);
 lean_ctor_release(x_544, 16);
 x_585 = x_544;
} else {
 lean_dec_ref(x_544);
 x_585 = lean_box(0);
}
lean_inc(x_1);
x_586 = l_Lean_PersistentArray_push___redArg(x_567, x_1);
lean_inc(x_531);
lean_inc(x_1);
x_587 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_568, x_1, x_531);
x_588 = lean_box(0);
x_589 = l_Lean_PersistentArray_push___redArg(x_572, x_588);
x_590 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_591 = l_Lean_PersistentArray_push___redArg(x_573, x_590);
x_592 = l_Lean_PersistentArray_push___redArg(x_574, x_590);
x_593 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_594 = l_Lean_PersistentArray_push___redArg(x_575, x_593);
x_595 = lean_box(0);
x_596 = l_Lean_PersistentArray_push___redArg(x_576, x_595);
x_597 = lean_box(0);
x_598 = l_Lean_PersistentArray_push___redArg(x_578, x_597);
if (lean_is_scalar(x_585)) {
 x_599 = lean_alloc_ctor(0, 17, 1);
} else {
 x_599 = x_585;
}
lean_ctor_set(x_599, 0, x_586);
lean_ctor_set(x_599, 1, x_587);
lean_ctor_set(x_599, 2, x_569);
lean_ctor_set(x_599, 3, x_570);
lean_ctor_set(x_599, 4, x_571);
lean_ctor_set(x_599, 5, x_589);
lean_ctor_set(x_599, 6, x_591);
lean_ctor_set(x_599, 7, x_592);
lean_ctor_set(x_599, 8, x_594);
lean_ctor_set(x_599, 9, x_596);
lean_ctor_set(x_599, 10, x_577);
lean_ctor_set(x_599, 11, x_598);
lean_ctor_set(x_599, 12, x_579);
lean_ctor_set(x_599, 13, x_580);
lean_ctor_set(x_599, 14, x_582);
lean_ctor_set(x_599, 15, x_583);
lean_ctor_set(x_599, 16, x_584);
lean_ctor_set_uint8(x_599, sizeof(void*)*17, x_581);
if (lean_is_scalar(x_566)) {
 x_600 = lean_alloc_ctor(0, 4, 0);
} else {
 x_600 = x_566;
}
lean_ctor_set(x_600, 0, x_563);
lean_ctor_set(x_600, 1, x_599);
lean_ctor_set(x_600, 2, x_564);
lean_ctor_set(x_600, 3, x_565);
if (lean_is_scalar(x_562)) {
 x_601 = lean_alloc_ctor(0, 16, 1);
} else {
 x_601 = x_562;
}
lean_ctor_set(x_601, 0, x_546);
lean_ctor_set(x_601, 1, x_547);
lean_ctor_set(x_601, 2, x_548);
lean_ctor_set(x_601, 3, x_549);
lean_ctor_set(x_601, 4, x_550);
lean_ctor_set(x_601, 5, x_551);
lean_ctor_set(x_601, 6, x_552);
lean_ctor_set(x_601, 7, x_553);
lean_ctor_set(x_601, 8, x_555);
lean_ctor_set(x_601, 9, x_556);
lean_ctor_set(x_601, 10, x_557);
lean_ctor_set(x_601, 11, x_558);
lean_ctor_set(x_601, 12, x_559);
lean_ctor_set(x_601, 13, x_560);
lean_ctor_set(x_601, 14, x_600);
lean_ctor_set(x_601, 15, x_561);
lean_ctor_set_uint8(x_601, sizeof(void*)*16, x_554);
x_602 = lean_st_ref_set(x_532, x_601, x_545);
x_603 = lean_ctor_get(x_602, 1);
lean_inc(x_603);
lean_dec(x_602);
lean_inc(x_539);
lean_inc(x_538);
lean_inc(x_537);
lean_inc(x_536);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_532);
lean_inc(x_1);
x_604 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_532, x_533, x_534, x_535, x_536, x_537, x_538, x_539, x_603);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_604, 1);
lean_inc(x_605);
lean_dec(x_604);
lean_inc(x_539);
lean_inc(x_538);
lean_inc(x_537);
lean_inc(x_536);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_532);
lean_inc(x_531);
lean_inc(x_1);
x_606 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_531, x_532, x_533, x_534, x_535, x_536, x_537, x_538, x_539, x_605);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; 
x_607 = lean_ctor_get(x_606, 1);
lean_inc(x_607);
lean_dec(x_606);
x_608 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_532, x_533, x_534, x_535, x_536, x_537, x_538, x_539, x_607);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_ctor_get(x_608, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_610 = x_608;
} else {
 lean_dec_ref(x_608);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(0, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_531);
lean_ctor_set(x_611, 1, x_609);
return x_611;
}
else
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; 
lean_dec(x_531);
x_612 = lean_ctor_get(x_608, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_608, 1);
lean_inc(x_613);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 x_614 = x_608;
} else {
 lean_dec_ref(x_608);
 x_614 = lean_box(0);
}
if (lean_is_scalar(x_614)) {
 x_615 = lean_alloc_ctor(1, 2, 0);
} else {
 x_615 = x_614;
}
lean_ctor_set(x_615, 0, x_612);
lean_ctor_set(x_615, 1, x_613);
return x_615;
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_535);
lean_dec(x_534);
lean_dec(x_533);
lean_dec(x_532);
lean_dec(x_531);
lean_dec(x_1);
x_616 = lean_ctor_get(x_606, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_606, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_606)) {
 lean_ctor_release(x_606, 0);
 lean_ctor_release(x_606, 1);
 x_618 = x_606;
} else {
 lean_dec_ref(x_606);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(1, 2, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_616);
lean_ctor_set(x_619, 1, x_617);
return x_619;
}
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_535);
lean_dec(x_534);
lean_dec(x_533);
lean_dec(x_532);
lean_dec(x_531);
lean_dec(x_1);
x_620 = lean_ctor_get(x_604, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_604, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 lean_ctor_release(x_604, 1);
 x_622 = x_604;
} else {
 lean_dec_ref(x_604);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_623 = x_622;
}
lean_ctor_set(x_623, 0, x_620);
lean_ctor_set(x_623, 1, x_621);
return x_623;
}
}
}
else
{
lean_object* x_638; lean_object* x_639; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_638 = lean_ctor_get(x_520, 0);
lean_inc(x_638);
lean_dec(x_520);
x_639 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_639, 1, x_518);
return x_639;
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
