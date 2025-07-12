// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
// Imports: Lean.Meta.IntInstTesters Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_324; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_324 = lean_unbox(x_25);
lean_dec(x_25);
if (x_324 == 0)
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
goto block_323;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_325 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_326 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_326);
lean_ctor_set(x_22, 0, x_325);
x_327 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_327);
lean_ctor_set(x_17, 0, x_22);
lean_inc(x_27);
x_328 = l_Nat_reprFast(x_27);
x_329 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_329, 0, x_328);
x_330 = l_Lean_MessageData_ofFormat(x_329);
x_331 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_331, 0, x_17);
lean_ctor_set(x_331, 1, x_330);
x_332 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_325);
x_333 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_332, x_6, x_7, x_8, x_9, x_26);
x_334 = lean_ctor_get(x_333, 1);
lean_inc(x_334);
lean_dec(x_333);
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_334;
goto block_323;
}
block_323:
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
x_49 = lean_ctor_get(x_40, 7);
x_50 = lean_ctor_get(x_40, 8);
x_51 = lean_ctor_get(x_40, 9);
x_52 = lean_ctor_get(x_40, 10);
x_53 = lean_ctor_get(x_40, 11);
x_54 = lean_ctor_get(x_40, 13);
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
lean_ctor_set(x_40, 13, x_67);
lean_ctor_set(x_40, 11, x_65);
lean_ctor_set(x_40, 10, x_63);
lean_ctor_set(x_40, 9, x_61);
lean_ctor_set(x_40, 8, x_60);
lean_ctor_set(x_40, 7, x_58);
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
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_74 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
lean_inc(x_27);
x_76 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_75);
if (lean_obj_tag(x_76) == 0)
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_76, 0);
lean_dec(x_78);
lean_ctor_set(x_76, 0, x_27);
return x_76;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_27);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
uint8_t x_81; 
lean_dec(x_27);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
return x_76;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_76, 0);
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_76);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
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
x_85 = !lean_is_exclusive(x_74);
if (x_85 == 0)
{
return x_74;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_74, 0);
x_87 = lean_ctor_get(x_74, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_74);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
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
x_89 = !lean_is_exclusive(x_72);
if (x_89 == 0)
{
return x_72;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_72, 0);
x_91 = lean_ctor_get(x_72, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_72);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
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
x_93 = !lean_is_exclusive(x_70);
if (x_93 == 0)
{
return x_70;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_70, 0);
x_95 = lean_ctor_get(x_70, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_70);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_97 = lean_ctor_get(x_40, 0);
x_98 = lean_ctor_get(x_40, 1);
x_99 = lean_ctor_get(x_40, 2);
x_100 = lean_ctor_get(x_40, 3);
x_101 = lean_ctor_get(x_40, 4);
x_102 = lean_ctor_get(x_40, 5);
x_103 = lean_ctor_get(x_40, 6);
x_104 = lean_ctor_get(x_40, 7);
x_105 = lean_ctor_get(x_40, 8);
x_106 = lean_ctor_get(x_40, 9);
x_107 = lean_ctor_get(x_40, 10);
x_108 = lean_ctor_get(x_40, 11);
x_109 = lean_ctor_get(x_40, 12);
x_110 = lean_ctor_get(x_40, 13);
x_111 = lean_ctor_get(x_40, 14);
x_112 = lean_ctor_get(x_40, 15);
x_113 = lean_ctor_get_uint8(x_40, sizeof(void*)*22);
x_114 = lean_ctor_get(x_40, 16);
x_115 = lean_ctor_get(x_40, 17);
x_116 = lean_ctor_get(x_40, 18);
x_117 = lean_ctor_get(x_40, 19);
x_118 = lean_ctor_get(x_40, 20);
x_119 = lean_ctor_get(x_40, 21);
x_120 = lean_ctor_get_uint8(x_40, sizeof(void*)*22 + 1);
lean_inc(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_116);
lean_inc(x_115);
lean_inc(x_114);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_40);
lean_inc(x_1);
x_121 = l_Lean_PersistentArray_push___redArg(x_97, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_122 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_98, x_1, x_27);
x_123 = lean_box(0);
x_124 = l_Lean_PersistentArray_push___redArg(x_104, x_123);
x_125 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_126 = l_Lean_PersistentArray_push___redArg(x_105, x_125);
x_127 = l_Lean_PersistentArray_push___redArg(x_106, x_125);
x_128 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_129 = l_Lean_PersistentArray_push___redArg(x_107, x_128);
x_130 = lean_box(0);
x_131 = l_Lean_PersistentArray_push___redArg(x_108, x_130);
x_132 = lean_box(0);
x_133 = l_Lean_PersistentArray_push___redArg(x_110, x_132);
x_134 = lean_alloc_ctor(0, 22, 2);
lean_ctor_set(x_134, 0, x_121);
lean_ctor_set(x_134, 1, x_122);
lean_ctor_set(x_134, 2, x_99);
lean_ctor_set(x_134, 3, x_100);
lean_ctor_set(x_134, 4, x_101);
lean_ctor_set(x_134, 5, x_102);
lean_ctor_set(x_134, 6, x_103);
lean_ctor_set(x_134, 7, x_124);
lean_ctor_set(x_134, 8, x_126);
lean_ctor_set(x_134, 9, x_127);
lean_ctor_set(x_134, 10, x_129);
lean_ctor_set(x_134, 11, x_131);
lean_ctor_set(x_134, 12, x_109);
lean_ctor_set(x_134, 13, x_133);
lean_ctor_set(x_134, 14, x_111);
lean_ctor_set(x_134, 15, x_112);
lean_ctor_set(x_134, 16, x_114);
lean_ctor_set(x_134, 17, x_115);
lean_ctor_set(x_134, 18, x_116);
lean_ctor_set(x_134, 19, x_117);
lean_ctor_set(x_134, 20, x_118);
lean_ctor_set(x_134, 21, x_119);
lean_ctor_set_uint8(x_134, sizeof(void*)*22, x_113);
lean_ctor_set_uint8(x_134, sizeof(void*)*22 + 1, x_120);
lean_ctor_set(x_39, 1, x_134);
x_135 = lean_st_ref_set(x_28, x_38, x_41);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_137 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
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
x_139 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_141 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
lean_inc(x_27);
x_143 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_27);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_27);
x_147 = lean_ctor_get(x_143, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_149 = x_143;
} else {
 lean_dec_ref(x_143);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
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
x_151 = lean_ctor_get(x_141, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_141, 1);
lean_inc(x_152);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_153 = x_141;
} else {
 lean_dec_ref(x_141);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 2, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
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
x_155 = lean_ctor_get(x_139, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_139, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_157 = x_139;
} else {
 lean_dec_ref(x_139);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
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
x_159 = lean_ctor_get(x_137, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_137, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_161 = x_137;
} else {
 lean_dec_ref(x_137);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_163 = lean_ctor_get(x_39, 0);
x_164 = lean_ctor_get(x_39, 2);
x_165 = lean_ctor_get(x_39, 3);
lean_inc(x_165);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_39);
x_166 = lean_ctor_get(x_40, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_40, 1);
lean_inc(x_167);
x_168 = lean_ctor_get(x_40, 2);
lean_inc(x_168);
x_169 = lean_ctor_get(x_40, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_40, 4);
lean_inc(x_170);
x_171 = lean_ctor_get(x_40, 5);
lean_inc(x_171);
x_172 = lean_ctor_get(x_40, 6);
lean_inc(x_172);
x_173 = lean_ctor_get(x_40, 7);
lean_inc(x_173);
x_174 = lean_ctor_get(x_40, 8);
lean_inc(x_174);
x_175 = lean_ctor_get(x_40, 9);
lean_inc(x_175);
x_176 = lean_ctor_get(x_40, 10);
lean_inc(x_176);
x_177 = lean_ctor_get(x_40, 11);
lean_inc(x_177);
x_178 = lean_ctor_get(x_40, 12);
lean_inc(x_178);
x_179 = lean_ctor_get(x_40, 13);
lean_inc(x_179);
x_180 = lean_ctor_get(x_40, 14);
lean_inc(x_180);
x_181 = lean_ctor_get(x_40, 15);
lean_inc(x_181);
x_182 = lean_ctor_get_uint8(x_40, sizeof(void*)*22);
x_183 = lean_ctor_get(x_40, 16);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 17);
lean_inc(x_184);
x_185 = lean_ctor_get(x_40, 18);
lean_inc(x_185);
x_186 = lean_ctor_get(x_40, 19);
lean_inc(x_186);
x_187 = lean_ctor_get(x_40, 20);
lean_inc(x_187);
x_188 = lean_ctor_get(x_40, 21);
lean_inc(x_188);
x_189 = lean_ctor_get_uint8(x_40, sizeof(void*)*22 + 1);
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
 lean_ctor_release(x_40, 18);
 lean_ctor_release(x_40, 19);
 lean_ctor_release(x_40, 20);
 lean_ctor_release(x_40, 21);
 x_190 = x_40;
} else {
 lean_dec_ref(x_40);
 x_190 = lean_box(0);
}
lean_inc(x_1);
x_191 = l_Lean_PersistentArray_push___redArg(x_166, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_192 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_167, x_1, x_27);
x_193 = lean_box(0);
x_194 = l_Lean_PersistentArray_push___redArg(x_173, x_193);
x_195 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_196 = l_Lean_PersistentArray_push___redArg(x_174, x_195);
x_197 = l_Lean_PersistentArray_push___redArg(x_175, x_195);
x_198 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_199 = l_Lean_PersistentArray_push___redArg(x_176, x_198);
x_200 = lean_box(0);
x_201 = l_Lean_PersistentArray_push___redArg(x_177, x_200);
x_202 = lean_box(0);
x_203 = l_Lean_PersistentArray_push___redArg(x_179, x_202);
if (lean_is_scalar(x_190)) {
 x_204 = lean_alloc_ctor(0, 22, 2);
} else {
 x_204 = x_190;
}
lean_ctor_set(x_204, 0, x_191);
lean_ctor_set(x_204, 1, x_192);
lean_ctor_set(x_204, 2, x_168);
lean_ctor_set(x_204, 3, x_169);
lean_ctor_set(x_204, 4, x_170);
lean_ctor_set(x_204, 5, x_171);
lean_ctor_set(x_204, 6, x_172);
lean_ctor_set(x_204, 7, x_194);
lean_ctor_set(x_204, 8, x_196);
lean_ctor_set(x_204, 9, x_197);
lean_ctor_set(x_204, 10, x_199);
lean_ctor_set(x_204, 11, x_201);
lean_ctor_set(x_204, 12, x_178);
lean_ctor_set(x_204, 13, x_203);
lean_ctor_set(x_204, 14, x_180);
lean_ctor_set(x_204, 15, x_181);
lean_ctor_set(x_204, 16, x_183);
lean_ctor_set(x_204, 17, x_184);
lean_ctor_set(x_204, 18, x_185);
lean_ctor_set(x_204, 19, x_186);
lean_ctor_set(x_204, 20, x_187);
lean_ctor_set(x_204, 21, x_188);
lean_ctor_set_uint8(x_204, sizeof(void*)*22, x_182);
lean_ctor_set_uint8(x_204, sizeof(void*)*22 + 1, x_189);
x_205 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_205, 0, x_163);
lean_ctor_set(x_205, 1, x_204);
lean_ctor_set(x_205, 2, x_164);
lean_ctor_set(x_205, 3, x_165);
lean_ctor_set(x_38, 14, x_205);
x_206 = lean_st_ref_set(x_28, x_38, x_41);
x_207 = lean_ctor_get(x_206, 1);
lean_inc(x_207);
lean_dec(x_206);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_208 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
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
x_210 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_209);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
lean_dec(x_210);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_212 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
lean_inc(x_27);
x_214 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_216 = x_214;
} else {
 lean_dec_ref(x_214);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_27);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_27);
x_218 = lean_ctor_get(x_214, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_220 = x_214;
} else {
 lean_dec_ref(x_214);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
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
x_222 = lean_ctor_get(x_212, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_212, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_224 = x_212;
} else {
 lean_dec_ref(x_212);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
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
x_226 = lean_ctor_get(x_210, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_210, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_228 = x_210;
} else {
 lean_dec_ref(x_210);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
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
x_230 = lean_ctor_get(x_208, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_208, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_232 = x_208;
} else {
 lean_dec_ref(x_208);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_234 = lean_ctor_get(x_38, 0);
x_235 = lean_ctor_get(x_38, 1);
x_236 = lean_ctor_get(x_38, 2);
x_237 = lean_ctor_get(x_38, 3);
x_238 = lean_ctor_get(x_38, 4);
x_239 = lean_ctor_get(x_38, 5);
x_240 = lean_ctor_get(x_38, 6);
x_241 = lean_ctor_get(x_38, 7);
x_242 = lean_ctor_get_uint8(x_38, sizeof(void*)*16);
x_243 = lean_ctor_get(x_38, 8);
x_244 = lean_ctor_get(x_38, 9);
x_245 = lean_ctor_get(x_38, 10);
x_246 = lean_ctor_get(x_38, 11);
x_247 = lean_ctor_get(x_38, 12);
x_248 = lean_ctor_get(x_38, 13);
x_249 = lean_ctor_get(x_38, 15);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_38);
x_250 = lean_ctor_get(x_39, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_39, 2);
lean_inc(x_251);
x_252 = lean_ctor_get(x_39, 3);
lean_inc(x_252);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 x_253 = x_39;
} else {
 lean_dec_ref(x_39);
 x_253 = lean_box(0);
}
x_254 = lean_ctor_get(x_40, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_40, 1);
lean_inc(x_255);
x_256 = lean_ctor_get(x_40, 2);
lean_inc(x_256);
x_257 = lean_ctor_get(x_40, 3);
lean_inc(x_257);
x_258 = lean_ctor_get(x_40, 4);
lean_inc(x_258);
x_259 = lean_ctor_get(x_40, 5);
lean_inc(x_259);
x_260 = lean_ctor_get(x_40, 6);
lean_inc(x_260);
x_261 = lean_ctor_get(x_40, 7);
lean_inc(x_261);
x_262 = lean_ctor_get(x_40, 8);
lean_inc(x_262);
x_263 = lean_ctor_get(x_40, 9);
lean_inc(x_263);
x_264 = lean_ctor_get(x_40, 10);
lean_inc(x_264);
x_265 = lean_ctor_get(x_40, 11);
lean_inc(x_265);
x_266 = lean_ctor_get(x_40, 12);
lean_inc(x_266);
x_267 = lean_ctor_get(x_40, 13);
lean_inc(x_267);
x_268 = lean_ctor_get(x_40, 14);
lean_inc(x_268);
x_269 = lean_ctor_get(x_40, 15);
lean_inc(x_269);
x_270 = lean_ctor_get_uint8(x_40, sizeof(void*)*22);
x_271 = lean_ctor_get(x_40, 16);
lean_inc(x_271);
x_272 = lean_ctor_get(x_40, 17);
lean_inc(x_272);
x_273 = lean_ctor_get(x_40, 18);
lean_inc(x_273);
x_274 = lean_ctor_get(x_40, 19);
lean_inc(x_274);
x_275 = lean_ctor_get(x_40, 20);
lean_inc(x_275);
x_276 = lean_ctor_get(x_40, 21);
lean_inc(x_276);
x_277 = lean_ctor_get_uint8(x_40, sizeof(void*)*22 + 1);
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
 lean_ctor_release(x_40, 18);
 lean_ctor_release(x_40, 19);
 lean_ctor_release(x_40, 20);
 lean_ctor_release(x_40, 21);
 x_278 = x_40;
} else {
 lean_dec_ref(x_40);
 x_278 = lean_box(0);
}
lean_inc(x_1);
x_279 = l_Lean_PersistentArray_push___redArg(x_254, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_280 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_255, x_1, x_27);
x_281 = lean_box(0);
x_282 = l_Lean_PersistentArray_push___redArg(x_261, x_281);
x_283 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_284 = l_Lean_PersistentArray_push___redArg(x_262, x_283);
x_285 = l_Lean_PersistentArray_push___redArg(x_263, x_283);
x_286 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_287 = l_Lean_PersistentArray_push___redArg(x_264, x_286);
x_288 = lean_box(0);
x_289 = l_Lean_PersistentArray_push___redArg(x_265, x_288);
x_290 = lean_box(0);
x_291 = l_Lean_PersistentArray_push___redArg(x_267, x_290);
if (lean_is_scalar(x_278)) {
 x_292 = lean_alloc_ctor(0, 22, 2);
} else {
 x_292 = x_278;
}
lean_ctor_set(x_292, 0, x_279);
lean_ctor_set(x_292, 1, x_280);
lean_ctor_set(x_292, 2, x_256);
lean_ctor_set(x_292, 3, x_257);
lean_ctor_set(x_292, 4, x_258);
lean_ctor_set(x_292, 5, x_259);
lean_ctor_set(x_292, 6, x_260);
lean_ctor_set(x_292, 7, x_282);
lean_ctor_set(x_292, 8, x_284);
lean_ctor_set(x_292, 9, x_285);
lean_ctor_set(x_292, 10, x_287);
lean_ctor_set(x_292, 11, x_289);
lean_ctor_set(x_292, 12, x_266);
lean_ctor_set(x_292, 13, x_291);
lean_ctor_set(x_292, 14, x_268);
lean_ctor_set(x_292, 15, x_269);
lean_ctor_set(x_292, 16, x_271);
lean_ctor_set(x_292, 17, x_272);
lean_ctor_set(x_292, 18, x_273);
lean_ctor_set(x_292, 19, x_274);
lean_ctor_set(x_292, 20, x_275);
lean_ctor_set(x_292, 21, x_276);
lean_ctor_set_uint8(x_292, sizeof(void*)*22, x_270);
lean_ctor_set_uint8(x_292, sizeof(void*)*22 + 1, x_277);
if (lean_is_scalar(x_253)) {
 x_293 = lean_alloc_ctor(0, 4, 0);
} else {
 x_293 = x_253;
}
lean_ctor_set(x_293, 0, x_250);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_293, 2, x_251);
lean_ctor_set(x_293, 3, x_252);
x_294 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_294, 0, x_234);
lean_ctor_set(x_294, 1, x_235);
lean_ctor_set(x_294, 2, x_236);
lean_ctor_set(x_294, 3, x_237);
lean_ctor_set(x_294, 4, x_238);
lean_ctor_set(x_294, 5, x_239);
lean_ctor_set(x_294, 6, x_240);
lean_ctor_set(x_294, 7, x_241);
lean_ctor_set(x_294, 8, x_243);
lean_ctor_set(x_294, 9, x_244);
lean_ctor_set(x_294, 10, x_245);
lean_ctor_set(x_294, 11, x_246);
lean_ctor_set(x_294, 12, x_247);
lean_ctor_set(x_294, 13, x_248);
lean_ctor_set(x_294, 14, x_293);
lean_ctor_set(x_294, 15, x_249);
lean_ctor_set_uint8(x_294, sizeof(void*)*16, x_242);
x_295 = lean_st_ref_set(x_28, x_294, x_41);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_297 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_296);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
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
x_299 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_298);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_299, 1);
lean_inc(x_300);
lean_dec(x_299);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_301 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_300);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec(x_301);
lean_inc(x_27);
x_303 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_302);
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_304 = lean_ctor_get(x_303, 1);
lean_inc(x_304);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_305 = x_303;
} else {
 lean_dec_ref(x_303);
 x_305 = lean_box(0);
}
if (lean_is_scalar(x_305)) {
 x_306 = lean_alloc_ctor(0, 2, 0);
} else {
 x_306 = x_305;
}
lean_ctor_set(x_306, 0, x_27);
lean_ctor_set(x_306, 1, x_304);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_27);
x_307 = lean_ctor_get(x_303, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_303, 1);
lean_inc(x_308);
if (lean_is_exclusive(x_303)) {
 lean_ctor_release(x_303, 0);
 lean_ctor_release(x_303, 1);
 x_309 = x_303;
} else {
 lean_dec_ref(x_303);
 x_309 = lean_box(0);
}
if (lean_is_scalar(x_309)) {
 x_310 = lean_alloc_ctor(1, 2, 0);
} else {
 x_310 = x_309;
}
lean_ctor_set(x_310, 0, x_307);
lean_ctor_set(x_310, 1, x_308);
return x_310;
}
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
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
x_311 = lean_ctor_get(x_301, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_301, 1);
lean_inc(x_312);
if (lean_is_exclusive(x_301)) {
 lean_ctor_release(x_301, 0);
 lean_ctor_release(x_301, 1);
 x_313 = x_301;
} else {
 lean_dec_ref(x_301);
 x_313 = lean_box(0);
}
if (lean_is_scalar(x_313)) {
 x_314 = lean_alloc_ctor(1, 2, 0);
} else {
 x_314 = x_313;
}
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_312);
return x_314;
}
}
else
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
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
x_315 = lean_ctor_get(x_299, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_299, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_317 = x_299;
} else {
 lean_dec_ref(x_299);
 x_317 = lean_box(0);
}
if (lean_is_scalar(x_317)) {
 x_318 = lean_alloc_ctor(1, 2, 0);
} else {
 x_318 = x_317;
}
lean_ctor_set(x_318, 0, x_315);
lean_ctor_set(x_318, 1, x_316);
return x_318;
}
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
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
x_319 = lean_ctor_get(x_297, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_297, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_321 = x_297;
} else {
 lean_dec_ref(x_297);
 x_321 = lean_box(0);
}
if (lean_is_scalar(x_321)) {
 x_322 = lean_alloc_ctor(1, 2, 0);
} else {
 x_322 = x_321;
}
lean_ctor_set(x_322, 0, x_319);
lean_ctor_set(x_322, 1, x_320);
return x_322;
}
}
}
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; uint8_t x_443; 
x_335 = lean_ctor_get(x_22, 0);
x_336 = lean_ctor_get(x_22, 1);
lean_inc(x_336);
lean_inc(x_335);
lean_dec(x_22);
x_337 = lean_ctor_get(x_23, 2);
lean_inc(x_337);
lean_dec(x_23);
x_443 = lean_unbox(x_335);
lean_dec(x_335);
if (x_443 == 0)
{
lean_free_object(x_17);
x_338 = x_2;
x_339 = x_3;
x_340 = x_4;
x_341 = x_5;
x_342 = x_6;
x_343 = x_7;
x_344 = x_8;
x_345 = x_9;
x_346 = x_336;
goto block_442;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_444 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_445 = l_Lean_MessageData_ofExpr(x_1);
x_446 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
x_447 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_447);
lean_ctor_set(x_17, 0, x_446);
lean_inc(x_337);
x_448 = l_Nat_reprFast(x_337);
x_449 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_449, 0, x_448);
x_450 = l_Lean_MessageData_ofFormat(x_449);
x_451 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_451, 0, x_17);
lean_ctor_set(x_451, 1, x_450);
x_452 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_444);
x_453 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_452, x_6, x_7, x_8, x_9, x_336);
x_454 = lean_ctor_get(x_453, 1);
lean_inc(x_454);
lean_dec(x_453);
x_338 = x_2;
x_339 = x_3;
x_340 = x_4;
x_341 = x_5;
x_342 = x_6;
x_343 = x_7;
x_344 = x_8;
x_345 = x_9;
x_346 = x_454;
goto block_442;
}
block_442:
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint8_t x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_347 = lean_st_ref_take(x_338, x_346);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_348, 14);
lean_inc(x_349);
x_350 = lean_ctor_get(x_349, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
lean_dec(x_347);
x_352 = lean_ctor_get(x_348, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_348, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_348, 2);
lean_inc(x_354);
x_355 = lean_ctor_get(x_348, 3);
lean_inc(x_355);
x_356 = lean_ctor_get(x_348, 4);
lean_inc(x_356);
x_357 = lean_ctor_get(x_348, 5);
lean_inc(x_357);
x_358 = lean_ctor_get(x_348, 6);
lean_inc(x_358);
x_359 = lean_ctor_get(x_348, 7);
lean_inc(x_359);
x_360 = lean_ctor_get_uint8(x_348, sizeof(void*)*16);
x_361 = lean_ctor_get(x_348, 8);
lean_inc(x_361);
x_362 = lean_ctor_get(x_348, 9);
lean_inc(x_362);
x_363 = lean_ctor_get(x_348, 10);
lean_inc(x_363);
x_364 = lean_ctor_get(x_348, 11);
lean_inc(x_364);
x_365 = lean_ctor_get(x_348, 12);
lean_inc(x_365);
x_366 = lean_ctor_get(x_348, 13);
lean_inc(x_366);
x_367 = lean_ctor_get(x_348, 15);
lean_inc(x_367);
if (lean_is_exclusive(x_348)) {
 lean_ctor_release(x_348, 0);
 lean_ctor_release(x_348, 1);
 lean_ctor_release(x_348, 2);
 lean_ctor_release(x_348, 3);
 lean_ctor_release(x_348, 4);
 lean_ctor_release(x_348, 5);
 lean_ctor_release(x_348, 6);
 lean_ctor_release(x_348, 7);
 lean_ctor_release(x_348, 8);
 lean_ctor_release(x_348, 9);
 lean_ctor_release(x_348, 10);
 lean_ctor_release(x_348, 11);
 lean_ctor_release(x_348, 12);
 lean_ctor_release(x_348, 13);
 lean_ctor_release(x_348, 14);
 lean_ctor_release(x_348, 15);
 x_368 = x_348;
} else {
 lean_dec_ref(x_348);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_349, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_349, 2);
lean_inc(x_370);
x_371 = lean_ctor_get(x_349, 3);
lean_inc(x_371);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 x_372 = x_349;
} else {
 lean_dec_ref(x_349);
 x_372 = lean_box(0);
}
x_373 = lean_ctor_get(x_350, 0);
lean_inc(x_373);
x_374 = lean_ctor_get(x_350, 1);
lean_inc(x_374);
x_375 = lean_ctor_get(x_350, 2);
lean_inc(x_375);
x_376 = lean_ctor_get(x_350, 3);
lean_inc(x_376);
x_377 = lean_ctor_get(x_350, 4);
lean_inc(x_377);
x_378 = lean_ctor_get(x_350, 5);
lean_inc(x_378);
x_379 = lean_ctor_get(x_350, 6);
lean_inc(x_379);
x_380 = lean_ctor_get(x_350, 7);
lean_inc(x_380);
x_381 = lean_ctor_get(x_350, 8);
lean_inc(x_381);
x_382 = lean_ctor_get(x_350, 9);
lean_inc(x_382);
x_383 = lean_ctor_get(x_350, 10);
lean_inc(x_383);
x_384 = lean_ctor_get(x_350, 11);
lean_inc(x_384);
x_385 = lean_ctor_get(x_350, 12);
lean_inc(x_385);
x_386 = lean_ctor_get(x_350, 13);
lean_inc(x_386);
x_387 = lean_ctor_get(x_350, 14);
lean_inc(x_387);
x_388 = lean_ctor_get(x_350, 15);
lean_inc(x_388);
x_389 = lean_ctor_get_uint8(x_350, sizeof(void*)*22);
x_390 = lean_ctor_get(x_350, 16);
lean_inc(x_390);
x_391 = lean_ctor_get(x_350, 17);
lean_inc(x_391);
x_392 = lean_ctor_get(x_350, 18);
lean_inc(x_392);
x_393 = lean_ctor_get(x_350, 19);
lean_inc(x_393);
x_394 = lean_ctor_get(x_350, 20);
lean_inc(x_394);
x_395 = lean_ctor_get(x_350, 21);
lean_inc(x_395);
x_396 = lean_ctor_get_uint8(x_350, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 lean_ctor_release(x_350, 3);
 lean_ctor_release(x_350, 4);
 lean_ctor_release(x_350, 5);
 lean_ctor_release(x_350, 6);
 lean_ctor_release(x_350, 7);
 lean_ctor_release(x_350, 8);
 lean_ctor_release(x_350, 9);
 lean_ctor_release(x_350, 10);
 lean_ctor_release(x_350, 11);
 lean_ctor_release(x_350, 12);
 lean_ctor_release(x_350, 13);
 lean_ctor_release(x_350, 14);
 lean_ctor_release(x_350, 15);
 lean_ctor_release(x_350, 16);
 lean_ctor_release(x_350, 17);
 lean_ctor_release(x_350, 18);
 lean_ctor_release(x_350, 19);
 lean_ctor_release(x_350, 20);
 lean_ctor_release(x_350, 21);
 x_397 = x_350;
} else {
 lean_dec_ref(x_350);
 x_397 = lean_box(0);
}
lean_inc(x_1);
x_398 = l_Lean_PersistentArray_push___redArg(x_373, x_1);
lean_inc(x_337);
lean_inc(x_1);
x_399 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_374, x_1, x_337);
x_400 = lean_box(0);
x_401 = l_Lean_PersistentArray_push___redArg(x_380, x_400);
x_402 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_403 = l_Lean_PersistentArray_push___redArg(x_381, x_402);
x_404 = l_Lean_PersistentArray_push___redArg(x_382, x_402);
x_405 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_406 = l_Lean_PersistentArray_push___redArg(x_383, x_405);
x_407 = lean_box(0);
x_408 = l_Lean_PersistentArray_push___redArg(x_384, x_407);
x_409 = lean_box(0);
x_410 = l_Lean_PersistentArray_push___redArg(x_386, x_409);
if (lean_is_scalar(x_397)) {
 x_411 = lean_alloc_ctor(0, 22, 2);
} else {
 x_411 = x_397;
}
lean_ctor_set(x_411, 0, x_398);
lean_ctor_set(x_411, 1, x_399);
lean_ctor_set(x_411, 2, x_375);
lean_ctor_set(x_411, 3, x_376);
lean_ctor_set(x_411, 4, x_377);
lean_ctor_set(x_411, 5, x_378);
lean_ctor_set(x_411, 6, x_379);
lean_ctor_set(x_411, 7, x_401);
lean_ctor_set(x_411, 8, x_403);
lean_ctor_set(x_411, 9, x_404);
lean_ctor_set(x_411, 10, x_406);
lean_ctor_set(x_411, 11, x_408);
lean_ctor_set(x_411, 12, x_385);
lean_ctor_set(x_411, 13, x_410);
lean_ctor_set(x_411, 14, x_387);
lean_ctor_set(x_411, 15, x_388);
lean_ctor_set(x_411, 16, x_390);
lean_ctor_set(x_411, 17, x_391);
lean_ctor_set(x_411, 18, x_392);
lean_ctor_set(x_411, 19, x_393);
lean_ctor_set(x_411, 20, x_394);
lean_ctor_set(x_411, 21, x_395);
lean_ctor_set_uint8(x_411, sizeof(void*)*22, x_389);
lean_ctor_set_uint8(x_411, sizeof(void*)*22 + 1, x_396);
if (lean_is_scalar(x_372)) {
 x_412 = lean_alloc_ctor(0, 4, 0);
} else {
 x_412 = x_372;
}
lean_ctor_set(x_412, 0, x_369);
lean_ctor_set(x_412, 1, x_411);
lean_ctor_set(x_412, 2, x_370);
lean_ctor_set(x_412, 3, x_371);
if (lean_is_scalar(x_368)) {
 x_413 = lean_alloc_ctor(0, 16, 1);
} else {
 x_413 = x_368;
}
lean_ctor_set(x_413, 0, x_352);
lean_ctor_set(x_413, 1, x_353);
lean_ctor_set(x_413, 2, x_354);
lean_ctor_set(x_413, 3, x_355);
lean_ctor_set(x_413, 4, x_356);
lean_ctor_set(x_413, 5, x_357);
lean_ctor_set(x_413, 6, x_358);
lean_ctor_set(x_413, 7, x_359);
lean_ctor_set(x_413, 8, x_361);
lean_ctor_set(x_413, 9, x_362);
lean_ctor_set(x_413, 10, x_363);
lean_ctor_set(x_413, 11, x_364);
lean_ctor_set(x_413, 12, x_365);
lean_ctor_set(x_413, 13, x_366);
lean_ctor_set(x_413, 14, x_412);
lean_ctor_set(x_413, 15, x_367);
lean_ctor_set_uint8(x_413, sizeof(void*)*16, x_360);
x_414 = lean_st_ref_set(x_338, x_413, x_351);
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
lean_dec(x_414);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_1);
x_416 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_338, x_339, x_340, x_341, x_342, x_343, x_344, x_345, x_415);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
lean_dec(x_416);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_1);
x_418 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_337, x_338, x_339, x_340, x_341, x_342, x_343, x_344, x_345, x_417);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; 
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
lean_dec(x_418);
lean_inc(x_345);
lean_inc(x_344);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_1);
x_420 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_338, x_339, x_340, x_341, x_342, x_343, x_344, x_345, x_419);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
lean_inc(x_337);
x_422 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_337, x_338, x_339, x_340, x_341, x_342, x_343, x_344, x_345, x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_424 = x_422;
} else {
 lean_dec_ref(x_422);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(0, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_337);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_337);
x_426 = lean_ctor_get(x_422, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_422, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_428 = x_422;
} else {
 lean_dec_ref(x_422);
 x_428 = lean_box(0);
}
if (lean_is_scalar(x_428)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_428;
}
lean_ctor_set(x_429, 0, x_426);
lean_ctor_set(x_429, 1, x_427);
return x_429;
}
}
else
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_1);
x_430 = lean_ctor_get(x_420, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_420, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_432 = x_420;
} else {
 lean_dec_ref(x_420);
 x_432 = lean_box(0);
}
if (lean_is_scalar(x_432)) {
 x_433 = lean_alloc_ctor(1, 2, 0);
} else {
 x_433 = x_432;
}
lean_ctor_set(x_433, 0, x_430);
lean_ctor_set(x_433, 1, x_431);
return x_433;
}
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_1);
x_434 = lean_ctor_get(x_418, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_418, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_436 = x_418;
} else {
 lean_dec_ref(x_418);
 x_436 = lean_box(0);
}
if (lean_is_scalar(x_436)) {
 x_437 = lean_alloc_ctor(1, 2, 0);
} else {
 x_437 = x_436;
}
lean_ctor_set(x_437, 0, x_434);
lean_ctor_set(x_437, 1, x_435);
return x_437;
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_345);
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_1);
x_438 = lean_ctor_get(x_416, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_416, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_440 = x_416;
} else {
 lean_dec_ref(x_416);
 x_440 = lean_box(0);
}
if (lean_is_scalar(x_440)) {
 x_441 = lean_alloc_ctor(1, 2, 0);
} else {
 x_441 = x_440;
}
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_439);
return x_441;
}
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; uint8_t x_569; 
x_455 = lean_ctor_get(x_17, 0);
x_456 = lean_ctor_get(x_17, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_17);
x_457 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_458 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_457, x_8, x_456);
x_459 = lean_ctor_get(x_455, 0);
lean_inc(x_459);
lean_dec(x_455);
x_460 = lean_ctor_get(x_458, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_458, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_462 = x_458;
} else {
 lean_dec_ref(x_458);
 x_462 = lean_box(0);
}
x_463 = lean_ctor_get(x_459, 2);
lean_inc(x_463);
lean_dec(x_459);
x_569 = lean_unbox(x_460);
lean_dec(x_460);
if (x_569 == 0)
{
lean_dec(x_462);
x_464 = x_2;
x_465 = x_3;
x_466 = x_4;
x_467 = x_5;
x_468 = x_6;
x_469 = x_7;
x_470 = x_8;
x_471 = x_9;
x_472 = x_461;
goto block_568;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_570 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_571 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_462)) {
 x_572 = lean_alloc_ctor(7, 2, 0);
} else {
 x_572 = x_462;
 lean_ctor_set_tag(x_572, 7);
}
lean_ctor_set(x_572, 0, x_570);
lean_ctor_set(x_572, 1, x_571);
x_573 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
x_574 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_574, 0, x_572);
lean_ctor_set(x_574, 1, x_573);
lean_inc(x_463);
x_575 = l_Nat_reprFast(x_463);
x_576 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_576, 0, x_575);
x_577 = l_Lean_MessageData_ofFormat(x_576);
x_578 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_578, 0, x_574);
lean_ctor_set(x_578, 1, x_577);
x_579 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_570);
x_580 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_457, x_579, x_6, x_7, x_8, x_9, x_461);
x_581 = lean_ctor_get(x_580, 1);
lean_inc(x_581);
lean_dec(x_580);
x_464 = x_2;
x_465 = x_3;
x_466 = x_4;
x_467 = x_5;
x_468 = x_6;
x_469 = x_7;
x_470 = x_8;
x_471 = x_9;
x_472 = x_581;
goto block_568;
}
block_568:
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; uint8_t x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_473 = lean_st_ref_take(x_464, x_472);
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_474, 14);
lean_inc(x_475);
x_476 = lean_ctor_get(x_475, 1);
lean_inc(x_476);
x_477 = lean_ctor_get(x_473, 1);
lean_inc(x_477);
lean_dec(x_473);
x_478 = lean_ctor_get(x_474, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_474, 1);
lean_inc(x_479);
x_480 = lean_ctor_get(x_474, 2);
lean_inc(x_480);
x_481 = lean_ctor_get(x_474, 3);
lean_inc(x_481);
x_482 = lean_ctor_get(x_474, 4);
lean_inc(x_482);
x_483 = lean_ctor_get(x_474, 5);
lean_inc(x_483);
x_484 = lean_ctor_get(x_474, 6);
lean_inc(x_484);
x_485 = lean_ctor_get(x_474, 7);
lean_inc(x_485);
x_486 = lean_ctor_get_uint8(x_474, sizeof(void*)*16);
x_487 = lean_ctor_get(x_474, 8);
lean_inc(x_487);
x_488 = lean_ctor_get(x_474, 9);
lean_inc(x_488);
x_489 = lean_ctor_get(x_474, 10);
lean_inc(x_489);
x_490 = lean_ctor_get(x_474, 11);
lean_inc(x_490);
x_491 = lean_ctor_get(x_474, 12);
lean_inc(x_491);
x_492 = lean_ctor_get(x_474, 13);
lean_inc(x_492);
x_493 = lean_ctor_get(x_474, 15);
lean_inc(x_493);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 lean_ctor_release(x_474, 2);
 lean_ctor_release(x_474, 3);
 lean_ctor_release(x_474, 4);
 lean_ctor_release(x_474, 5);
 lean_ctor_release(x_474, 6);
 lean_ctor_release(x_474, 7);
 lean_ctor_release(x_474, 8);
 lean_ctor_release(x_474, 9);
 lean_ctor_release(x_474, 10);
 lean_ctor_release(x_474, 11);
 lean_ctor_release(x_474, 12);
 lean_ctor_release(x_474, 13);
 lean_ctor_release(x_474, 14);
 lean_ctor_release(x_474, 15);
 x_494 = x_474;
} else {
 lean_dec_ref(x_474);
 x_494 = lean_box(0);
}
x_495 = lean_ctor_get(x_475, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_475, 2);
lean_inc(x_496);
x_497 = lean_ctor_get(x_475, 3);
lean_inc(x_497);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 lean_ctor_release(x_475, 2);
 lean_ctor_release(x_475, 3);
 x_498 = x_475;
} else {
 lean_dec_ref(x_475);
 x_498 = lean_box(0);
}
x_499 = lean_ctor_get(x_476, 0);
lean_inc(x_499);
x_500 = lean_ctor_get(x_476, 1);
lean_inc(x_500);
x_501 = lean_ctor_get(x_476, 2);
lean_inc(x_501);
x_502 = lean_ctor_get(x_476, 3);
lean_inc(x_502);
x_503 = lean_ctor_get(x_476, 4);
lean_inc(x_503);
x_504 = lean_ctor_get(x_476, 5);
lean_inc(x_504);
x_505 = lean_ctor_get(x_476, 6);
lean_inc(x_505);
x_506 = lean_ctor_get(x_476, 7);
lean_inc(x_506);
x_507 = lean_ctor_get(x_476, 8);
lean_inc(x_507);
x_508 = lean_ctor_get(x_476, 9);
lean_inc(x_508);
x_509 = lean_ctor_get(x_476, 10);
lean_inc(x_509);
x_510 = lean_ctor_get(x_476, 11);
lean_inc(x_510);
x_511 = lean_ctor_get(x_476, 12);
lean_inc(x_511);
x_512 = lean_ctor_get(x_476, 13);
lean_inc(x_512);
x_513 = lean_ctor_get(x_476, 14);
lean_inc(x_513);
x_514 = lean_ctor_get(x_476, 15);
lean_inc(x_514);
x_515 = lean_ctor_get_uint8(x_476, sizeof(void*)*22);
x_516 = lean_ctor_get(x_476, 16);
lean_inc(x_516);
x_517 = lean_ctor_get(x_476, 17);
lean_inc(x_517);
x_518 = lean_ctor_get(x_476, 18);
lean_inc(x_518);
x_519 = lean_ctor_get(x_476, 19);
lean_inc(x_519);
x_520 = lean_ctor_get(x_476, 20);
lean_inc(x_520);
x_521 = lean_ctor_get(x_476, 21);
lean_inc(x_521);
x_522 = lean_ctor_get_uint8(x_476, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 lean_ctor_release(x_476, 2);
 lean_ctor_release(x_476, 3);
 lean_ctor_release(x_476, 4);
 lean_ctor_release(x_476, 5);
 lean_ctor_release(x_476, 6);
 lean_ctor_release(x_476, 7);
 lean_ctor_release(x_476, 8);
 lean_ctor_release(x_476, 9);
 lean_ctor_release(x_476, 10);
 lean_ctor_release(x_476, 11);
 lean_ctor_release(x_476, 12);
 lean_ctor_release(x_476, 13);
 lean_ctor_release(x_476, 14);
 lean_ctor_release(x_476, 15);
 lean_ctor_release(x_476, 16);
 lean_ctor_release(x_476, 17);
 lean_ctor_release(x_476, 18);
 lean_ctor_release(x_476, 19);
 lean_ctor_release(x_476, 20);
 lean_ctor_release(x_476, 21);
 x_523 = x_476;
} else {
 lean_dec_ref(x_476);
 x_523 = lean_box(0);
}
lean_inc(x_1);
x_524 = l_Lean_PersistentArray_push___redArg(x_499, x_1);
lean_inc(x_463);
lean_inc(x_1);
x_525 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_500, x_1, x_463);
x_526 = lean_box(0);
x_527 = l_Lean_PersistentArray_push___redArg(x_506, x_526);
x_528 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_529 = l_Lean_PersistentArray_push___redArg(x_507, x_528);
x_530 = l_Lean_PersistentArray_push___redArg(x_508, x_528);
x_531 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_532 = l_Lean_PersistentArray_push___redArg(x_509, x_531);
x_533 = lean_box(0);
x_534 = l_Lean_PersistentArray_push___redArg(x_510, x_533);
x_535 = lean_box(0);
x_536 = l_Lean_PersistentArray_push___redArg(x_512, x_535);
if (lean_is_scalar(x_523)) {
 x_537 = lean_alloc_ctor(0, 22, 2);
} else {
 x_537 = x_523;
}
lean_ctor_set(x_537, 0, x_524);
lean_ctor_set(x_537, 1, x_525);
lean_ctor_set(x_537, 2, x_501);
lean_ctor_set(x_537, 3, x_502);
lean_ctor_set(x_537, 4, x_503);
lean_ctor_set(x_537, 5, x_504);
lean_ctor_set(x_537, 6, x_505);
lean_ctor_set(x_537, 7, x_527);
lean_ctor_set(x_537, 8, x_529);
lean_ctor_set(x_537, 9, x_530);
lean_ctor_set(x_537, 10, x_532);
lean_ctor_set(x_537, 11, x_534);
lean_ctor_set(x_537, 12, x_511);
lean_ctor_set(x_537, 13, x_536);
lean_ctor_set(x_537, 14, x_513);
lean_ctor_set(x_537, 15, x_514);
lean_ctor_set(x_537, 16, x_516);
lean_ctor_set(x_537, 17, x_517);
lean_ctor_set(x_537, 18, x_518);
lean_ctor_set(x_537, 19, x_519);
lean_ctor_set(x_537, 20, x_520);
lean_ctor_set(x_537, 21, x_521);
lean_ctor_set_uint8(x_537, sizeof(void*)*22, x_515);
lean_ctor_set_uint8(x_537, sizeof(void*)*22 + 1, x_522);
if (lean_is_scalar(x_498)) {
 x_538 = lean_alloc_ctor(0, 4, 0);
} else {
 x_538 = x_498;
}
lean_ctor_set(x_538, 0, x_495);
lean_ctor_set(x_538, 1, x_537);
lean_ctor_set(x_538, 2, x_496);
lean_ctor_set(x_538, 3, x_497);
if (lean_is_scalar(x_494)) {
 x_539 = lean_alloc_ctor(0, 16, 1);
} else {
 x_539 = x_494;
}
lean_ctor_set(x_539, 0, x_478);
lean_ctor_set(x_539, 1, x_479);
lean_ctor_set(x_539, 2, x_480);
lean_ctor_set(x_539, 3, x_481);
lean_ctor_set(x_539, 4, x_482);
lean_ctor_set(x_539, 5, x_483);
lean_ctor_set(x_539, 6, x_484);
lean_ctor_set(x_539, 7, x_485);
lean_ctor_set(x_539, 8, x_487);
lean_ctor_set(x_539, 9, x_488);
lean_ctor_set(x_539, 10, x_489);
lean_ctor_set(x_539, 11, x_490);
lean_ctor_set(x_539, 12, x_491);
lean_ctor_set(x_539, 13, x_492);
lean_ctor_set(x_539, 14, x_538);
lean_ctor_set(x_539, 15, x_493);
lean_ctor_set_uint8(x_539, sizeof(void*)*16, x_486);
x_540 = lean_st_ref_set(x_464, x_539, x_477);
x_541 = lean_ctor_get(x_540, 1);
lean_inc(x_541);
lean_dec(x_540);
lean_inc(x_471);
lean_inc(x_470);
lean_inc(x_469);
lean_inc(x_468);
lean_inc(x_467);
lean_inc(x_466);
lean_inc(x_465);
lean_inc(x_464);
lean_inc(x_1);
x_542 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_541);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; 
x_543 = lean_ctor_get(x_542, 1);
lean_inc(x_543);
lean_dec(x_542);
lean_inc(x_471);
lean_inc(x_470);
lean_inc(x_469);
lean_inc(x_468);
lean_inc(x_467);
lean_inc(x_466);
lean_inc(x_465);
lean_inc(x_464);
lean_inc(x_463);
lean_inc(x_1);
x_544 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_543);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; 
x_545 = lean_ctor_get(x_544, 1);
lean_inc(x_545);
lean_dec(x_544);
lean_inc(x_471);
lean_inc(x_470);
lean_inc(x_469);
lean_inc(x_468);
lean_inc(x_467);
lean_inc(x_466);
lean_inc(x_465);
lean_inc(x_464);
lean_inc(x_1);
x_546 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_545);
if (lean_obj_tag(x_546) == 0)
{
lean_object* x_547; lean_object* x_548; 
x_547 = lean_ctor_get(x_546, 1);
lean_inc(x_547);
lean_dec(x_546);
lean_inc(x_463);
x_548 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_463, x_464, x_465, x_466, x_467, x_468, x_469, x_470, x_471, x_547);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_548, 1);
lean_inc(x_549);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_550 = x_548;
} else {
 lean_dec_ref(x_548);
 x_550 = lean_box(0);
}
if (lean_is_scalar(x_550)) {
 x_551 = lean_alloc_ctor(0, 2, 0);
} else {
 x_551 = x_550;
}
lean_ctor_set(x_551, 0, x_463);
lean_ctor_set(x_551, 1, x_549);
return x_551;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
lean_dec(x_463);
x_552 = lean_ctor_get(x_548, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_548, 1);
lean_inc(x_553);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_554 = x_548;
} else {
 lean_dec_ref(x_548);
 x_554 = lean_box(0);
}
if (lean_is_scalar(x_554)) {
 x_555 = lean_alloc_ctor(1, 2, 0);
} else {
 x_555 = x_554;
}
lean_ctor_set(x_555, 0, x_552);
lean_ctor_set(x_555, 1, x_553);
return x_555;
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_1);
x_556 = lean_ctor_get(x_546, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_546, 1);
lean_inc(x_557);
if (lean_is_exclusive(x_546)) {
 lean_ctor_release(x_546, 0);
 lean_ctor_release(x_546, 1);
 x_558 = x_546;
} else {
 lean_dec_ref(x_546);
 x_558 = lean_box(0);
}
if (lean_is_scalar(x_558)) {
 x_559 = lean_alloc_ctor(1, 2, 0);
} else {
 x_559 = x_558;
}
lean_ctor_set(x_559, 0, x_556);
lean_ctor_set(x_559, 1, x_557);
return x_559;
}
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_1);
x_560 = lean_ctor_get(x_544, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_544, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_544)) {
 lean_ctor_release(x_544, 0);
 lean_ctor_release(x_544, 1);
 x_562 = x_544;
} else {
 lean_dec_ref(x_544);
 x_562 = lean_box(0);
}
if (lean_is_scalar(x_562)) {
 x_563 = lean_alloc_ctor(1, 2, 0);
} else {
 x_563 = x_562;
}
lean_ctor_set(x_563, 0, x_560);
lean_ctor_set(x_563, 1, x_561);
return x_563;
}
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_468);
lean_dec(x_467);
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_464);
lean_dec(x_463);
lean_dec(x_1);
x_564 = lean_ctor_get(x_542, 0);
lean_inc(x_564);
x_565 = lean_ctor_get(x_542, 1);
lean_inc(x_565);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_566 = x_542;
} else {
 lean_dec_ref(x_542);
 x_566 = lean_box(0);
}
if (lean_is_scalar(x_566)) {
 x_567 = lean_alloc_ctor(1, 2, 0);
} else {
 x_567 = x_566;
}
lean_ctor_set(x_567, 0, x_564);
lean_ctor_set(x_567, 1, x_565);
return x_567;
}
}
}
}
else
{
lean_object* x_582; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_582 = lean_ctor_get(x_16, 0);
lean_inc(x_582);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_582);
return x_11;
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_583 = lean_ctor_get(x_11, 0);
x_584 = lean_ctor_get(x_11, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_11);
x_585 = lean_ctor_get(x_583, 1);
lean_inc(x_585);
lean_dec(x_583);
lean_inc(x_1);
x_586 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_585, x_1);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_703; 
x_587 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_584);
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_590 = x_587;
} else {
 lean_dec_ref(x_587);
 x_590 = lean_box(0);
}
x_591 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_592 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_591, x_8, x_589);
x_593 = lean_ctor_get(x_588, 0);
lean_inc(x_593);
lean_dec(x_588);
x_594 = lean_ctor_get(x_592, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_592, 1);
lean_inc(x_595);
if (lean_is_exclusive(x_592)) {
 lean_ctor_release(x_592, 0);
 lean_ctor_release(x_592, 1);
 x_596 = x_592;
} else {
 lean_dec_ref(x_592);
 x_596 = lean_box(0);
}
x_597 = lean_ctor_get(x_593, 2);
lean_inc(x_597);
lean_dec(x_593);
x_703 = lean_unbox(x_594);
lean_dec(x_594);
if (x_703 == 0)
{
lean_dec(x_596);
lean_dec(x_590);
x_598 = x_2;
x_599 = x_3;
x_600 = x_4;
x_601 = x_5;
x_602 = x_6;
x_603 = x_7;
x_604 = x_8;
x_605 = x_9;
x_606 = x_595;
goto block_702;
}
else
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_704 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_705 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_596)) {
 x_706 = lean_alloc_ctor(7, 2, 0);
} else {
 x_706 = x_596;
 lean_ctor_set_tag(x_706, 7);
}
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
x_707 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
if (lean_is_scalar(x_590)) {
 x_708 = lean_alloc_ctor(7, 2, 0);
} else {
 x_708 = x_590;
 lean_ctor_set_tag(x_708, 7);
}
lean_ctor_set(x_708, 0, x_706);
lean_ctor_set(x_708, 1, x_707);
lean_inc(x_597);
x_709 = l_Nat_reprFast(x_597);
x_710 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_710, 0, x_709);
x_711 = l_Lean_MessageData_ofFormat(x_710);
x_712 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_712, 0, x_708);
lean_ctor_set(x_712, 1, x_711);
x_713 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_713, 0, x_712);
lean_ctor_set(x_713, 1, x_704);
x_714 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_591, x_713, x_6, x_7, x_8, x_9, x_595);
x_715 = lean_ctor_get(x_714, 1);
lean_inc(x_715);
lean_dec(x_714);
x_598 = x_2;
x_599 = x_3;
x_600 = x_4;
x_601 = x_5;
x_602 = x_6;
x_603 = x_7;
x_604 = x_8;
x_605 = x_9;
x_606 = x_715;
goto block_702;
}
block_702:
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; uint8_t x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; uint8_t x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_607 = lean_st_ref_take(x_598, x_606);
x_608 = lean_ctor_get(x_607, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_608, 14);
lean_inc(x_609);
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
x_611 = lean_ctor_get(x_607, 1);
lean_inc(x_611);
lean_dec(x_607);
x_612 = lean_ctor_get(x_608, 0);
lean_inc(x_612);
x_613 = lean_ctor_get(x_608, 1);
lean_inc(x_613);
x_614 = lean_ctor_get(x_608, 2);
lean_inc(x_614);
x_615 = lean_ctor_get(x_608, 3);
lean_inc(x_615);
x_616 = lean_ctor_get(x_608, 4);
lean_inc(x_616);
x_617 = lean_ctor_get(x_608, 5);
lean_inc(x_617);
x_618 = lean_ctor_get(x_608, 6);
lean_inc(x_618);
x_619 = lean_ctor_get(x_608, 7);
lean_inc(x_619);
x_620 = lean_ctor_get_uint8(x_608, sizeof(void*)*16);
x_621 = lean_ctor_get(x_608, 8);
lean_inc(x_621);
x_622 = lean_ctor_get(x_608, 9);
lean_inc(x_622);
x_623 = lean_ctor_get(x_608, 10);
lean_inc(x_623);
x_624 = lean_ctor_get(x_608, 11);
lean_inc(x_624);
x_625 = lean_ctor_get(x_608, 12);
lean_inc(x_625);
x_626 = lean_ctor_get(x_608, 13);
lean_inc(x_626);
x_627 = lean_ctor_get(x_608, 15);
lean_inc(x_627);
if (lean_is_exclusive(x_608)) {
 lean_ctor_release(x_608, 0);
 lean_ctor_release(x_608, 1);
 lean_ctor_release(x_608, 2);
 lean_ctor_release(x_608, 3);
 lean_ctor_release(x_608, 4);
 lean_ctor_release(x_608, 5);
 lean_ctor_release(x_608, 6);
 lean_ctor_release(x_608, 7);
 lean_ctor_release(x_608, 8);
 lean_ctor_release(x_608, 9);
 lean_ctor_release(x_608, 10);
 lean_ctor_release(x_608, 11);
 lean_ctor_release(x_608, 12);
 lean_ctor_release(x_608, 13);
 lean_ctor_release(x_608, 14);
 lean_ctor_release(x_608, 15);
 x_628 = x_608;
} else {
 lean_dec_ref(x_608);
 x_628 = lean_box(0);
}
x_629 = lean_ctor_get(x_609, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_609, 2);
lean_inc(x_630);
x_631 = lean_ctor_get(x_609, 3);
lean_inc(x_631);
if (lean_is_exclusive(x_609)) {
 lean_ctor_release(x_609, 0);
 lean_ctor_release(x_609, 1);
 lean_ctor_release(x_609, 2);
 lean_ctor_release(x_609, 3);
 x_632 = x_609;
} else {
 lean_dec_ref(x_609);
 x_632 = lean_box(0);
}
x_633 = lean_ctor_get(x_610, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_610, 1);
lean_inc(x_634);
x_635 = lean_ctor_get(x_610, 2);
lean_inc(x_635);
x_636 = lean_ctor_get(x_610, 3);
lean_inc(x_636);
x_637 = lean_ctor_get(x_610, 4);
lean_inc(x_637);
x_638 = lean_ctor_get(x_610, 5);
lean_inc(x_638);
x_639 = lean_ctor_get(x_610, 6);
lean_inc(x_639);
x_640 = lean_ctor_get(x_610, 7);
lean_inc(x_640);
x_641 = lean_ctor_get(x_610, 8);
lean_inc(x_641);
x_642 = lean_ctor_get(x_610, 9);
lean_inc(x_642);
x_643 = lean_ctor_get(x_610, 10);
lean_inc(x_643);
x_644 = lean_ctor_get(x_610, 11);
lean_inc(x_644);
x_645 = lean_ctor_get(x_610, 12);
lean_inc(x_645);
x_646 = lean_ctor_get(x_610, 13);
lean_inc(x_646);
x_647 = lean_ctor_get(x_610, 14);
lean_inc(x_647);
x_648 = lean_ctor_get(x_610, 15);
lean_inc(x_648);
x_649 = lean_ctor_get_uint8(x_610, sizeof(void*)*22);
x_650 = lean_ctor_get(x_610, 16);
lean_inc(x_650);
x_651 = lean_ctor_get(x_610, 17);
lean_inc(x_651);
x_652 = lean_ctor_get(x_610, 18);
lean_inc(x_652);
x_653 = lean_ctor_get(x_610, 19);
lean_inc(x_653);
x_654 = lean_ctor_get(x_610, 20);
lean_inc(x_654);
x_655 = lean_ctor_get(x_610, 21);
lean_inc(x_655);
x_656 = lean_ctor_get_uint8(x_610, sizeof(void*)*22 + 1);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 lean_ctor_release(x_610, 1);
 lean_ctor_release(x_610, 2);
 lean_ctor_release(x_610, 3);
 lean_ctor_release(x_610, 4);
 lean_ctor_release(x_610, 5);
 lean_ctor_release(x_610, 6);
 lean_ctor_release(x_610, 7);
 lean_ctor_release(x_610, 8);
 lean_ctor_release(x_610, 9);
 lean_ctor_release(x_610, 10);
 lean_ctor_release(x_610, 11);
 lean_ctor_release(x_610, 12);
 lean_ctor_release(x_610, 13);
 lean_ctor_release(x_610, 14);
 lean_ctor_release(x_610, 15);
 lean_ctor_release(x_610, 16);
 lean_ctor_release(x_610, 17);
 lean_ctor_release(x_610, 18);
 lean_ctor_release(x_610, 19);
 lean_ctor_release(x_610, 20);
 lean_ctor_release(x_610, 21);
 x_657 = x_610;
} else {
 lean_dec_ref(x_610);
 x_657 = lean_box(0);
}
lean_inc(x_1);
x_658 = l_Lean_PersistentArray_push___redArg(x_633, x_1);
lean_inc(x_597);
lean_inc(x_1);
x_659 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_634, x_1, x_597);
x_660 = lean_box(0);
x_661 = l_Lean_PersistentArray_push___redArg(x_640, x_660);
x_662 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_663 = l_Lean_PersistentArray_push___redArg(x_641, x_662);
x_664 = l_Lean_PersistentArray_push___redArg(x_642, x_662);
x_665 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_666 = l_Lean_PersistentArray_push___redArg(x_643, x_665);
x_667 = lean_box(0);
x_668 = l_Lean_PersistentArray_push___redArg(x_644, x_667);
x_669 = lean_box(0);
x_670 = l_Lean_PersistentArray_push___redArg(x_646, x_669);
if (lean_is_scalar(x_657)) {
 x_671 = lean_alloc_ctor(0, 22, 2);
} else {
 x_671 = x_657;
}
lean_ctor_set(x_671, 0, x_658);
lean_ctor_set(x_671, 1, x_659);
lean_ctor_set(x_671, 2, x_635);
lean_ctor_set(x_671, 3, x_636);
lean_ctor_set(x_671, 4, x_637);
lean_ctor_set(x_671, 5, x_638);
lean_ctor_set(x_671, 6, x_639);
lean_ctor_set(x_671, 7, x_661);
lean_ctor_set(x_671, 8, x_663);
lean_ctor_set(x_671, 9, x_664);
lean_ctor_set(x_671, 10, x_666);
lean_ctor_set(x_671, 11, x_668);
lean_ctor_set(x_671, 12, x_645);
lean_ctor_set(x_671, 13, x_670);
lean_ctor_set(x_671, 14, x_647);
lean_ctor_set(x_671, 15, x_648);
lean_ctor_set(x_671, 16, x_650);
lean_ctor_set(x_671, 17, x_651);
lean_ctor_set(x_671, 18, x_652);
lean_ctor_set(x_671, 19, x_653);
lean_ctor_set(x_671, 20, x_654);
lean_ctor_set(x_671, 21, x_655);
lean_ctor_set_uint8(x_671, sizeof(void*)*22, x_649);
lean_ctor_set_uint8(x_671, sizeof(void*)*22 + 1, x_656);
if (lean_is_scalar(x_632)) {
 x_672 = lean_alloc_ctor(0, 4, 0);
} else {
 x_672 = x_632;
}
lean_ctor_set(x_672, 0, x_629);
lean_ctor_set(x_672, 1, x_671);
lean_ctor_set(x_672, 2, x_630);
lean_ctor_set(x_672, 3, x_631);
if (lean_is_scalar(x_628)) {
 x_673 = lean_alloc_ctor(0, 16, 1);
} else {
 x_673 = x_628;
}
lean_ctor_set(x_673, 0, x_612);
lean_ctor_set(x_673, 1, x_613);
lean_ctor_set(x_673, 2, x_614);
lean_ctor_set(x_673, 3, x_615);
lean_ctor_set(x_673, 4, x_616);
lean_ctor_set(x_673, 5, x_617);
lean_ctor_set(x_673, 6, x_618);
lean_ctor_set(x_673, 7, x_619);
lean_ctor_set(x_673, 8, x_621);
lean_ctor_set(x_673, 9, x_622);
lean_ctor_set(x_673, 10, x_623);
lean_ctor_set(x_673, 11, x_624);
lean_ctor_set(x_673, 12, x_625);
lean_ctor_set(x_673, 13, x_626);
lean_ctor_set(x_673, 14, x_672);
lean_ctor_set(x_673, 15, x_627);
lean_ctor_set_uint8(x_673, sizeof(void*)*16, x_620);
x_674 = lean_st_ref_set(x_598, x_673, x_611);
x_675 = lean_ctor_get(x_674, 1);
lean_inc(x_675);
lean_dec(x_674);
lean_inc(x_605);
lean_inc(x_604);
lean_inc(x_603);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_1);
x_676 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_598, x_599, x_600, x_601, x_602, x_603, x_604, x_605, x_675);
if (lean_obj_tag(x_676) == 0)
{
lean_object* x_677; lean_object* x_678; 
x_677 = lean_ctor_get(x_676, 1);
lean_inc(x_677);
lean_dec(x_676);
lean_inc(x_605);
lean_inc(x_604);
lean_inc(x_603);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_597);
lean_inc(x_1);
x_678 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_597, x_598, x_599, x_600, x_601, x_602, x_603, x_604, x_605, x_677);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; 
x_679 = lean_ctor_get(x_678, 1);
lean_inc(x_679);
lean_dec(x_678);
lean_inc(x_605);
lean_inc(x_604);
lean_inc(x_603);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
lean_inc(x_599);
lean_inc(x_598);
lean_inc(x_1);
x_680 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_598, x_599, x_600, x_601, x_602, x_603, x_604, x_605, x_679);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; 
x_681 = lean_ctor_get(x_680, 1);
lean_inc(x_681);
lean_dec(x_680);
lean_inc(x_597);
x_682 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_597, x_598, x_599, x_600, x_601, x_602, x_603, x_604, x_605, x_681);
if (lean_obj_tag(x_682) == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_683 = lean_ctor_get(x_682, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_684 = x_682;
} else {
 lean_dec_ref(x_682);
 x_684 = lean_box(0);
}
if (lean_is_scalar(x_684)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_684;
}
lean_ctor_set(x_685, 0, x_597);
lean_ctor_set(x_685, 1, x_683);
return x_685;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_597);
x_686 = lean_ctor_get(x_682, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_682, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_682)) {
 lean_ctor_release(x_682, 0);
 lean_ctor_release(x_682, 1);
 x_688 = x_682;
} else {
 lean_dec_ref(x_682);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_686);
lean_ctor_set(x_689, 1, x_687);
return x_689;
}
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_1);
x_690 = lean_ctor_get(x_680, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_680, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_692 = x_680;
} else {
 lean_dec_ref(x_680);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_691);
return x_693;
}
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_1);
x_694 = lean_ctor_get(x_678, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_678, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_696 = x_678;
} else {
 lean_dec_ref(x_678);
 x_696 = lean_box(0);
}
if (lean_is_scalar(x_696)) {
 x_697 = lean_alloc_ctor(1, 2, 0);
} else {
 x_697 = x_696;
}
lean_ctor_set(x_697, 0, x_694);
lean_ctor_set(x_697, 1, x_695);
return x_697;
}
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_599);
lean_dec(x_598);
lean_dec(x_597);
lean_dec(x_1);
x_698 = lean_ctor_get(x_676, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_676, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 x_700 = x_676;
} else {
 lean_dec_ref(x_676);
 x_700 = lean_box(0);
}
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_698);
lean_ctor_set(x_701, 1, x_699);
return x_701;
}
}
}
else
{
lean_object* x_716; lean_object* x_717; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_716 = lean_ctor_get(x_586, 0);
lean_inc(x_716);
lean_dec(x_586);
x_717 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_584);
return x_717;
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
uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_10 = 0;
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(x_10);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
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
uint8_t x_10; lean_object* x_11; 
x_10 = 0;
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(x_10);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(x_10);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_12);
x_19 = !lean_is_exclusive(x_11);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_11, 0);
lean_dec(x_20);
x_21 = 1;
x_22 = lean_box(x_21);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_dec(x_11);
x_24 = 1;
x_25 = lean_box(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_36; lean_object* x_37; 
x_36 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_isMul_x3f___redArg(x_1, x_36, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_40 = l_Lean_Meta_getIntValue_x3f(x_1, x_7, x_8, x_9, x_10, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_42;
goto block_35;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_44 = lean_ctor_get(x_40, 1);
x_45 = lean_ctor_get(x_40, 0);
lean_dec(x_45);
x_46 = !lean_is_exclusive(x_41);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_41, 0);
x_48 = l_Int_Linear_Poly_isZero(x_2);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
lean_free_object(x_41);
lean_dec(x_47);
lean_free_object(x_40);
x_49 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_44);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*6 + 11);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_52;
goto block_35;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_49);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_54 = lean_ctor_get(x_49, 1);
x_55 = lean_ctor_get(x_49, 0);
lean_dec(x_55);
x_56 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
lean_inc(x_1);
x_57 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_49, 7);
lean_ctor_set(x_49, 1, x_57);
lean_ctor_set(x_49, 0, x_56);
x_58 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_49);
lean_ctor_set(x_59, 1, x_58);
x_60 = l_Lean_Meta_Grind_reportIssue(x_59, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_61;
goto block_35;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_49, 1);
lean_inc(x_62);
lean_dec(x_49);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
lean_inc(x_1);
x_64 = l_Lean_indentExpr(x_1);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_Grind_reportIssue(x_67, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_62);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_69;
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
lean_ctor_set_tag(x_41, 0);
return x_40;
}
}
else
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_41, 0);
lean_inc(x_70);
lean_dec(x_41);
x_71 = l_Int_Linear_Poly_isZero(x_2);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_70);
lean_free_object(x_40);
x_72 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_44);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_73, sizeof(void*)*6 + 11);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_72, 1);
lean_inc(x_75);
lean_dec(x_72);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_75;
goto block_35;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_77 = x_72;
} else {
 lean_dec_ref(x_72);
 x_77 = lean_box(0);
}
x_78 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
lean_inc(x_1);
x_79 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_77)) {
 x_80 = lean_alloc_ctor(7, 2, 0);
} else {
 x_80 = x_77;
 lean_ctor_set_tag(x_80, 7);
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_Meta_Grind_reportIssue(x_82, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_76);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_84;
goto block_35;
}
}
else
{
lean_object* x_85; 
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
x_85 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_85, 0, x_70);
lean_ctor_set(x_40, 0, x_85);
return x_40;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_86 = lean_ctor_get(x_40, 1);
lean_inc(x_86);
lean_dec(x_40);
x_87 = lean_ctor_get(x_41, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_88 = x_41;
} else {
 lean_dec_ref(x_41);
 x_88 = lean_box(0);
}
x_89 = l_Int_Linear_Poly_isZero(x_2);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
lean_dec(x_88);
lean_dec(x_87);
x_90 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_86);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get_uint8(x_91, sizeof(void*)*6 + 11);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_93;
goto block_35;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_95 = x_90;
} else {
 lean_dec_ref(x_90);
 x_95 = lean_box(0);
}
x_96 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__2;
lean_inc(x_1);
x_97 = l_Lean_indentExpr(x_1);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(7, 2, 0);
} else {
 x_98 = x_95;
 lean_ctor_set_tag(x_98, 7);
}
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial___closed__4;
x_100 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = l_Lean_Meta_Grind_reportIssue(x_100, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_94);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
x_20 = x_102;
goto block_35;
}
}
else
{
lean_object* x_103; lean_object* x_104; 
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
if (lean_is_scalar(x_88)) {
 x_103 = lean_alloc_ctor(0, 1, 0);
} else {
 x_103 = x_88;
 lean_ctor_set_tag(x_103, 0);
}
lean_ctor_set(x_103, 0, x_87);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_86);
return x_104;
}
}
}
}
else
{
uint8_t x_105; 
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
x_105 = !lean_is_exclusive(x_40);
if (x_105 == 0)
{
return x_40;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_40, 0);
x_107 = lean_ctor_get(x_40, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_40);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_1);
x_109 = lean_ctor_get(x_38, 0);
lean_inc(x_109);
lean_dec(x_38);
x_110 = lean_ctor_get(x_37, 1);
lean_inc(x_110);
lean_dec(x_37);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_109, 1);
lean_inc(x_112);
lean_dec(x_109);
x_113 = lean_grind_cutsat_mk_var(x_112, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_110);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set(x_116, 2, x_2);
lean_ctor_set(x_113, 0, x_116);
return x_113;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_113, 0);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_113);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_111);
lean_ctor_set(x_119, 1, x_117);
lean_ctor_set(x_119, 2, x_2);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
uint8_t x_121; 
lean_dec(x_111);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_113);
if (x_121 == 0)
{
return x_113;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_113, 0);
x_123 = lean_ctor_get(x_113, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_113);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_125; 
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
x_125 = !lean_is_exclusive(x_37);
if (x_125 == 0)
{
return x_37;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_37, 0);
x_127 = lean_ctor_get(x_37, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_37);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
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
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 1;
lean_inc(x_1);
x_13 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_20, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_1 = x_19;
x_2 = x_22;
x_11 = x_23;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
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
uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_11 = 1;
lean_inc(x_1);
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_isAdd_x3f___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1;
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_12, 1);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_addMonomial(x_20, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly_go(x_19, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
return x_25;
}
else
{
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
}
}
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin, lean_object*);
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin, lean_io_mk_world());
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
