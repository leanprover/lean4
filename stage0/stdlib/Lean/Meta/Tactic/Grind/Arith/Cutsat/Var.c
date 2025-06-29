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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_318; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_318 = lean_unbox(x_25);
lean_dec(x_25);
if (x_318 == 0)
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
goto block_317;
}
else
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_319 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_320 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_320);
lean_ctor_set(x_22, 0, x_319);
x_321 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_321);
lean_ctor_set(x_17, 0, x_22);
lean_inc(x_27);
x_322 = l_Nat_reprFast(x_27);
x_323 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_323, 0, x_322);
x_324 = l_Lean_MessageData_ofFormat(x_323);
x_325 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_325, 0, x_17);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_319);
x_327 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_326, x_6, x_7, x_8, x_9, x_26);
x_328 = lean_ctor_get(x_327, 1);
lean_inc(x_328);
lean_dec(x_327);
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_328;
goto block_317;
}
block_317:
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
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
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
x_113 = lean_ctor_get_uint8(x_40, sizeof(void*)*21);
x_114 = lean_ctor_get(x_40, 16);
x_115 = lean_ctor_get(x_40, 17);
x_116 = lean_ctor_get(x_40, 18);
x_117 = lean_ctor_get(x_40, 19);
x_118 = lean_ctor_get(x_40, 20);
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
x_119 = l_Lean_PersistentArray_push___redArg(x_97, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_120 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_98, x_1, x_27);
x_121 = lean_box(0);
x_122 = l_Lean_PersistentArray_push___redArg(x_104, x_121);
x_123 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_124 = l_Lean_PersistentArray_push___redArg(x_105, x_123);
x_125 = l_Lean_PersistentArray_push___redArg(x_106, x_123);
x_126 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_127 = l_Lean_PersistentArray_push___redArg(x_107, x_126);
x_128 = lean_box(0);
x_129 = l_Lean_PersistentArray_push___redArg(x_108, x_128);
x_130 = lean_box(0);
x_131 = l_Lean_PersistentArray_push___redArg(x_110, x_130);
x_132 = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(x_132, 0, x_119);
lean_ctor_set(x_132, 1, x_120);
lean_ctor_set(x_132, 2, x_99);
lean_ctor_set(x_132, 3, x_100);
lean_ctor_set(x_132, 4, x_101);
lean_ctor_set(x_132, 5, x_102);
lean_ctor_set(x_132, 6, x_103);
lean_ctor_set(x_132, 7, x_122);
lean_ctor_set(x_132, 8, x_124);
lean_ctor_set(x_132, 9, x_125);
lean_ctor_set(x_132, 10, x_127);
lean_ctor_set(x_132, 11, x_129);
lean_ctor_set(x_132, 12, x_109);
lean_ctor_set(x_132, 13, x_131);
lean_ctor_set(x_132, 14, x_111);
lean_ctor_set(x_132, 15, x_112);
lean_ctor_set(x_132, 16, x_114);
lean_ctor_set(x_132, 17, x_115);
lean_ctor_set(x_132, 18, x_116);
lean_ctor_set(x_132, 19, x_117);
lean_ctor_set(x_132, 20, x_118);
lean_ctor_set_uint8(x_132, sizeof(void*)*21, x_113);
lean_ctor_set(x_39, 1, x_132);
x_133 = lean_st_ref_set(x_28, x_38, x_41);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec(x_133);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_135 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
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
lean_inc(x_27);
lean_inc(x_1);
x_137 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_136);
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
lean_inc(x_1);
x_139 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
lean_inc(x_27);
x_141 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_27);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_27);
x_145 = lean_ctor_get(x_141, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_147 = x_141;
} else {
 lean_dec_ref(x_141);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
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
x_149 = lean_ctor_get(x_139, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_139, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_151 = x_139;
} else {
 lean_dec_ref(x_139);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
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
x_153 = lean_ctor_get(x_137, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_137, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_155 = x_137;
} else {
 lean_dec_ref(x_137);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_153);
lean_ctor_set(x_156, 1, x_154);
return x_156;
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
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
x_157 = lean_ctor_get(x_135, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_135, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_159 = x_135;
} else {
 lean_dec_ref(x_135);
 x_159 = lean_box(0);
}
if (lean_is_scalar(x_159)) {
 x_160 = lean_alloc_ctor(1, 2, 0);
} else {
 x_160 = x_159;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_158);
return x_160;
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_161 = lean_ctor_get(x_39, 0);
x_162 = lean_ctor_get(x_39, 2);
x_163 = lean_ctor_get(x_39, 3);
lean_inc(x_163);
lean_inc(x_162);
lean_inc(x_161);
lean_dec(x_39);
x_164 = lean_ctor_get(x_40, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_40, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_40, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_40, 3);
lean_inc(x_167);
x_168 = lean_ctor_get(x_40, 4);
lean_inc(x_168);
x_169 = lean_ctor_get(x_40, 5);
lean_inc(x_169);
x_170 = lean_ctor_get(x_40, 6);
lean_inc(x_170);
x_171 = lean_ctor_get(x_40, 7);
lean_inc(x_171);
x_172 = lean_ctor_get(x_40, 8);
lean_inc(x_172);
x_173 = lean_ctor_get(x_40, 9);
lean_inc(x_173);
x_174 = lean_ctor_get(x_40, 10);
lean_inc(x_174);
x_175 = lean_ctor_get(x_40, 11);
lean_inc(x_175);
x_176 = lean_ctor_get(x_40, 12);
lean_inc(x_176);
x_177 = lean_ctor_get(x_40, 13);
lean_inc(x_177);
x_178 = lean_ctor_get(x_40, 14);
lean_inc(x_178);
x_179 = lean_ctor_get(x_40, 15);
lean_inc(x_179);
x_180 = lean_ctor_get_uint8(x_40, sizeof(void*)*21);
x_181 = lean_ctor_get(x_40, 16);
lean_inc(x_181);
x_182 = lean_ctor_get(x_40, 17);
lean_inc(x_182);
x_183 = lean_ctor_get(x_40, 18);
lean_inc(x_183);
x_184 = lean_ctor_get(x_40, 19);
lean_inc(x_184);
x_185 = lean_ctor_get(x_40, 20);
lean_inc(x_185);
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
 x_186 = x_40;
} else {
 lean_dec_ref(x_40);
 x_186 = lean_box(0);
}
lean_inc(x_1);
x_187 = l_Lean_PersistentArray_push___redArg(x_164, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_188 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_165, x_1, x_27);
x_189 = lean_box(0);
x_190 = l_Lean_PersistentArray_push___redArg(x_171, x_189);
x_191 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_192 = l_Lean_PersistentArray_push___redArg(x_172, x_191);
x_193 = l_Lean_PersistentArray_push___redArg(x_173, x_191);
x_194 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_195 = l_Lean_PersistentArray_push___redArg(x_174, x_194);
x_196 = lean_box(0);
x_197 = l_Lean_PersistentArray_push___redArg(x_175, x_196);
x_198 = lean_box(0);
x_199 = l_Lean_PersistentArray_push___redArg(x_177, x_198);
if (lean_is_scalar(x_186)) {
 x_200 = lean_alloc_ctor(0, 21, 1);
} else {
 x_200 = x_186;
}
lean_ctor_set(x_200, 0, x_187);
lean_ctor_set(x_200, 1, x_188);
lean_ctor_set(x_200, 2, x_166);
lean_ctor_set(x_200, 3, x_167);
lean_ctor_set(x_200, 4, x_168);
lean_ctor_set(x_200, 5, x_169);
lean_ctor_set(x_200, 6, x_170);
lean_ctor_set(x_200, 7, x_190);
lean_ctor_set(x_200, 8, x_192);
lean_ctor_set(x_200, 9, x_193);
lean_ctor_set(x_200, 10, x_195);
lean_ctor_set(x_200, 11, x_197);
lean_ctor_set(x_200, 12, x_176);
lean_ctor_set(x_200, 13, x_199);
lean_ctor_set(x_200, 14, x_178);
lean_ctor_set(x_200, 15, x_179);
lean_ctor_set(x_200, 16, x_181);
lean_ctor_set(x_200, 17, x_182);
lean_ctor_set(x_200, 18, x_183);
lean_ctor_set(x_200, 19, x_184);
lean_ctor_set(x_200, 20, x_185);
lean_ctor_set_uint8(x_200, sizeof(void*)*21, x_180);
x_201 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_201, 0, x_161);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set(x_201, 2, x_162);
lean_ctor_set(x_201, 3, x_163);
lean_ctor_set(x_38, 14, x_201);
x_202 = lean_st_ref_set(x_28, x_38, x_41);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_204 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec(x_204);
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
x_206 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; 
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
x_208 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
lean_inc(x_27);
x_210 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_209);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_210, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_212 = x_210;
} else {
 lean_dec_ref(x_210);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_27);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_27);
x_214 = lean_ctor_get(x_210, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_210, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 lean_ctor_release(x_210, 1);
 x_216 = x_210;
} else {
 lean_dec_ref(x_210);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
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
x_218 = lean_ctor_get(x_208, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_208, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_220 = x_208;
} else {
 lean_dec_ref(x_208);
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
x_222 = lean_ctor_get(x_206, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_206, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_224 = x_206;
} else {
 lean_dec_ref(x_206);
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
x_226 = lean_ctor_get(x_204, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_204, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_228 = x_204;
} else {
 lean_dec_ref(x_204);
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
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_230 = lean_ctor_get(x_38, 0);
x_231 = lean_ctor_get(x_38, 1);
x_232 = lean_ctor_get(x_38, 2);
x_233 = lean_ctor_get(x_38, 3);
x_234 = lean_ctor_get(x_38, 4);
x_235 = lean_ctor_get(x_38, 5);
x_236 = lean_ctor_get(x_38, 6);
x_237 = lean_ctor_get(x_38, 7);
x_238 = lean_ctor_get_uint8(x_38, sizeof(void*)*16);
x_239 = lean_ctor_get(x_38, 8);
x_240 = lean_ctor_get(x_38, 9);
x_241 = lean_ctor_get(x_38, 10);
x_242 = lean_ctor_get(x_38, 11);
x_243 = lean_ctor_get(x_38, 12);
x_244 = lean_ctor_get(x_38, 13);
x_245 = lean_ctor_get(x_38, 15);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_38);
x_246 = lean_ctor_get(x_39, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_39, 2);
lean_inc(x_247);
x_248 = lean_ctor_get(x_39, 3);
lean_inc(x_248);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 x_249 = x_39;
} else {
 lean_dec_ref(x_39);
 x_249 = lean_box(0);
}
x_250 = lean_ctor_get(x_40, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_40, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_40, 2);
lean_inc(x_252);
x_253 = lean_ctor_get(x_40, 3);
lean_inc(x_253);
x_254 = lean_ctor_get(x_40, 4);
lean_inc(x_254);
x_255 = lean_ctor_get(x_40, 5);
lean_inc(x_255);
x_256 = lean_ctor_get(x_40, 6);
lean_inc(x_256);
x_257 = lean_ctor_get(x_40, 7);
lean_inc(x_257);
x_258 = lean_ctor_get(x_40, 8);
lean_inc(x_258);
x_259 = lean_ctor_get(x_40, 9);
lean_inc(x_259);
x_260 = lean_ctor_get(x_40, 10);
lean_inc(x_260);
x_261 = lean_ctor_get(x_40, 11);
lean_inc(x_261);
x_262 = lean_ctor_get(x_40, 12);
lean_inc(x_262);
x_263 = lean_ctor_get(x_40, 13);
lean_inc(x_263);
x_264 = lean_ctor_get(x_40, 14);
lean_inc(x_264);
x_265 = lean_ctor_get(x_40, 15);
lean_inc(x_265);
x_266 = lean_ctor_get_uint8(x_40, sizeof(void*)*21);
x_267 = lean_ctor_get(x_40, 16);
lean_inc(x_267);
x_268 = lean_ctor_get(x_40, 17);
lean_inc(x_268);
x_269 = lean_ctor_get(x_40, 18);
lean_inc(x_269);
x_270 = lean_ctor_get(x_40, 19);
lean_inc(x_270);
x_271 = lean_ctor_get(x_40, 20);
lean_inc(x_271);
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
 x_272 = x_40;
} else {
 lean_dec_ref(x_40);
 x_272 = lean_box(0);
}
lean_inc(x_1);
x_273 = l_Lean_PersistentArray_push___redArg(x_250, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_274 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_251, x_1, x_27);
x_275 = lean_box(0);
x_276 = l_Lean_PersistentArray_push___redArg(x_257, x_275);
x_277 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_278 = l_Lean_PersistentArray_push___redArg(x_258, x_277);
x_279 = l_Lean_PersistentArray_push___redArg(x_259, x_277);
x_280 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_281 = l_Lean_PersistentArray_push___redArg(x_260, x_280);
x_282 = lean_box(0);
x_283 = l_Lean_PersistentArray_push___redArg(x_261, x_282);
x_284 = lean_box(0);
x_285 = l_Lean_PersistentArray_push___redArg(x_263, x_284);
if (lean_is_scalar(x_272)) {
 x_286 = lean_alloc_ctor(0, 21, 1);
} else {
 x_286 = x_272;
}
lean_ctor_set(x_286, 0, x_273);
lean_ctor_set(x_286, 1, x_274);
lean_ctor_set(x_286, 2, x_252);
lean_ctor_set(x_286, 3, x_253);
lean_ctor_set(x_286, 4, x_254);
lean_ctor_set(x_286, 5, x_255);
lean_ctor_set(x_286, 6, x_256);
lean_ctor_set(x_286, 7, x_276);
lean_ctor_set(x_286, 8, x_278);
lean_ctor_set(x_286, 9, x_279);
lean_ctor_set(x_286, 10, x_281);
lean_ctor_set(x_286, 11, x_283);
lean_ctor_set(x_286, 12, x_262);
lean_ctor_set(x_286, 13, x_285);
lean_ctor_set(x_286, 14, x_264);
lean_ctor_set(x_286, 15, x_265);
lean_ctor_set(x_286, 16, x_267);
lean_ctor_set(x_286, 17, x_268);
lean_ctor_set(x_286, 18, x_269);
lean_ctor_set(x_286, 19, x_270);
lean_ctor_set(x_286, 20, x_271);
lean_ctor_set_uint8(x_286, sizeof(void*)*21, x_266);
if (lean_is_scalar(x_249)) {
 x_287 = lean_alloc_ctor(0, 4, 0);
} else {
 x_287 = x_249;
}
lean_ctor_set(x_287, 0, x_246);
lean_ctor_set(x_287, 1, x_286);
lean_ctor_set(x_287, 2, x_247);
lean_ctor_set(x_287, 3, x_248);
x_288 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_288, 0, x_230);
lean_ctor_set(x_288, 1, x_231);
lean_ctor_set(x_288, 2, x_232);
lean_ctor_set(x_288, 3, x_233);
lean_ctor_set(x_288, 4, x_234);
lean_ctor_set(x_288, 5, x_235);
lean_ctor_set(x_288, 6, x_236);
lean_ctor_set(x_288, 7, x_237);
lean_ctor_set(x_288, 8, x_239);
lean_ctor_set(x_288, 9, x_240);
lean_ctor_set(x_288, 10, x_241);
lean_ctor_set(x_288, 11, x_242);
lean_ctor_set(x_288, 12, x_243);
lean_ctor_set(x_288, 13, x_244);
lean_ctor_set(x_288, 14, x_287);
lean_ctor_set(x_288, 15, x_245);
lean_ctor_set_uint8(x_288, sizeof(void*)*16, x_238);
x_289 = lean_st_ref_set(x_28, x_288, x_41);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_291 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec(x_291);
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
x_293 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_292);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_293, 1);
lean_inc(x_294);
lean_dec(x_293);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_295 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_294);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
lean_inc(x_27);
x_297 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_296);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_299 = x_297;
} else {
 lean_dec_ref(x_297);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(0, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_27);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_27);
x_301 = lean_ctor_get(x_297, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_297, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_303 = x_297;
} else {
 lean_dec_ref(x_297);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
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
x_305 = lean_ctor_get(x_295, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_295, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 lean_ctor_release(x_295, 1);
 x_307 = x_295;
} else {
 lean_dec_ref(x_295);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_306);
return x_308;
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
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
x_309 = lean_ctor_get(x_293, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_293, 1);
lean_inc(x_310);
if (lean_is_exclusive(x_293)) {
 lean_ctor_release(x_293, 0);
 lean_ctor_release(x_293, 1);
 x_311 = x_293;
} else {
 lean_dec_ref(x_293);
 x_311 = lean_box(0);
}
if (lean_is_scalar(x_311)) {
 x_312 = lean_alloc_ctor(1, 2, 0);
} else {
 x_312 = x_311;
}
lean_ctor_set(x_312, 0, x_309);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
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
x_313 = lean_ctor_get(x_291, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_291, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_315 = x_291;
} else {
 lean_dec_ref(x_291);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 2, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_313);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; uint8_t x_435; 
x_329 = lean_ctor_get(x_22, 0);
x_330 = lean_ctor_get(x_22, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_22);
x_331 = lean_ctor_get(x_23, 2);
lean_inc(x_331);
lean_dec(x_23);
x_435 = lean_unbox(x_329);
lean_dec(x_329);
if (x_435 == 0)
{
lean_free_object(x_17);
x_332 = x_2;
x_333 = x_3;
x_334 = x_4;
x_335 = x_5;
x_336 = x_6;
x_337 = x_7;
x_338 = x_8;
x_339 = x_9;
x_340 = x_330;
goto block_434;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_436 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_437 = l_Lean_MessageData_ofExpr(x_1);
x_438 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
x_439 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_439);
lean_ctor_set(x_17, 0, x_438);
lean_inc(x_331);
x_440 = l_Nat_reprFast(x_331);
x_441 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_441, 0, x_440);
x_442 = l_Lean_MessageData_ofFormat(x_441);
x_443 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_443, 0, x_17);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_436);
x_445 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_444, x_6, x_7, x_8, x_9, x_330);
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
lean_dec(x_445);
x_332 = x_2;
x_333 = x_3;
x_334 = x_4;
x_335 = x_5;
x_336 = x_6;
x_337 = x_7;
x_338 = x_8;
x_339 = x_9;
x_340 = x_446;
goto block_434;
}
block_434:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_341 = lean_st_ref_take(x_332, x_340);
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_342, 14);
lean_inc(x_343);
x_344 = lean_ctor_get(x_343, 1);
lean_inc(x_344);
x_345 = lean_ctor_get(x_341, 1);
lean_inc(x_345);
lean_dec(x_341);
x_346 = lean_ctor_get(x_342, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_342, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_342, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_342, 3);
lean_inc(x_349);
x_350 = lean_ctor_get(x_342, 4);
lean_inc(x_350);
x_351 = lean_ctor_get(x_342, 5);
lean_inc(x_351);
x_352 = lean_ctor_get(x_342, 6);
lean_inc(x_352);
x_353 = lean_ctor_get(x_342, 7);
lean_inc(x_353);
x_354 = lean_ctor_get_uint8(x_342, sizeof(void*)*16);
x_355 = lean_ctor_get(x_342, 8);
lean_inc(x_355);
x_356 = lean_ctor_get(x_342, 9);
lean_inc(x_356);
x_357 = lean_ctor_get(x_342, 10);
lean_inc(x_357);
x_358 = lean_ctor_get(x_342, 11);
lean_inc(x_358);
x_359 = lean_ctor_get(x_342, 12);
lean_inc(x_359);
x_360 = lean_ctor_get(x_342, 13);
lean_inc(x_360);
x_361 = lean_ctor_get(x_342, 15);
lean_inc(x_361);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 lean_ctor_release(x_342, 4);
 lean_ctor_release(x_342, 5);
 lean_ctor_release(x_342, 6);
 lean_ctor_release(x_342, 7);
 lean_ctor_release(x_342, 8);
 lean_ctor_release(x_342, 9);
 lean_ctor_release(x_342, 10);
 lean_ctor_release(x_342, 11);
 lean_ctor_release(x_342, 12);
 lean_ctor_release(x_342, 13);
 lean_ctor_release(x_342, 14);
 lean_ctor_release(x_342, 15);
 x_362 = x_342;
} else {
 lean_dec_ref(x_342);
 x_362 = lean_box(0);
}
x_363 = lean_ctor_get(x_343, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_343, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_343, 3);
lean_inc(x_365);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 x_366 = x_343;
} else {
 lean_dec_ref(x_343);
 x_366 = lean_box(0);
}
x_367 = lean_ctor_get(x_344, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_344, 1);
lean_inc(x_368);
x_369 = lean_ctor_get(x_344, 2);
lean_inc(x_369);
x_370 = lean_ctor_get(x_344, 3);
lean_inc(x_370);
x_371 = lean_ctor_get(x_344, 4);
lean_inc(x_371);
x_372 = lean_ctor_get(x_344, 5);
lean_inc(x_372);
x_373 = lean_ctor_get(x_344, 6);
lean_inc(x_373);
x_374 = lean_ctor_get(x_344, 7);
lean_inc(x_374);
x_375 = lean_ctor_get(x_344, 8);
lean_inc(x_375);
x_376 = lean_ctor_get(x_344, 9);
lean_inc(x_376);
x_377 = lean_ctor_get(x_344, 10);
lean_inc(x_377);
x_378 = lean_ctor_get(x_344, 11);
lean_inc(x_378);
x_379 = lean_ctor_get(x_344, 12);
lean_inc(x_379);
x_380 = lean_ctor_get(x_344, 13);
lean_inc(x_380);
x_381 = lean_ctor_get(x_344, 14);
lean_inc(x_381);
x_382 = lean_ctor_get(x_344, 15);
lean_inc(x_382);
x_383 = lean_ctor_get_uint8(x_344, sizeof(void*)*21);
x_384 = lean_ctor_get(x_344, 16);
lean_inc(x_384);
x_385 = lean_ctor_get(x_344, 17);
lean_inc(x_385);
x_386 = lean_ctor_get(x_344, 18);
lean_inc(x_386);
x_387 = lean_ctor_get(x_344, 19);
lean_inc(x_387);
x_388 = lean_ctor_get(x_344, 20);
lean_inc(x_388);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 lean_ctor_release(x_344, 2);
 lean_ctor_release(x_344, 3);
 lean_ctor_release(x_344, 4);
 lean_ctor_release(x_344, 5);
 lean_ctor_release(x_344, 6);
 lean_ctor_release(x_344, 7);
 lean_ctor_release(x_344, 8);
 lean_ctor_release(x_344, 9);
 lean_ctor_release(x_344, 10);
 lean_ctor_release(x_344, 11);
 lean_ctor_release(x_344, 12);
 lean_ctor_release(x_344, 13);
 lean_ctor_release(x_344, 14);
 lean_ctor_release(x_344, 15);
 lean_ctor_release(x_344, 16);
 lean_ctor_release(x_344, 17);
 lean_ctor_release(x_344, 18);
 lean_ctor_release(x_344, 19);
 lean_ctor_release(x_344, 20);
 x_389 = x_344;
} else {
 lean_dec_ref(x_344);
 x_389 = lean_box(0);
}
lean_inc(x_1);
x_390 = l_Lean_PersistentArray_push___redArg(x_367, x_1);
lean_inc(x_331);
lean_inc(x_1);
x_391 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_368, x_1, x_331);
x_392 = lean_box(0);
x_393 = l_Lean_PersistentArray_push___redArg(x_374, x_392);
x_394 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_395 = l_Lean_PersistentArray_push___redArg(x_375, x_394);
x_396 = l_Lean_PersistentArray_push___redArg(x_376, x_394);
x_397 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_398 = l_Lean_PersistentArray_push___redArg(x_377, x_397);
x_399 = lean_box(0);
x_400 = l_Lean_PersistentArray_push___redArg(x_378, x_399);
x_401 = lean_box(0);
x_402 = l_Lean_PersistentArray_push___redArg(x_380, x_401);
if (lean_is_scalar(x_389)) {
 x_403 = lean_alloc_ctor(0, 21, 1);
} else {
 x_403 = x_389;
}
lean_ctor_set(x_403, 0, x_390);
lean_ctor_set(x_403, 1, x_391);
lean_ctor_set(x_403, 2, x_369);
lean_ctor_set(x_403, 3, x_370);
lean_ctor_set(x_403, 4, x_371);
lean_ctor_set(x_403, 5, x_372);
lean_ctor_set(x_403, 6, x_373);
lean_ctor_set(x_403, 7, x_393);
lean_ctor_set(x_403, 8, x_395);
lean_ctor_set(x_403, 9, x_396);
lean_ctor_set(x_403, 10, x_398);
lean_ctor_set(x_403, 11, x_400);
lean_ctor_set(x_403, 12, x_379);
lean_ctor_set(x_403, 13, x_402);
lean_ctor_set(x_403, 14, x_381);
lean_ctor_set(x_403, 15, x_382);
lean_ctor_set(x_403, 16, x_384);
lean_ctor_set(x_403, 17, x_385);
lean_ctor_set(x_403, 18, x_386);
lean_ctor_set(x_403, 19, x_387);
lean_ctor_set(x_403, 20, x_388);
lean_ctor_set_uint8(x_403, sizeof(void*)*21, x_383);
if (lean_is_scalar(x_366)) {
 x_404 = lean_alloc_ctor(0, 4, 0);
} else {
 x_404 = x_366;
}
lean_ctor_set(x_404, 0, x_363);
lean_ctor_set(x_404, 1, x_403);
lean_ctor_set(x_404, 2, x_364);
lean_ctor_set(x_404, 3, x_365);
if (lean_is_scalar(x_362)) {
 x_405 = lean_alloc_ctor(0, 16, 1);
} else {
 x_405 = x_362;
}
lean_ctor_set(x_405, 0, x_346);
lean_ctor_set(x_405, 1, x_347);
lean_ctor_set(x_405, 2, x_348);
lean_ctor_set(x_405, 3, x_349);
lean_ctor_set(x_405, 4, x_350);
lean_ctor_set(x_405, 5, x_351);
lean_ctor_set(x_405, 6, x_352);
lean_ctor_set(x_405, 7, x_353);
lean_ctor_set(x_405, 8, x_355);
lean_ctor_set(x_405, 9, x_356);
lean_ctor_set(x_405, 10, x_357);
lean_ctor_set(x_405, 11, x_358);
lean_ctor_set(x_405, 12, x_359);
lean_ctor_set(x_405, 13, x_360);
lean_ctor_set(x_405, 14, x_404);
lean_ctor_set(x_405, 15, x_361);
lean_ctor_set_uint8(x_405, sizeof(void*)*16, x_354);
x_406 = lean_st_ref_set(x_332, x_405, x_345);
x_407 = lean_ctor_get(x_406, 1);
lean_inc(x_407);
lean_dec(x_406);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_1);
x_408 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_332, x_333, x_334, x_335, x_336, x_337, x_338, x_339, x_407);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; 
x_409 = lean_ctor_get(x_408, 1);
lean_inc(x_409);
lean_dec(x_408);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_1);
x_410 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_331, x_332, x_333, x_334, x_335, x_336, x_337, x_338, x_339, x_409);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; 
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_1);
x_412 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_332, x_333, x_334, x_335, x_336, x_337, x_338, x_339, x_411);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_412, 1);
lean_inc(x_413);
lean_dec(x_412);
lean_inc(x_331);
x_414 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_331, x_332, x_333, x_334, x_335, x_336, x_337, x_338, x_339, x_413);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_414, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_416 = x_414;
} else {
 lean_dec_ref(x_414);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(0, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_331);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_331);
x_418 = lean_ctor_get(x_414, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_414, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 lean_ctor_release(x_414, 1);
 x_420 = x_414;
} else {
 lean_dec_ref(x_414);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_1);
x_422 = lean_ctor_get(x_412, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_412, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_424 = x_412;
} else {
 lean_dec_ref(x_412);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_1);
x_426 = lean_ctor_get(x_410, 0);
lean_inc(x_426);
x_427 = lean_ctor_get(x_410, 1);
lean_inc(x_427);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_428 = x_410;
} else {
 lean_dec_ref(x_410);
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
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_1);
x_430 = lean_ctor_get(x_408, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_408, 1);
lean_inc(x_431);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_432 = x_408;
} else {
 lean_dec_ref(x_408);
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
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_559; 
x_447 = lean_ctor_get(x_17, 0);
x_448 = lean_ctor_get(x_17, 1);
lean_inc(x_448);
lean_inc(x_447);
lean_dec(x_17);
x_449 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_450 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_449, x_8, x_448);
x_451 = lean_ctor_get(x_447, 0);
lean_inc(x_451);
lean_dec(x_447);
x_452 = lean_ctor_get(x_450, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_454 = x_450;
} else {
 lean_dec_ref(x_450);
 x_454 = lean_box(0);
}
x_455 = lean_ctor_get(x_451, 2);
lean_inc(x_455);
lean_dec(x_451);
x_559 = lean_unbox(x_452);
lean_dec(x_452);
if (x_559 == 0)
{
lean_dec(x_454);
x_456 = x_2;
x_457 = x_3;
x_458 = x_4;
x_459 = x_5;
x_460 = x_6;
x_461 = x_7;
x_462 = x_8;
x_463 = x_9;
x_464 = x_453;
goto block_558;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
x_560 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_561 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_454)) {
 x_562 = lean_alloc_ctor(7, 2, 0);
} else {
 x_562 = x_454;
 lean_ctor_set_tag(x_562, 7);
}
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
x_563 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
x_564 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
lean_inc(x_455);
x_565 = l_Nat_reprFast(x_455);
x_566 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_566, 0, x_565);
x_567 = l_Lean_MessageData_ofFormat(x_566);
x_568 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_568, 0, x_564);
lean_ctor_set(x_568, 1, x_567);
x_569 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_569, 0, x_568);
lean_ctor_set(x_569, 1, x_560);
x_570 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_449, x_569, x_6, x_7, x_8, x_9, x_453);
x_571 = lean_ctor_get(x_570, 1);
lean_inc(x_571);
lean_dec(x_570);
x_456 = x_2;
x_457 = x_3;
x_458 = x_4;
x_459 = x_5;
x_460 = x_6;
x_461 = x_7;
x_462 = x_8;
x_463 = x_9;
x_464 = x_571;
goto block_558;
}
block_558:
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; uint8_t x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; uint8_t x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_465 = lean_st_ref_take(x_456, x_464);
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_466, 14);
lean_inc(x_467);
x_468 = lean_ctor_get(x_467, 1);
lean_inc(x_468);
x_469 = lean_ctor_get(x_465, 1);
lean_inc(x_469);
lean_dec(x_465);
x_470 = lean_ctor_get(x_466, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_466, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_466, 2);
lean_inc(x_472);
x_473 = lean_ctor_get(x_466, 3);
lean_inc(x_473);
x_474 = lean_ctor_get(x_466, 4);
lean_inc(x_474);
x_475 = lean_ctor_get(x_466, 5);
lean_inc(x_475);
x_476 = lean_ctor_get(x_466, 6);
lean_inc(x_476);
x_477 = lean_ctor_get(x_466, 7);
lean_inc(x_477);
x_478 = lean_ctor_get_uint8(x_466, sizeof(void*)*16);
x_479 = lean_ctor_get(x_466, 8);
lean_inc(x_479);
x_480 = lean_ctor_get(x_466, 9);
lean_inc(x_480);
x_481 = lean_ctor_get(x_466, 10);
lean_inc(x_481);
x_482 = lean_ctor_get(x_466, 11);
lean_inc(x_482);
x_483 = lean_ctor_get(x_466, 12);
lean_inc(x_483);
x_484 = lean_ctor_get(x_466, 13);
lean_inc(x_484);
x_485 = lean_ctor_get(x_466, 15);
lean_inc(x_485);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 lean_ctor_release(x_466, 2);
 lean_ctor_release(x_466, 3);
 lean_ctor_release(x_466, 4);
 lean_ctor_release(x_466, 5);
 lean_ctor_release(x_466, 6);
 lean_ctor_release(x_466, 7);
 lean_ctor_release(x_466, 8);
 lean_ctor_release(x_466, 9);
 lean_ctor_release(x_466, 10);
 lean_ctor_release(x_466, 11);
 lean_ctor_release(x_466, 12);
 lean_ctor_release(x_466, 13);
 lean_ctor_release(x_466, 14);
 lean_ctor_release(x_466, 15);
 x_486 = x_466;
} else {
 lean_dec_ref(x_466);
 x_486 = lean_box(0);
}
x_487 = lean_ctor_get(x_467, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_467, 2);
lean_inc(x_488);
x_489 = lean_ctor_get(x_467, 3);
lean_inc(x_489);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 lean_ctor_release(x_467, 2);
 lean_ctor_release(x_467, 3);
 x_490 = x_467;
} else {
 lean_dec_ref(x_467);
 x_490 = lean_box(0);
}
x_491 = lean_ctor_get(x_468, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_468, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_468, 2);
lean_inc(x_493);
x_494 = lean_ctor_get(x_468, 3);
lean_inc(x_494);
x_495 = lean_ctor_get(x_468, 4);
lean_inc(x_495);
x_496 = lean_ctor_get(x_468, 5);
lean_inc(x_496);
x_497 = lean_ctor_get(x_468, 6);
lean_inc(x_497);
x_498 = lean_ctor_get(x_468, 7);
lean_inc(x_498);
x_499 = lean_ctor_get(x_468, 8);
lean_inc(x_499);
x_500 = lean_ctor_get(x_468, 9);
lean_inc(x_500);
x_501 = lean_ctor_get(x_468, 10);
lean_inc(x_501);
x_502 = lean_ctor_get(x_468, 11);
lean_inc(x_502);
x_503 = lean_ctor_get(x_468, 12);
lean_inc(x_503);
x_504 = lean_ctor_get(x_468, 13);
lean_inc(x_504);
x_505 = lean_ctor_get(x_468, 14);
lean_inc(x_505);
x_506 = lean_ctor_get(x_468, 15);
lean_inc(x_506);
x_507 = lean_ctor_get_uint8(x_468, sizeof(void*)*21);
x_508 = lean_ctor_get(x_468, 16);
lean_inc(x_508);
x_509 = lean_ctor_get(x_468, 17);
lean_inc(x_509);
x_510 = lean_ctor_get(x_468, 18);
lean_inc(x_510);
x_511 = lean_ctor_get(x_468, 19);
lean_inc(x_511);
x_512 = lean_ctor_get(x_468, 20);
lean_inc(x_512);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 lean_ctor_release(x_468, 2);
 lean_ctor_release(x_468, 3);
 lean_ctor_release(x_468, 4);
 lean_ctor_release(x_468, 5);
 lean_ctor_release(x_468, 6);
 lean_ctor_release(x_468, 7);
 lean_ctor_release(x_468, 8);
 lean_ctor_release(x_468, 9);
 lean_ctor_release(x_468, 10);
 lean_ctor_release(x_468, 11);
 lean_ctor_release(x_468, 12);
 lean_ctor_release(x_468, 13);
 lean_ctor_release(x_468, 14);
 lean_ctor_release(x_468, 15);
 lean_ctor_release(x_468, 16);
 lean_ctor_release(x_468, 17);
 lean_ctor_release(x_468, 18);
 lean_ctor_release(x_468, 19);
 lean_ctor_release(x_468, 20);
 x_513 = x_468;
} else {
 lean_dec_ref(x_468);
 x_513 = lean_box(0);
}
lean_inc(x_1);
x_514 = l_Lean_PersistentArray_push___redArg(x_491, x_1);
lean_inc(x_455);
lean_inc(x_1);
x_515 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_492, x_1, x_455);
x_516 = lean_box(0);
x_517 = l_Lean_PersistentArray_push___redArg(x_498, x_516);
x_518 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_519 = l_Lean_PersistentArray_push___redArg(x_499, x_518);
x_520 = l_Lean_PersistentArray_push___redArg(x_500, x_518);
x_521 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_522 = l_Lean_PersistentArray_push___redArg(x_501, x_521);
x_523 = lean_box(0);
x_524 = l_Lean_PersistentArray_push___redArg(x_502, x_523);
x_525 = lean_box(0);
x_526 = l_Lean_PersistentArray_push___redArg(x_504, x_525);
if (lean_is_scalar(x_513)) {
 x_527 = lean_alloc_ctor(0, 21, 1);
} else {
 x_527 = x_513;
}
lean_ctor_set(x_527, 0, x_514);
lean_ctor_set(x_527, 1, x_515);
lean_ctor_set(x_527, 2, x_493);
lean_ctor_set(x_527, 3, x_494);
lean_ctor_set(x_527, 4, x_495);
lean_ctor_set(x_527, 5, x_496);
lean_ctor_set(x_527, 6, x_497);
lean_ctor_set(x_527, 7, x_517);
lean_ctor_set(x_527, 8, x_519);
lean_ctor_set(x_527, 9, x_520);
lean_ctor_set(x_527, 10, x_522);
lean_ctor_set(x_527, 11, x_524);
lean_ctor_set(x_527, 12, x_503);
lean_ctor_set(x_527, 13, x_526);
lean_ctor_set(x_527, 14, x_505);
lean_ctor_set(x_527, 15, x_506);
lean_ctor_set(x_527, 16, x_508);
lean_ctor_set(x_527, 17, x_509);
lean_ctor_set(x_527, 18, x_510);
lean_ctor_set(x_527, 19, x_511);
lean_ctor_set(x_527, 20, x_512);
lean_ctor_set_uint8(x_527, sizeof(void*)*21, x_507);
if (lean_is_scalar(x_490)) {
 x_528 = lean_alloc_ctor(0, 4, 0);
} else {
 x_528 = x_490;
}
lean_ctor_set(x_528, 0, x_487);
lean_ctor_set(x_528, 1, x_527);
lean_ctor_set(x_528, 2, x_488);
lean_ctor_set(x_528, 3, x_489);
if (lean_is_scalar(x_486)) {
 x_529 = lean_alloc_ctor(0, 16, 1);
} else {
 x_529 = x_486;
}
lean_ctor_set(x_529, 0, x_470);
lean_ctor_set(x_529, 1, x_471);
lean_ctor_set(x_529, 2, x_472);
lean_ctor_set(x_529, 3, x_473);
lean_ctor_set(x_529, 4, x_474);
lean_ctor_set(x_529, 5, x_475);
lean_ctor_set(x_529, 6, x_476);
lean_ctor_set(x_529, 7, x_477);
lean_ctor_set(x_529, 8, x_479);
lean_ctor_set(x_529, 9, x_480);
lean_ctor_set(x_529, 10, x_481);
lean_ctor_set(x_529, 11, x_482);
lean_ctor_set(x_529, 12, x_483);
lean_ctor_set(x_529, 13, x_484);
lean_ctor_set(x_529, 14, x_528);
lean_ctor_set(x_529, 15, x_485);
lean_ctor_set_uint8(x_529, sizeof(void*)*16, x_478);
x_530 = lean_st_ref_set(x_456, x_529, x_469);
x_531 = lean_ctor_get(x_530, 1);
lean_inc(x_531);
lean_dec(x_530);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_1);
x_532 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_456, x_457, x_458, x_459, x_460, x_461, x_462, x_463, x_531);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; 
x_533 = lean_ctor_get(x_532, 1);
lean_inc(x_533);
lean_dec(x_532);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_455);
lean_inc(x_1);
x_534 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_455, x_456, x_457, x_458, x_459, x_460, x_461, x_462, x_463, x_533);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; 
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
lean_dec(x_534);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_inc(x_459);
lean_inc(x_458);
lean_inc(x_457);
lean_inc(x_456);
lean_inc(x_1);
x_536 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_456, x_457, x_458, x_459, x_460, x_461, x_462, x_463, x_535);
if (lean_obj_tag(x_536) == 0)
{
lean_object* x_537; lean_object* x_538; 
x_537 = lean_ctor_get(x_536, 1);
lean_inc(x_537);
lean_dec(x_536);
lean_inc(x_455);
x_538 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_455, x_456, x_457, x_458, x_459, x_460, x_461, x_462, x_463, x_537);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_539 = lean_ctor_get(x_538, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_540 = x_538;
} else {
 lean_dec_ref(x_538);
 x_540 = lean_box(0);
}
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(0, 2, 0);
} else {
 x_541 = x_540;
}
lean_ctor_set(x_541, 0, x_455);
lean_ctor_set(x_541, 1, x_539);
return x_541;
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_455);
x_542 = lean_ctor_get(x_538, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_538, 1);
lean_inc(x_543);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_544 = x_538;
} else {
 lean_dec_ref(x_538);
 x_544 = lean_box(0);
}
if (lean_is_scalar(x_544)) {
 x_545 = lean_alloc_ctor(1, 2, 0);
} else {
 x_545 = x_544;
}
lean_ctor_set(x_545, 0, x_542);
lean_ctor_set(x_545, 1, x_543);
return x_545;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_1);
x_546 = lean_ctor_get(x_536, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_536, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 lean_ctor_release(x_536, 1);
 x_548 = x_536;
} else {
 lean_dec_ref(x_536);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_549 = x_548;
}
lean_ctor_set(x_549, 0, x_546);
lean_ctor_set(x_549, 1, x_547);
return x_549;
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_1);
x_550 = lean_ctor_get(x_534, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_534, 1);
lean_inc(x_551);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_552 = x_534;
} else {
 lean_dec_ref(x_534);
 x_552 = lean_box(0);
}
if (lean_is_scalar(x_552)) {
 x_553 = lean_alloc_ctor(1, 2, 0);
} else {
 x_553 = x_552;
}
lean_ctor_set(x_553, 0, x_550);
lean_ctor_set(x_553, 1, x_551);
return x_553;
}
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_463);
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_460);
lean_dec(x_459);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_1);
x_554 = lean_ctor_get(x_532, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_532, 1);
lean_inc(x_555);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_556 = x_532;
} else {
 lean_dec_ref(x_532);
 x_556 = lean_box(0);
}
if (lean_is_scalar(x_556)) {
 x_557 = lean_alloc_ctor(1, 2, 0);
} else {
 x_557 = x_556;
}
lean_ctor_set(x_557, 0, x_554);
lean_ctor_set(x_557, 1, x_555);
return x_557;
}
}
}
}
else
{
lean_object* x_572; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_572 = lean_ctor_get(x_16, 0);
lean_inc(x_572);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_572);
return x_11;
}
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_573 = lean_ctor_get(x_11, 0);
x_574 = lean_ctor_get(x_11, 1);
lean_inc(x_574);
lean_inc(x_573);
lean_dec(x_11);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
lean_inc(x_1);
x_576 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_575, x_1);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_691; 
x_577 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_574);
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
if (lean_is_exclusive(x_577)) {
 lean_ctor_release(x_577, 0);
 lean_ctor_release(x_577, 1);
 x_580 = x_577;
} else {
 lean_dec_ref(x_577);
 x_580 = lean_box(0);
}
x_581 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_582 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_581, x_8, x_579);
x_583 = lean_ctor_get(x_578, 0);
lean_inc(x_583);
lean_dec(x_578);
x_584 = lean_ctor_get(x_582, 0);
lean_inc(x_584);
x_585 = lean_ctor_get(x_582, 1);
lean_inc(x_585);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_586 = x_582;
} else {
 lean_dec_ref(x_582);
 x_586 = lean_box(0);
}
x_587 = lean_ctor_get(x_583, 2);
lean_inc(x_587);
lean_dec(x_583);
x_691 = lean_unbox(x_584);
lean_dec(x_584);
if (x_691 == 0)
{
lean_dec(x_586);
lean_dec(x_580);
x_588 = x_2;
x_589 = x_3;
x_590 = x_4;
x_591 = x_5;
x_592 = x_6;
x_593 = x_7;
x_594 = x_8;
x_595 = x_9;
x_596 = x_585;
goto block_690;
}
else
{
lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_692 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_693 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_586)) {
 x_694 = lean_alloc_ctor(7, 2, 0);
} else {
 x_694 = x_586;
 lean_ctor_set_tag(x_694, 7);
}
lean_ctor_set(x_694, 0, x_692);
lean_ctor_set(x_694, 1, x_693);
x_695 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
if (lean_is_scalar(x_580)) {
 x_696 = lean_alloc_ctor(7, 2, 0);
} else {
 x_696 = x_580;
 lean_ctor_set_tag(x_696, 7);
}
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
lean_inc(x_587);
x_697 = l_Nat_reprFast(x_587);
x_698 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_698, 0, x_697);
x_699 = l_Lean_MessageData_ofFormat(x_698);
x_700 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_700, 0, x_696);
lean_ctor_set(x_700, 1, x_699);
x_701 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_701, 0, x_700);
lean_ctor_set(x_701, 1, x_692);
x_702 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_581, x_701, x_6, x_7, x_8, x_9, x_585);
x_703 = lean_ctor_get(x_702, 1);
lean_inc(x_703);
lean_dec(x_702);
x_588 = x_2;
x_589 = x_3;
x_590 = x_4;
x_591 = x_5;
x_592 = x_6;
x_593 = x_7;
x_594 = x_8;
x_595 = x_9;
x_596 = x_703;
goto block_690;
}
block_690:
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; uint8_t x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_597 = lean_st_ref_take(x_588, x_596);
x_598 = lean_ctor_get(x_597, 0);
lean_inc(x_598);
x_599 = lean_ctor_get(x_598, 14);
lean_inc(x_599);
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
x_601 = lean_ctor_get(x_597, 1);
lean_inc(x_601);
lean_dec(x_597);
x_602 = lean_ctor_get(x_598, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_598, 1);
lean_inc(x_603);
x_604 = lean_ctor_get(x_598, 2);
lean_inc(x_604);
x_605 = lean_ctor_get(x_598, 3);
lean_inc(x_605);
x_606 = lean_ctor_get(x_598, 4);
lean_inc(x_606);
x_607 = lean_ctor_get(x_598, 5);
lean_inc(x_607);
x_608 = lean_ctor_get(x_598, 6);
lean_inc(x_608);
x_609 = lean_ctor_get(x_598, 7);
lean_inc(x_609);
x_610 = lean_ctor_get_uint8(x_598, sizeof(void*)*16);
x_611 = lean_ctor_get(x_598, 8);
lean_inc(x_611);
x_612 = lean_ctor_get(x_598, 9);
lean_inc(x_612);
x_613 = lean_ctor_get(x_598, 10);
lean_inc(x_613);
x_614 = lean_ctor_get(x_598, 11);
lean_inc(x_614);
x_615 = lean_ctor_get(x_598, 12);
lean_inc(x_615);
x_616 = lean_ctor_get(x_598, 13);
lean_inc(x_616);
x_617 = lean_ctor_get(x_598, 15);
lean_inc(x_617);
if (lean_is_exclusive(x_598)) {
 lean_ctor_release(x_598, 0);
 lean_ctor_release(x_598, 1);
 lean_ctor_release(x_598, 2);
 lean_ctor_release(x_598, 3);
 lean_ctor_release(x_598, 4);
 lean_ctor_release(x_598, 5);
 lean_ctor_release(x_598, 6);
 lean_ctor_release(x_598, 7);
 lean_ctor_release(x_598, 8);
 lean_ctor_release(x_598, 9);
 lean_ctor_release(x_598, 10);
 lean_ctor_release(x_598, 11);
 lean_ctor_release(x_598, 12);
 lean_ctor_release(x_598, 13);
 lean_ctor_release(x_598, 14);
 lean_ctor_release(x_598, 15);
 x_618 = x_598;
} else {
 lean_dec_ref(x_598);
 x_618 = lean_box(0);
}
x_619 = lean_ctor_get(x_599, 0);
lean_inc(x_619);
x_620 = lean_ctor_get(x_599, 2);
lean_inc(x_620);
x_621 = lean_ctor_get(x_599, 3);
lean_inc(x_621);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 lean_ctor_release(x_599, 2);
 lean_ctor_release(x_599, 3);
 x_622 = x_599;
} else {
 lean_dec_ref(x_599);
 x_622 = lean_box(0);
}
x_623 = lean_ctor_get(x_600, 0);
lean_inc(x_623);
x_624 = lean_ctor_get(x_600, 1);
lean_inc(x_624);
x_625 = lean_ctor_get(x_600, 2);
lean_inc(x_625);
x_626 = lean_ctor_get(x_600, 3);
lean_inc(x_626);
x_627 = lean_ctor_get(x_600, 4);
lean_inc(x_627);
x_628 = lean_ctor_get(x_600, 5);
lean_inc(x_628);
x_629 = lean_ctor_get(x_600, 6);
lean_inc(x_629);
x_630 = lean_ctor_get(x_600, 7);
lean_inc(x_630);
x_631 = lean_ctor_get(x_600, 8);
lean_inc(x_631);
x_632 = lean_ctor_get(x_600, 9);
lean_inc(x_632);
x_633 = lean_ctor_get(x_600, 10);
lean_inc(x_633);
x_634 = lean_ctor_get(x_600, 11);
lean_inc(x_634);
x_635 = lean_ctor_get(x_600, 12);
lean_inc(x_635);
x_636 = lean_ctor_get(x_600, 13);
lean_inc(x_636);
x_637 = lean_ctor_get(x_600, 14);
lean_inc(x_637);
x_638 = lean_ctor_get(x_600, 15);
lean_inc(x_638);
x_639 = lean_ctor_get_uint8(x_600, sizeof(void*)*21);
x_640 = lean_ctor_get(x_600, 16);
lean_inc(x_640);
x_641 = lean_ctor_get(x_600, 17);
lean_inc(x_641);
x_642 = lean_ctor_get(x_600, 18);
lean_inc(x_642);
x_643 = lean_ctor_get(x_600, 19);
lean_inc(x_643);
x_644 = lean_ctor_get(x_600, 20);
lean_inc(x_644);
if (lean_is_exclusive(x_600)) {
 lean_ctor_release(x_600, 0);
 lean_ctor_release(x_600, 1);
 lean_ctor_release(x_600, 2);
 lean_ctor_release(x_600, 3);
 lean_ctor_release(x_600, 4);
 lean_ctor_release(x_600, 5);
 lean_ctor_release(x_600, 6);
 lean_ctor_release(x_600, 7);
 lean_ctor_release(x_600, 8);
 lean_ctor_release(x_600, 9);
 lean_ctor_release(x_600, 10);
 lean_ctor_release(x_600, 11);
 lean_ctor_release(x_600, 12);
 lean_ctor_release(x_600, 13);
 lean_ctor_release(x_600, 14);
 lean_ctor_release(x_600, 15);
 lean_ctor_release(x_600, 16);
 lean_ctor_release(x_600, 17);
 lean_ctor_release(x_600, 18);
 lean_ctor_release(x_600, 19);
 lean_ctor_release(x_600, 20);
 x_645 = x_600;
} else {
 lean_dec_ref(x_600);
 x_645 = lean_box(0);
}
lean_inc(x_1);
x_646 = l_Lean_PersistentArray_push___redArg(x_623, x_1);
lean_inc(x_587);
lean_inc(x_1);
x_647 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_624, x_1, x_587);
x_648 = lean_box(0);
x_649 = l_Lean_PersistentArray_push___redArg(x_630, x_648);
x_650 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_651 = l_Lean_PersistentArray_push___redArg(x_631, x_650);
x_652 = l_Lean_PersistentArray_push___redArg(x_632, x_650);
x_653 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_654 = l_Lean_PersistentArray_push___redArg(x_633, x_653);
x_655 = lean_box(0);
x_656 = l_Lean_PersistentArray_push___redArg(x_634, x_655);
x_657 = lean_box(0);
x_658 = l_Lean_PersistentArray_push___redArg(x_636, x_657);
if (lean_is_scalar(x_645)) {
 x_659 = lean_alloc_ctor(0, 21, 1);
} else {
 x_659 = x_645;
}
lean_ctor_set(x_659, 0, x_646);
lean_ctor_set(x_659, 1, x_647);
lean_ctor_set(x_659, 2, x_625);
lean_ctor_set(x_659, 3, x_626);
lean_ctor_set(x_659, 4, x_627);
lean_ctor_set(x_659, 5, x_628);
lean_ctor_set(x_659, 6, x_629);
lean_ctor_set(x_659, 7, x_649);
lean_ctor_set(x_659, 8, x_651);
lean_ctor_set(x_659, 9, x_652);
lean_ctor_set(x_659, 10, x_654);
lean_ctor_set(x_659, 11, x_656);
lean_ctor_set(x_659, 12, x_635);
lean_ctor_set(x_659, 13, x_658);
lean_ctor_set(x_659, 14, x_637);
lean_ctor_set(x_659, 15, x_638);
lean_ctor_set(x_659, 16, x_640);
lean_ctor_set(x_659, 17, x_641);
lean_ctor_set(x_659, 18, x_642);
lean_ctor_set(x_659, 19, x_643);
lean_ctor_set(x_659, 20, x_644);
lean_ctor_set_uint8(x_659, sizeof(void*)*21, x_639);
if (lean_is_scalar(x_622)) {
 x_660 = lean_alloc_ctor(0, 4, 0);
} else {
 x_660 = x_622;
}
lean_ctor_set(x_660, 0, x_619);
lean_ctor_set(x_660, 1, x_659);
lean_ctor_set(x_660, 2, x_620);
lean_ctor_set(x_660, 3, x_621);
if (lean_is_scalar(x_618)) {
 x_661 = lean_alloc_ctor(0, 16, 1);
} else {
 x_661 = x_618;
}
lean_ctor_set(x_661, 0, x_602);
lean_ctor_set(x_661, 1, x_603);
lean_ctor_set(x_661, 2, x_604);
lean_ctor_set(x_661, 3, x_605);
lean_ctor_set(x_661, 4, x_606);
lean_ctor_set(x_661, 5, x_607);
lean_ctor_set(x_661, 6, x_608);
lean_ctor_set(x_661, 7, x_609);
lean_ctor_set(x_661, 8, x_611);
lean_ctor_set(x_661, 9, x_612);
lean_ctor_set(x_661, 10, x_613);
lean_ctor_set(x_661, 11, x_614);
lean_ctor_set(x_661, 12, x_615);
lean_ctor_set(x_661, 13, x_616);
lean_ctor_set(x_661, 14, x_660);
lean_ctor_set(x_661, 15, x_617);
lean_ctor_set_uint8(x_661, sizeof(void*)*16, x_610);
x_662 = lean_st_ref_set(x_588, x_661, x_601);
x_663 = lean_ctor_get(x_662, 1);
lean_inc(x_663);
lean_dec(x_662);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
lean_inc(x_592);
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_inc(x_588);
lean_inc(x_1);
x_664 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_588, x_589, x_590, x_591, x_592, x_593, x_594, x_595, x_663);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; 
x_665 = lean_ctor_get(x_664, 1);
lean_inc(x_665);
lean_dec(x_664);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
lean_inc(x_592);
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_inc(x_588);
lean_inc(x_587);
lean_inc(x_1);
x_666 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_587, x_588, x_589, x_590, x_591, x_592, x_593, x_594, x_595, x_665);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; 
x_667 = lean_ctor_get(x_666, 1);
lean_inc(x_667);
lean_dec(x_666);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_593);
lean_inc(x_592);
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_inc(x_588);
lean_inc(x_1);
x_668 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_588, x_589, x_590, x_591, x_592, x_593, x_594, x_595, x_667);
if (lean_obj_tag(x_668) == 0)
{
lean_object* x_669; lean_object* x_670; 
x_669 = lean_ctor_get(x_668, 1);
lean_inc(x_669);
lean_dec(x_668);
lean_inc(x_587);
x_670 = l_Lean_Meta_Grind_Arith_Cutsat_assertToIntBounds(x_1, x_587, x_588, x_589, x_590, x_591, x_592, x_593, x_594, x_595, x_669);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = lean_ctor_get(x_670, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 x_672 = x_670;
} else {
 lean_dec_ref(x_670);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(0, 2, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_587);
lean_ctor_set(x_673, 1, x_671);
return x_673;
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
lean_dec(x_587);
x_674 = lean_ctor_get(x_670, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_670, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 x_676 = x_670;
} else {
 lean_dec_ref(x_670);
 x_676 = lean_box(0);
}
if (lean_is_scalar(x_676)) {
 x_677 = lean_alloc_ctor(1, 2, 0);
} else {
 x_677 = x_676;
}
lean_ctor_set(x_677, 0, x_674);
lean_ctor_set(x_677, 1, x_675);
return x_677;
}
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_587);
lean_dec(x_1);
x_678 = lean_ctor_get(x_668, 0);
lean_inc(x_678);
x_679 = lean_ctor_get(x_668, 1);
lean_inc(x_679);
if (lean_is_exclusive(x_668)) {
 lean_ctor_release(x_668, 0);
 lean_ctor_release(x_668, 1);
 x_680 = x_668;
} else {
 lean_dec_ref(x_668);
 x_680 = lean_box(0);
}
if (lean_is_scalar(x_680)) {
 x_681 = lean_alloc_ctor(1, 2, 0);
} else {
 x_681 = x_680;
}
lean_ctor_set(x_681, 0, x_678);
lean_ctor_set(x_681, 1, x_679);
return x_681;
}
}
else
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_587);
lean_dec(x_1);
x_682 = lean_ctor_get(x_666, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_666, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_666)) {
 lean_ctor_release(x_666, 0);
 lean_ctor_release(x_666, 1);
 x_684 = x_666;
} else {
 lean_dec_ref(x_666);
 x_684 = lean_box(0);
}
if (lean_is_scalar(x_684)) {
 x_685 = lean_alloc_ctor(1, 2, 0);
} else {
 x_685 = x_684;
}
lean_ctor_set(x_685, 0, x_682);
lean_ctor_set(x_685, 1, x_683);
return x_685;
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_590);
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_587);
lean_dec(x_1);
x_686 = lean_ctor_get(x_664, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_664, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_688 = x_664;
} else {
 lean_dec_ref(x_664);
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
}
else
{
lean_object* x_704; lean_object* x_705; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_704 = lean_ctor_get(x_576, 0);
lean_inc(x_704);
lean_dec(x_576);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_574);
return x_705;
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
