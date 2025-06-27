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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_288; 
x_25 = lean_ctor_get(x_22, 0);
x_26 = lean_ctor_get(x_22, 1);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_288 = lean_unbox(x_25);
lean_dec(x_25);
if (x_288 == 0)
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
goto block_287;
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_289 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_290 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_22, 7);
lean_ctor_set(x_22, 1, x_290);
lean_ctor_set(x_22, 0, x_289);
x_291 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_291);
lean_ctor_set(x_17, 0, x_22);
lean_inc(x_27);
x_292 = l_Nat_reprFast(x_27);
x_293 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_293, 0, x_292);
x_294 = l_Lean_MessageData_ofFormat(x_293);
x_295 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_295, 0, x_17);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_289);
x_297 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_296, x_6, x_7, x_8, x_9, x_26);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
x_28 = x_2;
x_29 = x_3;
x_30 = x_4;
x_31 = x_5;
x_32 = x_6;
x_33 = x_7;
x_34 = x_8;
x_35 = x_9;
x_36 = x_298;
goto block_287;
}
block_287:
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
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
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
x_105 = lean_ctor_get_uint8(x_40, sizeof(void*)*19);
x_106 = lean_ctor_get(x_40, 14);
x_107 = lean_ctor_get(x_40, 15);
x_108 = lean_ctor_get(x_40, 16);
x_109 = lean_ctor_get(x_40, 17);
x_110 = lean_ctor_get(x_40, 18);
lean_inc(x_110);
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
x_111 = l_Lean_PersistentArray_push___redArg(x_91, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_112 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_92, x_1, x_27);
x_113 = lean_box(0);
x_114 = l_Lean_PersistentArray_push___redArg(x_96, x_113);
x_115 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_116 = l_Lean_PersistentArray_push___redArg(x_97, x_115);
x_117 = l_Lean_PersistentArray_push___redArg(x_98, x_115);
x_118 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_119 = l_Lean_PersistentArray_push___redArg(x_99, x_118);
x_120 = lean_box(0);
x_121 = l_Lean_PersistentArray_push___redArg(x_100, x_120);
x_122 = lean_box(0);
x_123 = l_Lean_PersistentArray_push___redArg(x_102, x_122);
x_124 = lean_alloc_ctor(0, 19, 1);
lean_ctor_set(x_124, 0, x_111);
lean_ctor_set(x_124, 1, x_112);
lean_ctor_set(x_124, 2, x_93);
lean_ctor_set(x_124, 3, x_94);
lean_ctor_set(x_124, 4, x_95);
lean_ctor_set(x_124, 5, x_114);
lean_ctor_set(x_124, 6, x_116);
lean_ctor_set(x_124, 7, x_117);
lean_ctor_set(x_124, 8, x_119);
lean_ctor_set(x_124, 9, x_121);
lean_ctor_set(x_124, 10, x_101);
lean_ctor_set(x_124, 11, x_123);
lean_ctor_set(x_124, 12, x_103);
lean_ctor_set(x_124, 13, x_104);
lean_ctor_set(x_124, 14, x_106);
lean_ctor_set(x_124, 15, x_107);
lean_ctor_set(x_124, 16, x_108);
lean_ctor_set(x_124, 17, x_109);
lean_ctor_set(x_124, 18, x_110);
lean_ctor_set_uint8(x_124, sizeof(void*)*19, x_105);
lean_ctor_set(x_39, 1, x_124);
x_125 = lean_st_ref_set(x_28, x_38, x_41);
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
lean_inc(x_1);
x_127 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
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
x_129 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_131, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_27);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_27);
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_137 = x_131;
} else {
 lean_dec_ref(x_131);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
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
x_139 = lean_ctor_get(x_129, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_129, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_141 = x_129;
} else {
 lean_dec_ref(x_129);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
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
x_143 = lean_ctor_get(x_127, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_127, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_145 = x_127;
} else {
 lean_dec_ref(x_127);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_147 = lean_ctor_get(x_39, 0);
x_148 = lean_ctor_get(x_39, 2);
x_149 = lean_ctor_get(x_39, 3);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_39);
x_150 = lean_ctor_get(x_40, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_40, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_40, 2);
lean_inc(x_152);
x_153 = lean_ctor_get(x_40, 3);
lean_inc(x_153);
x_154 = lean_ctor_get(x_40, 4);
lean_inc(x_154);
x_155 = lean_ctor_get(x_40, 5);
lean_inc(x_155);
x_156 = lean_ctor_get(x_40, 6);
lean_inc(x_156);
x_157 = lean_ctor_get(x_40, 7);
lean_inc(x_157);
x_158 = lean_ctor_get(x_40, 8);
lean_inc(x_158);
x_159 = lean_ctor_get(x_40, 9);
lean_inc(x_159);
x_160 = lean_ctor_get(x_40, 10);
lean_inc(x_160);
x_161 = lean_ctor_get(x_40, 11);
lean_inc(x_161);
x_162 = lean_ctor_get(x_40, 12);
lean_inc(x_162);
x_163 = lean_ctor_get(x_40, 13);
lean_inc(x_163);
x_164 = lean_ctor_get_uint8(x_40, sizeof(void*)*19);
x_165 = lean_ctor_get(x_40, 14);
lean_inc(x_165);
x_166 = lean_ctor_get(x_40, 15);
lean_inc(x_166);
x_167 = lean_ctor_get(x_40, 16);
lean_inc(x_167);
x_168 = lean_ctor_get(x_40, 17);
lean_inc(x_168);
x_169 = lean_ctor_get(x_40, 18);
lean_inc(x_169);
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
 x_170 = x_40;
} else {
 lean_dec_ref(x_40);
 x_170 = lean_box(0);
}
lean_inc(x_1);
x_171 = l_Lean_PersistentArray_push___redArg(x_150, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_172 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_151, x_1, x_27);
x_173 = lean_box(0);
x_174 = l_Lean_PersistentArray_push___redArg(x_155, x_173);
x_175 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_176 = l_Lean_PersistentArray_push___redArg(x_156, x_175);
x_177 = l_Lean_PersistentArray_push___redArg(x_157, x_175);
x_178 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_179 = l_Lean_PersistentArray_push___redArg(x_158, x_178);
x_180 = lean_box(0);
x_181 = l_Lean_PersistentArray_push___redArg(x_159, x_180);
x_182 = lean_box(0);
x_183 = l_Lean_PersistentArray_push___redArg(x_161, x_182);
if (lean_is_scalar(x_170)) {
 x_184 = lean_alloc_ctor(0, 19, 1);
} else {
 x_184 = x_170;
}
lean_ctor_set(x_184, 0, x_171);
lean_ctor_set(x_184, 1, x_172);
lean_ctor_set(x_184, 2, x_152);
lean_ctor_set(x_184, 3, x_153);
lean_ctor_set(x_184, 4, x_154);
lean_ctor_set(x_184, 5, x_174);
lean_ctor_set(x_184, 6, x_176);
lean_ctor_set(x_184, 7, x_177);
lean_ctor_set(x_184, 8, x_179);
lean_ctor_set(x_184, 9, x_181);
lean_ctor_set(x_184, 10, x_160);
lean_ctor_set(x_184, 11, x_183);
lean_ctor_set(x_184, 12, x_162);
lean_ctor_set(x_184, 13, x_163);
lean_ctor_set(x_184, 14, x_165);
lean_ctor_set(x_184, 15, x_166);
lean_ctor_set(x_184, 16, x_167);
lean_ctor_set(x_184, 17, x_168);
lean_ctor_set(x_184, 18, x_169);
lean_ctor_set_uint8(x_184, sizeof(void*)*19, x_164);
x_185 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_185, 0, x_147);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_185, 2, x_148);
lean_ctor_set(x_185, 3, x_149);
lean_ctor_set(x_38, 14, x_185);
x_186 = lean_st_ref_set(x_28, x_38, x_41);
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
lean_inc(x_1);
x_188 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec(x_188);
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
x_190 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_189);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_190, 1);
lean_inc(x_191);
lean_dec(x_190);
x_192 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_27);
lean_ctor_set(x_195, 1, x_193);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_27);
x_196 = lean_ctor_get(x_192, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_192, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_198 = x_192;
} else {
 lean_dec_ref(x_192);
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
x_200 = lean_ctor_get(x_190, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_190, 1);
lean_inc(x_201);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_202 = x_190;
} else {
 lean_dec_ref(x_190);
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
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
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
x_204 = lean_ctor_get(x_188, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_188, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_206 = x_188;
} else {
 lean_dec_ref(x_188);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 2, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_205);
return x_207;
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_208 = lean_ctor_get(x_38, 0);
x_209 = lean_ctor_get(x_38, 1);
x_210 = lean_ctor_get(x_38, 2);
x_211 = lean_ctor_get(x_38, 3);
x_212 = lean_ctor_get(x_38, 4);
x_213 = lean_ctor_get(x_38, 5);
x_214 = lean_ctor_get(x_38, 6);
x_215 = lean_ctor_get(x_38, 7);
x_216 = lean_ctor_get_uint8(x_38, sizeof(void*)*16);
x_217 = lean_ctor_get(x_38, 8);
x_218 = lean_ctor_get(x_38, 9);
x_219 = lean_ctor_get(x_38, 10);
x_220 = lean_ctor_get(x_38, 11);
x_221 = lean_ctor_get(x_38, 12);
x_222 = lean_ctor_get(x_38, 13);
x_223 = lean_ctor_get(x_38, 15);
lean_inc(x_223);
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_218);
lean_inc(x_217);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_38);
x_224 = lean_ctor_get(x_39, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_39, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_39, 3);
lean_inc(x_226);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 lean_ctor_release(x_39, 2);
 lean_ctor_release(x_39, 3);
 x_227 = x_39;
} else {
 lean_dec_ref(x_39);
 x_227 = lean_box(0);
}
x_228 = lean_ctor_get(x_40, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_40, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_40, 2);
lean_inc(x_230);
x_231 = lean_ctor_get(x_40, 3);
lean_inc(x_231);
x_232 = lean_ctor_get(x_40, 4);
lean_inc(x_232);
x_233 = lean_ctor_get(x_40, 5);
lean_inc(x_233);
x_234 = lean_ctor_get(x_40, 6);
lean_inc(x_234);
x_235 = lean_ctor_get(x_40, 7);
lean_inc(x_235);
x_236 = lean_ctor_get(x_40, 8);
lean_inc(x_236);
x_237 = lean_ctor_get(x_40, 9);
lean_inc(x_237);
x_238 = lean_ctor_get(x_40, 10);
lean_inc(x_238);
x_239 = lean_ctor_get(x_40, 11);
lean_inc(x_239);
x_240 = lean_ctor_get(x_40, 12);
lean_inc(x_240);
x_241 = lean_ctor_get(x_40, 13);
lean_inc(x_241);
x_242 = lean_ctor_get_uint8(x_40, sizeof(void*)*19);
x_243 = lean_ctor_get(x_40, 14);
lean_inc(x_243);
x_244 = lean_ctor_get(x_40, 15);
lean_inc(x_244);
x_245 = lean_ctor_get(x_40, 16);
lean_inc(x_245);
x_246 = lean_ctor_get(x_40, 17);
lean_inc(x_246);
x_247 = lean_ctor_get(x_40, 18);
lean_inc(x_247);
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
 x_248 = x_40;
} else {
 lean_dec_ref(x_40);
 x_248 = lean_box(0);
}
lean_inc(x_1);
x_249 = l_Lean_PersistentArray_push___redArg(x_228, x_1);
lean_inc(x_27);
lean_inc(x_1);
x_250 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_229, x_1, x_27);
x_251 = lean_box(0);
x_252 = l_Lean_PersistentArray_push___redArg(x_233, x_251);
x_253 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_254 = l_Lean_PersistentArray_push___redArg(x_234, x_253);
x_255 = l_Lean_PersistentArray_push___redArg(x_235, x_253);
x_256 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_257 = l_Lean_PersistentArray_push___redArg(x_236, x_256);
x_258 = lean_box(0);
x_259 = l_Lean_PersistentArray_push___redArg(x_237, x_258);
x_260 = lean_box(0);
x_261 = l_Lean_PersistentArray_push___redArg(x_239, x_260);
if (lean_is_scalar(x_248)) {
 x_262 = lean_alloc_ctor(0, 19, 1);
} else {
 x_262 = x_248;
}
lean_ctor_set(x_262, 0, x_249);
lean_ctor_set(x_262, 1, x_250);
lean_ctor_set(x_262, 2, x_230);
lean_ctor_set(x_262, 3, x_231);
lean_ctor_set(x_262, 4, x_232);
lean_ctor_set(x_262, 5, x_252);
lean_ctor_set(x_262, 6, x_254);
lean_ctor_set(x_262, 7, x_255);
lean_ctor_set(x_262, 8, x_257);
lean_ctor_set(x_262, 9, x_259);
lean_ctor_set(x_262, 10, x_238);
lean_ctor_set(x_262, 11, x_261);
lean_ctor_set(x_262, 12, x_240);
lean_ctor_set(x_262, 13, x_241);
lean_ctor_set(x_262, 14, x_243);
lean_ctor_set(x_262, 15, x_244);
lean_ctor_set(x_262, 16, x_245);
lean_ctor_set(x_262, 17, x_246);
lean_ctor_set(x_262, 18, x_247);
lean_ctor_set_uint8(x_262, sizeof(void*)*19, x_242);
if (lean_is_scalar(x_227)) {
 x_263 = lean_alloc_ctor(0, 4, 0);
} else {
 x_263 = x_227;
}
lean_ctor_set(x_263, 0, x_224);
lean_ctor_set(x_263, 1, x_262);
lean_ctor_set(x_263, 2, x_225);
lean_ctor_set(x_263, 3, x_226);
x_264 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_264, 0, x_208);
lean_ctor_set(x_264, 1, x_209);
lean_ctor_set(x_264, 2, x_210);
lean_ctor_set(x_264, 3, x_211);
lean_ctor_set(x_264, 4, x_212);
lean_ctor_set(x_264, 5, x_213);
lean_ctor_set(x_264, 6, x_214);
lean_ctor_set(x_264, 7, x_215);
lean_ctor_set(x_264, 8, x_217);
lean_ctor_set(x_264, 9, x_218);
lean_ctor_set(x_264, 10, x_219);
lean_ctor_set(x_264, 11, x_220);
lean_ctor_set(x_264, 12, x_221);
lean_ctor_set(x_264, 13, x_222);
lean_ctor_set(x_264, 14, x_263);
lean_ctor_set(x_264, 15, x_223);
lean_ctor_set_uint8(x_264, sizeof(void*)*16, x_216);
x_265 = lean_st_ref_set(x_28, x_264, x_41);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_1);
x_267 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
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
x_269 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_268);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_269, 1);
lean_inc(x_270);
lean_dec(x_269);
x_271 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_28, x_29, x_30, x_31, x_32, x_33, x_34, x_35, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_271, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_273 = x_271;
} else {
 lean_dec_ref(x_271);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(0, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_27);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_27);
x_275 = lean_ctor_get(x_271, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_271, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_277 = x_271;
} else {
 lean_dec_ref(x_271);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
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
x_279 = lean_ctor_get(x_269, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_269, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_269)) {
 lean_ctor_release(x_269, 0);
 lean_ctor_release(x_269, 1);
 x_281 = x_269;
} else {
 lean_dec_ref(x_269);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
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
x_283 = lean_ctor_get(x_267, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_267, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_285 = x_267;
} else {
 lean_dec_ref(x_267);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; uint8_t x_397; 
x_299 = lean_ctor_get(x_22, 0);
x_300 = lean_ctor_get(x_22, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_22);
x_301 = lean_ctor_get(x_23, 2);
lean_inc(x_301);
lean_dec(x_23);
x_397 = lean_unbox(x_299);
lean_dec(x_299);
if (x_397 == 0)
{
lean_free_object(x_17);
x_302 = x_2;
x_303 = x_3;
x_304 = x_4;
x_305 = x_5;
x_306 = x_6;
x_307 = x_7;
x_308 = x_8;
x_309 = x_9;
x_310 = x_300;
goto block_396;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_398 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_399 = l_Lean_MessageData_ofExpr(x_1);
x_400 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
x_401 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_401);
lean_ctor_set(x_17, 0, x_400);
lean_inc(x_301);
x_402 = l_Nat_reprFast(x_301);
x_403 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_403, 0, x_402);
x_404 = l_Lean_MessageData_ofFormat(x_403);
x_405 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_405, 0, x_17);
lean_ctor_set(x_405, 1, x_404);
x_406 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_398);
x_407 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_21, x_406, x_6, x_7, x_8, x_9, x_300);
x_408 = lean_ctor_get(x_407, 1);
lean_inc(x_408);
lean_dec(x_407);
x_302 = x_2;
x_303 = x_3;
x_304 = x_4;
x_305 = x_5;
x_306 = x_6;
x_307 = x_7;
x_308 = x_8;
x_309 = x_9;
x_310 = x_408;
goto block_396;
}
block_396:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_311 = lean_st_ref_take(x_302, x_310);
x_312 = lean_ctor_get(x_311, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_312, 14);
lean_inc(x_313);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
x_315 = lean_ctor_get(x_311, 1);
lean_inc(x_315);
lean_dec(x_311);
x_316 = lean_ctor_get(x_312, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_312, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_312, 2);
lean_inc(x_318);
x_319 = lean_ctor_get(x_312, 3);
lean_inc(x_319);
x_320 = lean_ctor_get(x_312, 4);
lean_inc(x_320);
x_321 = lean_ctor_get(x_312, 5);
lean_inc(x_321);
x_322 = lean_ctor_get(x_312, 6);
lean_inc(x_322);
x_323 = lean_ctor_get(x_312, 7);
lean_inc(x_323);
x_324 = lean_ctor_get_uint8(x_312, sizeof(void*)*16);
x_325 = lean_ctor_get(x_312, 8);
lean_inc(x_325);
x_326 = lean_ctor_get(x_312, 9);
lean_inc(x_326);
x_327 = lean_ctor_get(x_312, 10);
lean_inc(x_327);
x_328 = lean_ctor_get(x_312, 11);
lean_inc(x_328);
x_329 = lean_ctor_get(x_312, 12);
lean_inc(x_329);
x_330 = lean_ctor_get(x_312, 13);
lean_inc(x_330);
x_331 = lean_ctor_get(x_312, 15);
lean_inc(x_331);
if (lean_is_exclusive(x_312)) {
 lean_ctor_release(x_312, 0);
 lean_ctor_release(x_312, 1);
 lean_ctor_release(x_312, 2);
 lean_ctor_release(x_312, 3);
 lean_ctor_release(x_312, 4);
 lean_ctor_release(x_312, 5);
 lean_ctor_release(x_312, 6);
 lean_ctor_release(x_312, 7);
 lean_ctor_release(x_312, 8);
 lean_ctor_release(x_312, 9);
 lean_ctor_release(x_312, 10);
 lean_ctor_release(x_312, 11);
 lean_ctor_release(x_312, 12);
 lean_ctor_release(x_312, 13);
 lean_ctor_release(x_312, 14);
 lean_ctor_release(x_312, 15);
 x_332 = x_312;
} else {
 lean_dec_ref(x_312);
 x_332 = lean_box(0);
}
x_333 = lean_ctor_get(x_313, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_313, 2);
lean_inc(x_334);
x_335 = lean_ctor_get(x_313, 3);
lean_inc(x_335);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 lean_ctor_release(x_313, 2);
 lean_ctor_release(x_313, 3);
 x_336 = x_313;
} else {
 lean_dec_ref(x_313);
 x_336 = lean_box(0);
}
x_337 = lean_ctor_get(x_314, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_314, 1);
lean_inc(x_338);
x_339 = lean_ctor_get(x_314, 2);
lean_inc(x_339);
x_340 = lean_ctor_get(x_314, 3);
lean_inc(x_340);
x_341 = lean_ctor_get(x_314, 4);
lean_inc(x_341);
x_342 = lean_ctor_get(x_314, 5);
lean_inc(x_342);
x_343 = lean_ctor_get(x_314, 6);
lean_inc(x_343);
x_344 = lean_ctor_get(x_314, 7);
lean_inc(x_344);
x_345 = lean_ctor_get(x_314, 8);
lean_inc(x_345);
x_346 = lean_ctor_get(x_314, 9);
lean_inc(x_346);
x_347 = lean_ctor_get(x_314, 10);
lean_inc(x_347);
x_348 = lean_ctor_get(x_314, 11);
lean_inc(x_348);
x_349 = lean_ctor_get(x_314, 12);
lean_inc(x_349);
x_350 = lean_ctor_get(x_314, 13);
lean_inc(x_350);
x_351 = lean_ctor_get_uint8(x_314, sizeof(void*)*19);
x_352 = lean_ctor_get(x_314, 14);
lean_inc(x_352);
x_353 = lean_ctor_get(x_314, 15);
lean_inc(x_353);
x_354 = lean_ctor_get(x_314, 16);
lean_inc(x_354);
x_355 = lean_ctor_get(x_314, 17);
lean_inc(x_355);
x_356 = lean_ctor_get(x_314, 18);
lean_inc(x_356);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 lean_ctor_release(x_314, 2);
 lean_ctor_release(x_314, 3);
 lean_ctor_release(x_314, 4);
 lean_ctor_release(x_314, 5);
 lean_ctor_release(x_314, 6);
 lean_ctor_release(x_314, 7);
 lean_ctor_release(x_314, 8);
 lean_ctor_release(x_314, 9);
 lean_ctor_release(x_314, 10);
 lean_ctor_release(x_314, 11);
 lean_ctor_release(x_314, 12);
 lean_ctor_release(x_314, 13);
 lean_ctor_release(x_314, 14);
 lean_ctor_release(x_314, 15);
 lean_ctor_release(x_314, 16);
 lean_ctor_release(x_314, 17);
 lean_ctor_release(x_314, 18);
 x_357 = x_314;
} else {
 lean_dec_ref(x_314);
 x_357 = lean_box(0);
}
lean_inc(x_1);
x_358 = l_Lean_PersistentArray_push___redArg(x_337, x_1);
lean_inc(x_301);
lean_inc(x_1);
x_359 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_338, x_1, x_301);
x_360 = lean_box(0);
x_361 = l_Lean_PersistentArray_push___redArg(x_342, x_360);
x_362 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_363 = l_Lean_PersistentArray_push___redArg(x_343, x_362);
x_364 = l_Lean_PersistentArray_push___redArg(x_344, x_362);
x_365 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_366 = l_Lean_PersistentArray_push___redArg(x_345, x_365);
x_367 = lean_box(0);
x_368 = l_Lean_PersistentArray_push___redArg(x_346, x_367);
x_369 = lean_box(0);
x_370 = l_Lean_PersistentArray_push___redArg(x_348, x_369);
if (lean_is_scalar(x_357)) {
 x_371 = lean_alloc_ctor(0, 19, 1);
} else {
 x_371 = x_357;
}
lean_ctor_set(x_371, 0, x_358);
lean_ctor_set(x_371, 1, x_359);
lean_ctor_set(x_371, 2, x_339);
lean_ctor_set(x_371, 3, x_340);
lean_ctor_set(x_371, 4, x_341);
lean_ctor_set(x_371, 5, x_361);
lean_ctor_set(x_371, 6, x_363);
lean_ctor_set(x_371, 7, x_364);
lean_ctor_set(x_371, 8, x_366);
lean_ctor_set(x_371, 9, x_368);
lean_ctor_set(x_371, 10, x_347);
lean_ctor_set(x_371, 11, x_370);
lean_ctor_set(x_371, 12, x_349);
lean_ctor_set(x_371, 13, x_350);
lean_ctor_set(x_371, 14, x_352);
lean_ctor_set(x_371, 15, x_353);
lean_ctor_set(x_371, 16, x_354);
lean_ctor_set(x_371, 17, x_355);
lean_ctor_set(x_371, 18, x_356);
lean_ctor_set_uint8(x_371, sizeof(void*)*19, x_351);
if (lean_is_scalar(x_336)) {
 x_372 = lean_alloc_ctor(0, 4, 0);
} else {
 x_372 = x_336;
}
lean_ctor_set(x_372, 0, x_333);
lean_ctor_set(x_372, 1, x_371);
lean_ctor_set(x_372, 2, x_334);
lean_ctor_set(x_372, 3, x_335);
if (lean_is_scalar(x_332)) {
 x_373 = lean_alloc_ctor(0, 16, 1);
} else {
 x_373 = x_332;
}
lean_ctor_set(x_373, 0, x_316);
lean_ctor_set(x_373, 1, x_317);
lean_ctor_set(x_373, 2, x_318);
lean_ctor_set(x_373, 3, x_319);
lean_ctor_set(x_373, 4, x_320);
lean_ctor_set(x_373, 5, x_321);
lean_ctor_set(x_373, 6, x_322);
lean_ctor_set(x_373, 7, x_323);
lean_ctor_set(x_373, 8, x_325);
lean_ctor_set(x_373, 9, x_326);
lean_ctor_set(x_373, 10, x_327);
lean_ctor_set(x_373, 11, x_328);
lean_ctor_set(x_373, 12, x_329);
lean_ctor_set(x_373, 13, x_330);
lean_ctor_set(x_373, 14, x_372);
lean_ctor_set(x_373, 15, x_331);
lean_ctor_set_uint8(x_373, sizeof(void*)*16, x_324);
x_374 = lean_st_ref_set(x_302, x_373, x_315);
x_375 = lean_ctor_get(x_374, 1);
lean_inc(x_375);
lean_dec(x_374);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_1);
x_376 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_302, x_303, x_304, x_305, x_306, x_307, x_308, x_309, x_375);
if (lean_obj_tag(x_376) == 0)
{
lean_object* x_377; lean_object* x_378; 
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec(x_376);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
lean_inc(x_303);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_1);
x_378 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_301, x_302, x_303, x_304, x_305, x_306, x_307, x_308, x_309, x_377);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_378, 1);
lean_inc(x_379);
lean_dec(x_378);
x_380 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_302, x_303, x_304, x_305, x_306, x_307, x_308, x_309, x_379);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_380, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(0, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_301);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
lean_dec(x_301);
x_384 = lean_ctor_get(x_380, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_380, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_386 = x_380;
} else {
 lean_dec_ref(x_380);
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
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_1);
x_388 = lean_ctor_get(x_378, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_378, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_390 = x_378;
} else {
 lean_dec_ref(x_378);
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
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_309);
lean_dec(x_308);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_1);
x_392 = lean_ctor_get(x_376, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_376, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_376)) {
 lean_ctor_release(x_376, 0);
 lean_ctor_release(x_376, 1);
 x_394 = x_376;
} else {
 lean_dec_ref(x_376);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; uint8_t x_513; 
x_409 = lean_ctor_get(x_17, 0);
x_410 = lean_ctor_get(x_17, 1);
lean_inc(x_410);
lean_inc(x_409);
lean_dec(x_17);
x_411 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_412 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_411, x_8, x_410);
x_413 = lean_ctor_get(x_409, 0);
lean_inc(x_413);
lean_dec(x_409);
x_414 = lean_ctor_get(x_412, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_412, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_412)) {
 lean_ctor_release(x_412, 0);
 lean_ctor_release(x_412, 1);
 x_416 = x_412;
} else {
 lean_dec_ref(x_412);
 x_416 = lean_box(0);
}
x_417 = lean_ctor_get(x_413, 2);
lean_inc(x_417);
lean_dec(x_413);
x_513 = lean_unbox(x_414);
lean_dec(x_414);
if (x_513 == 0)
{
lean_dec(x_416);
x_418 = x_2;
x_419 = x_3;
x_420 = x_4;
x_421 = x_5;
x_422 = x_6;
x_423 = x_7;
x_424 = x_8;
x_425 = x_9;
x_426 = x_415;
goto block_512;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_514 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_515 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_416)) {
 x_516 = lean_alloc_ctor(7, 2, 0);
} else {
 x_516 = x_416;
 lean_ctor_set_tag(x_516, 7);
}
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
x_517 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
x_518 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_518, 0, x_516);
lean_ctor_set(x_518, 1, x_517);
lean_inc(x_417);
x_519 = l_Nat_reprFast(x_417);
x_520 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_520, 0, x_519);
x_521 = l_Lean_MessageData_ofFormat(x_520);
x_522 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_522, 0, x_518);
lean_ctor_set(x_522, 1, x_521);
x_523 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_523, 0, x_522);
lean_ctor_set(x_523, 1, x_514);
x_524 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_411, x_523, x_6, x_7, x_8, x_9, x_415);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec(x_524);
x_418 = x_2;
x_419 = x_3;
x_420 = x_4;
x_421 = x_5;
x_422 = x_6;
x_423 = x_7;
x_424 = x_8;
x_425 = x_9;
x_426 = x_525;
goto block_512;
}
block_512:
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; uint8_t x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; uint8_t x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_427 = lean_st_ref_take(x_418, x_426);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_428, 14);
lean_inc(x_429);
x_430 = lean_ctor_get(x_429, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_427, 1);
lean_inc(x_431);
lean_dec(x_427);
x_432 = lean_ctor_get(x_428, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_428, 1);
lean_inc(x_433);
x_434 = lean_ctor_get(x_428, 2);
lean_inc(x_434);
x_435 = lean_ctor_get(x_428, 3);
lean_inc(x_435);
x_436 = lean_ctor_get(x_428, 4);
lean_inc(x_436);
x_437 = lean_ctor_get(x_428, 5);
lean_inc(x_437);
x_438 = lean_ctor_get(x_428, 6);
lean_inc(x_438);
x_439 = lean_ctor_get(x_428, 7);
lean_inc(x_439);
x_440 = lean_ctor_get_uint8(x_428, sizeof(void*)*16);
x_441 = lean_ctor_get(x_428, 8);
lean_inc(x_441);
x_442 = lean_ctor_get(x_428, 9);
lean_inc(x_442);
x_443 = lean_ctor_get(x_428, 10);
lean_inc(x_443);
x_444 = lean_ctor_get(x_428, 11);
lean_inc(x_444);
x_445 = lean_ctor_get(x_428, 12);
lean_inc(x_445);
x_446 = lean_ctor_get(x_428, 13);
lean_inc(x_446);
x_447 = lean_ctor_get(x_428, 15);
lean_inc(x_447);
if (lean_is_exclusive(x_428)) {
 lean_ctor_release(x_428, 0);
 lean_ctor_release(x_428, 1);
 lean_ctor_release(x_428, 2);
 lean_ctor_release(x_428, 3);
 lean_ctor_release(x_428, 4);
 lean_ctor_release(x_428, 5);
 lean_ctor_release(x_428, 6);
 lean_ctor_release(x_428, 7);
 lean_ctor_release(x_428, 8);
 lean_ctor_release(x_428, 9);
 lean_ctor_release(x_428, 10);
 lean_ctor_release(x_428, 11);
 lean_ctor_release(x_428, 12);
 lean_ctor_release(x_428, 13);
 lean_ctor_release(x_428, 14);
 lean_ctor_release(x_428, 15);
 x_448 = x_428;
} else {
 lean_dec_ref(x_428);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_429, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_429, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_429, 3);
lean_inc(x_451);
if (lean_is_exclusive(x_429)) {
 lean_ctor_release(x_429, 0);
 lean_ctor_release(x_429, 1);
 lean_ctor_release(x_429, 2);
 lean_ctor_release(x_429, 3);
 x_452 = x_429;
} else {
 lean_dec_ref(x_429);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_430, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_430, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_430, 2);
lean_inc(x_455);
x_456 = lean_ctor_get(x_430, 3);
lean_inc(x_456);
x_457 = lean_ctor_get(x_430, 4);
lean_inc(x_457);
x_458 = lean_ctor_get(x_430, 5);
lean_inc(x_458);
x_459 = lean_ctor_get(x_430, 6);
lean_inc(x_459);
x_460 = lean_ctor_get(x_430, 7);
lean_inc(x_460);
x_461 = lean_ctor_get(x_430, 8);
lean_inc(x_461);
x_462 = lean_ctor_get(x_430, 9);
lean_inc(x_462);
x_463 = lean_ctor_get(x_430, 10);
lean_inc(x_463);
x_464 = lean_ctor_get(x_430, 11);
lean_inc(x_464);
x_465 = lean_ctor_get(x_430, 12);
lean_inc(x_465);
x_466 = lean_ctor_get(x_430, 13);
lean_inc(x_466);
x_467 = lean_ctor_get_uint8(x_430, sizeof(void*)*19);
x_468 = lean_ctor_get(x_430, 14);
lean_inc(x_468);
x_469 = lean_ctor_get(x_430, 15);
lean_inc(x_469);
x_470 = lean_ctor_get(x_430, 16);
lean_inc(x_470);
x_471 = lean_ctor_get(x_430, 17);
lean_inc(x_471);
x_472 = lean_ctor_get(x_430, 18);
lean_inc(x_472);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 lean_ctor_release(x_430, 1);
 lean_ctor_release(x_430, 2);
 lean_ctor_release(x_430, 3);
 lean_ctor_release(x_430, 4);
 lean_ctor_release(x_430, 5);
 lean_ctor_release(x_430, 6);
 lean_ctor_release(x_430, 7);
 lean_ctor_release(x_430, 8);
 lean_ctor_release(x_430, 9);
 lean_ctor_release(x_430, 10);
 lean_ctor_release(x_430, 11);
 lean_ctor_release(x_430, 12);
 lean_ctor_release(x_430, 13);
 lean_ctor_release(x_430, 14);
 lean_ctor_release(x_430, 15);
 lean_ctor_release(x_430, 16);
 lean_ctor_release(x_430, 17);
 lean_ctor_release(x_430, 18);
 x_473 = x_430;
} else {
 lean_dec_ref(x_430);
 x_473 = lean_box(0);
}
lean_inc(x_1);
x_474 = l_Lean_PersistentArray_push___redArg(x_453, x_1);
lean_inc(x_417);
lean_inc(x_1);
x_475 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_454, x_1, x_417);
x_476 = lean_box(0);
x_477 = l_Lean_PersistentArray_push___redArg(x_458, x_476);
x_478 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_479 = l_Lean_PersistentArray_push___redArg(x_459, x_478);
x_480 = l_Lean_PersistentArray_push___redArg(x_460, x_478);
x_481 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_482 = l_Lean_PersistentArray_push___redArg(x_461, x_481);
x_483 = lean_box(0);
x_484 = l_Lean_PersistentArray_push___redArg(x_462, x_483);
x_485 = lean_box(0);
x_486 = l_Lean_PersistentArray_push___redArg(x_464, x_485);
if (lean_is_scalar(x_473)) {
 x_487 = lean_alloc_ctor(0, 19, 1);
} else {
 x_487 = x_473;
}
lean_ctor_set(x_487, 0, x_474);
lean_ctor_set(x_487, 1, x_475);
lean_ctor_set(x_487, 2, x_455);
lean_ctor_set(x_487, 3, x_456);
lean_ctor_set(x_487, 4, x_457);
lean_ctor_set(x_487, 5, x_477);
lean_ctor_set(x_487, 6, x_479);
lean_ctor_set(x_487, 7, x_480);
lean_ctor_set(x_487, 8, x_482);
lean_ctor_set(x_487, 9, x_484);
lean_ctor_set(x_487, 10, x_463);
lean_ctor_set(x_487, 11, x_486);
lean_ctor_set(x_487, 12, x_465);
lean_ctor_set(x_487, 13, x_466);
lean_ctor_set(x_487, 14, x_468);
lean_ctor_set(x_487, 15, x_469);
lean_ctor_set(x_487, 16, x_470);
lean_ctor_set(x_487, 17, x_471);
lean_ctor_set(x_487, 18, x_472);
lean_ctor_set_uint8(x_487, sizeof(void*)*19, x_467);
if (lean_is_scalar(x_452)) {
 x_488 = lean_alloc_ctor(0, 4, 0);
} else {
 x_488 = x_452;
}
lean_ctor_set(x_488, 0, x_449);
lean_ctor_set(x_488, 1, x_487);
lean_ctor_set(x_488, 2, x_450);
lean_ctor_set(x_488, 3, x_451);
if (lean_is_scalar(x_448)) {
 x_489 = lean_alloc_ctor(0, 16, 1);
} else {
 x_489 = x_448;
}
lean_ctor_set(x_489, 0, x_432);
lean_ctor_set(x_489, 1, x_433);
lean_ctor_set(x_489, 2, x_434);
lean_ctor_set(x_489, 3, x_435);
lean_ctor_set(x_489, 4, x_436);
lean_ctor_set(x_489, 5, x_437);
lean_ctor_set(x_489, 6, x_438);
lean_ctor_set(x_489, 7, x_439);
lean_ctor_set(x_489, 8, x_441);
lean_ctor_set(x_489, 9, x_442);
lean_ctor_set(x_489, 10, x_443);
lean_ctor_set(x_489, 11, x_444);
lean_ctor_set(x_489, 12, x_445);
lean_ctor_set(x_489, 13, x_446);
lean_ctor_set(x_489, 14, x_488);
lean_ctor_set(x_489, 15, x_447);
lean_ctor_set_uint8(x_489, sizeof(void*)*16, x_440);
x_490 = lean_st_ref_set(x_418, x_489, x_431);
x_491 = lean_ctor_get(x_490, 1);
lean_inc(x_491);
lean_dec(x_490);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_422);
lean_inc(x_421);
lean_inc(x_420);
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_1);
x_492 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_418, x_419, x_420, x_421, x_422, x_423, x_424, x_425, x_491);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; 
x_493 = lean_ctor_get(x_492, 1);
lean_inc(x_493);
lean_dec(x_492);
lean_inc(x_425);
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_422);
lean_inc(x_421);
lean_inc(x_420);
lean_inc(x_419);
lean_inc(x_418);
lean_inc(x_417);
lean_inc(x_1);
x_494 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_417, x_418, x_419, x_420, x_421, x_422, x_423, x_424, x_425, x_493);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; 
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec(x_494);
x_496 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_418, x_419, x_420, x_421, x_422, x_423, x_424, x_425, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
x_497 = lean_ctor_get(x_496, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_498 = x_496;
} else {
 lean_dec_ref(x_496);
 x_498 = lean_box(0);
}
if (lean_is_scalar(x_498)) {
 x_499 = lean_alloc_ctor(0, 2, 0);
} else {
 x_499 = x_498;
}
lean_ctor_set(x_499, 0, x_417);
lean_ctor_set(x_499, 1, x_497);
return x_499;
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_417);
x_500 = lean_ctor_get(x_496, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_496, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_496)) {
 lean_ctor_release(x_496, 0);
 lean_ctor_release(x_496, 1);
 x_502 = x_496;
} else {
 lean_dec_ref(x_496);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_425);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_1);
x_504 = lean_ctor_get(x_494, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_494, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_506 = x_494;
} else {
 lean_dec_ref(x_494);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_425);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_1);
x_508 = lean_ctor_get(x_492, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_492, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_510 = x_492;
} else {
 lean_dec_ref(x_492);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
}
}
else
{
lean_object* x_526; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_526 = lean_ctor_get(x_16, 0);
lean_inc(x_526);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_526);
return x_11;
}
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_527 = lean_ctor_get(x_11, 0);
x_528 = lean_ctor_get(x_11, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_11);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
lean_inc(x_1);
x_530 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_shareCommonAlpha_go_spec__0___redArg(x_529, x_1);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; uint8_t x_637; 
x_531 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_2, x_528);
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_534 = x_531;
} else {
 lean_dec_ref(x_531);
 x_534 = lean_box(0);
}
x_535 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__4;
x_536 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_535, x_8, x_533);
x_537 = lean_ctor_get(x_532, 0);
lean_inc(x_537);
lean_dec(x_532);
x_538 = lean_ctor_get(x_536, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_536, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 lean_ctor_release(x_536, 1);
 x_540 = x_536;
} else {
 lean_dec_ref(x_536);
 x_540 = lean_box(0);
}
x_541 = lean_ctor_get(x_537, 2);
lean_inc(x_541);
lean_dec(x_537);
x_637 = lean_unbox(x_538);
lean_dec(x_538);
if (x_637 == 0)
{
lean_dec(x_540);
lean_dec(x_534);
x_542 = x_2;
x_543 = x_3;
x_544 = x_4;
x_545 = x_5;
x_546 = x_6;
x_547 = x_7;
x_548 = x_8;
x_549 = x_9;
x_550 = x_539;
goto block_636;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
x_638 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__11;
lean_inc(x_1);
x_639 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_540)) {
 x_640 = lean_alloc_ctor(7, 2, 0);
} else {
 x_640 = x_540;
 lean_ctor_set_tag(x_640, 7);
}
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
x_641 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__13;
if (lean_is_scalar(x_534)) {
 x_642 = lean_alloc_ctor(7, 2, 0);
} else {
 x_642 = x_534;
 lean_ctor_set_tag(x_642, 7);
}
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
lean_inc(x_541);
x_643 = l_Nat_reprFast(x_541);
x_644 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_644, 0, x_643);
x_645 = l_Lean_MessageData_ofFormat(x_644);
x_646 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_646, 0, x_642);
lean_ctor_set(x_646, 1, x_645);
x_647 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_638);
x_648 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_535, x_647, x_6, x_7, x_8, x_9, x_539);
x_649 = lean_ctor_get(x_648, 1);
lean_inc(x_649);
lean_dec(x_648);
x_542 = x_2;
x_543 = x_3;
x_544 = x_4;
x_545 = x_5;
x_546 = x_6;
x_547 = x_7;
x_548 = x_8;
x_549 = x_9;
x_550 = x_649;
goto block_636;
}
block_636:
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; uint8_t x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; uint8_t x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_551 = lean_st_ref_take(x_542, x_550);
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_552, 14);
lean_inc(x_553);
x_554 = lean_ctor_get(x_553, 1);
lean_inc(x_554);
x_555 = lean_ctor_get(x_551, 1);
lean_inc(x_555);
lean_dec(x_551);
x_556 = lean_ctor_get(x_552, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_552, 1);
lean_inc(x_557);
x_558 = lean_ctor_get(x_552, 2);
lean_inc(x_558);
x_559 = lean_ctor_get(x_552, 3);
lean_inc(x_559);
x_560 = lean_ctor_get(x_552, 4);
lean_inc(x_560);
x_561 = lean_ctor_get(x_552, 5);
lean_inc(x_561);
x_562 = lean_ctor_get(x_552, 6);
lean_inc(x_562);
x_563 = lean_ctor_get(x_552, 7);
lean_inc(x_563);
x_564 = lean_ctor_get_uint8(x_552, sizeof(void*)*16);
x_565 = lean_ctor_get(x_552, 8);
lean_inc(x_565);
x_566 = lean_ctor_get(x_552, 9);
lean_inc(x_566);
x_567 = lean_ctor_get(x_552, 10);
lean_inc(x_567);
x_568 = lean_ctor_get(x_552, 11);
lean_inc(x_568);
x_569 = lean_ctor_get(x_552, 12);
lean_inc(x_569);
x_570 = lean_ctor_get(x_552, 13);
lean_inc(x_570);
x_571 = lean_ctor_get(x_552, 15);
lean_inc(x_571);
if (lean_is_exclusive(x_552)) {
 lean_ctor_release(x_552, 0);
 lean_ctor_release(x_552, 1);
 lean_ctor_release(x_552, 2);
 lean_ctor_release(x_552, 3);
 lean_ctor_release(x_552, 4);
 lean_ctor_release(x_552, 5);
 lean_ctor_release(x_552, 6);
 lean_ctor_release(x_552, 7);
 lean_ctor_release(x_552, 8);
 lean_ctor_release(x_552, 9);
 lean_ctor_release(x_552, 10);
 lean_ctor_release(x_552, 11);
 lean_ctor_release(x_552, 12);
 lean_ctor_release(x_552, 13);
 lean_ctor_release(x_552, 14);
 lean_ctor_release(x_552, 15);
 x_572 = x_552;
} else {
 lean_dec_ref(x_552);
 x_572 = lean_box(0);
}
x_573 = lean_ctor_get(x_553, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_553, 2);
lean_inc(x_574);
x_575 = lean_ctor_get(x_553, 3);
lean_inc(x_575);
if (lean_is_exclusive(x_553)) {
 lean_ctor_release(x_553, 0);
 lean_ctor_release(x_553, 1);
 lean_ctor_release(x_553, 2);
 lean_ctor_release(x_553, 3);
 x_576 = x_553;
} else {
 lean_dec_ref(x_553);
 x_576 = lean_box(0);
}
x_577 = lean_ctor_get(x_554, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_554, 1);
lean_inc(x_578);
x_579 = lean_ctor_get(x_554, 2);
lean_inc(x_579);
x_580 = lean_ctor_get(x_554, 3);
lean_inc(x_580);
x_581 = lean_ctor_get(x_554, 4);
lean_inc(x_581);
x_582 = lean_ctor_get(x_554, 5);
lean_inc(x_582);
x_583 = lean_ctor_get(x_554, 6);
lean_inc(x_583);
x_584 = lean_ctor_get(x_554, 7);
lean_inc(x_584);
x_585 = lean_ctor_get(x_554, 8);
lean_inc(x_585);
x_586 = lean_ctor_get(x_554, 9);
lean_inc(x_586);
x_587 = lean_ctor_get(x_554, 10);
lean_inc(x_587);
x_588 = lean_ctor_get(x_554, 11);
lean_inc(x_588);
x_589 = lean_ctor_get(x_554, 12);
lean_inc(x_589);
x_590 = lean_ctor_get(x_554, 13);
lean_inc(x_590);
x_591 = lean_ctor_get_uint8(x_554, sizeof(void*)*19);
x_592 = lean_ctor_get(x_554, 14);
lean_inc(x_592);
x_593 = lean_ctor_get(x_554, 15);
lean_inc(x_593);
x_594 = lean_ctor_get(x_554, 16);
lean_inc(x_594);
x_595 = lean_ctor_get(x_554, 17);
lean_inc(x_595);
x_596 = lean_ctor_get(x_554, 18);
lean_inc(x_596);
if (lean_is_exclusive(x_554)) {
 lean_ctor_release(x_554, 0);
 lean_ctor_release(x_554, 1);
 lean_ctor_release(x_554, 2);
 lean_ctor_release(x_554, 3);
 lean_ctor_release(x_554, 4);
 lean_ctor_release(x_554, 5);
 lean_ctor_release(x_554, 6);
 lean_ctor_release(x_554, 7);
 lean_ctor_release(x_554, 8);
 lean_ctor_release(x_554, 9);
 lean_ctor_release(x_554, 10);
 lean_ctor_release(x_554, 11);
 lean_ctor_release(x_554, 12);
 lean_ctor_release(x_554, 13);
 lean_ctor_release(x_554, 14);
 lean_ctor_release(x_554, 15);
 lean_ctor_release(x_554, 16);
 lean_ctor_release(x_554, 17);
 lean_ctor_release(x_554, 18);
 x_597 = x_554;
} else {
 lean_dec_ref(x_554);
 x_597 = lean_box(0);
}
lean_inc(x_1);
x_598 = l_Lean_PersistentArray_push___redArg(x_577, x_1);
lean_inc(x_541);
lean_inc(x_1);
x_599 = l_Lean_PersistentHashMap_insert___at_____private_Lean_Meta_Tactic_Grind_AlphaShareCommon_0__Lean_Meta_Grind_save_spec__1___redArg(x_578, x_1, x_541);
x_600 = lean_box(0);
x_601 = l_Lean_PersistentArray_push___redArg(x_582, x_600);
x_602 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__7;
x_603 = l_Lean_PersistentArray_push___redArg(x_583, x_602);
x_604 = l_Lean_PersistentArray_push___redArg(x_584, x_602);
x_605 = l_Lean_Meta_Grind_Arith_Cutsat_mkVarImpl___closed__9;
x_606 = l_Lean_PersistentArray_push___redArg(x_585, x_605);
x_607 = lean_box(0);
x_608 = l_Lean_PersistentArray_push___redArg(x_586, x_607);
x_609 = lean_box(0);
x_610 = l_Lean_PersistentArray_push___redArg(x_588, x_609);
if (lean_is_scalar(x_597)) {
 x_611 = lean_alloc_ctor(0, 19, 1);
} else {
 x_611 = x_597;
}
lean_ctor_set(x_611, 0, x_598);
lean_ctor_set(x_611, 1, x_599);
lean_ctor_set(x_611, 2, x_579);
lean_ctor_set(x_611, 3, x_580);
lean_ctor_set(x_611, 4, x_581);
lean_ctor_set(x_611, 5, x_601);
lean_ctor_set(x_611, 6, x_603);
lean_ctor_set(x_611, 7, x_604);
lean_ctor_set(x_611, 8, x_606);
lean_ctor_set(x_611, 9, x_608);
lean_ctor_set(x_611, 10, x_587);
lean_ctor_set(x_611, 11, x_610);
lean_ctor_set(x_611, 12, x_589);
lean_ctor_set(x_611, 13, x_590);
lean_ctor_set(x_611, 14, x_592);
lean_ctor_set(x_611, 15, x_593);
lean_ctor_set(x_611, 16, x_594);
lean_ctor_set(x_611, 17, x_595);
lean_ctor_set(x_611, 18, x_596);
lean_ctor_set_uint8(x_611, sizeof(void*)*19, x_591);
if (lean_is_scalar(x_576)) {
 x_612 = lean_alloc_ctor(0, 4, 0);
} else {
 x_612 = x_576;
}
lean_ctor_set(x_612, 0, x_573);
lean_ctor_set(x_612, 1, x_611);
lean_ctor_set(x_612, 2, x_574);
lean_ctor_set(x_612, 3, x_575);
if (lean_is_scalar(x_572)) {
 x_613 = lean_alloc_ctor(0, 16, 1);
} else {
 x_613 = x_572;
}
lean_ctor_set(x_613, 0, x_556);
lean_ctor_set(x_613, 1, x_557);
lean_ctor_set(x_613, 2, x_558);
lean_ctor_set(x_613, 3, x_559);
lean_ctor_set(x_613, 4, x_560);
lean_ctor_set(x_613, 5, x_561);
lean_ctor_set(x_613, 6, x_562);
lean_ctor_set(x_613, 7, x_563);
lean_ctor_set(x_613, 8, x_565);
lean_ctor_set(x_613, 9, x_566);
lean_ctor_set(x_613, 10, x_567);
lean_ctor_set(x_613, 11, x_568);
lean_ctor_set(x_613, 12, x_569);
lean_ctor_set(x_613, 13, x_570);
lean_ctor_set(x_613, 14, x_612);
lean_ctor_set(x_613, 15, x_571);
lean_ctor_set_uint8(x_613, sizeof(void*)*16, x_564);
x_614 = lean_st_ref_set(x_542, x_613, x_555);
x_615 = lean_ctor_get(x_614, 1);
lean_inc(x_615);
lean_dec(x_614);
lean_inc(x_549);
lean_inc(x_548);
lean_inc(x_547);
lean_inc(x_546);
lean_inc(x_545);
lean_inc(x_544);
lean_inc(x_543);
lean_inc(x_542);
lean_inc(x_1);
x_616 = l_Lean_Meta_Grind_markAsCutsatTerm(x_1, x_542, x_543, x_544, x_545, x_546, x_547, x_548, x_549, x_615);
if (lean_obj_tag(x_616) == 0)
{
lean_object* x_617; lean_object* x_618; 
x_617 = lean_ctor_get(x_616, 1);
lean_inc(x_617);
lean_dec(x_616);
lean_inc(x_549);
lean_inc(x_548);
lean_inc(x_547);
lean_inc(x_546);
lean_inc(x_545);
lean_inc(x_544);
lean_inc(x_543);
lean_inc(x_542);
lean_inc(x_541);
lean_inc(x_1);
x_618 = l_Lean_Meta_Grind_Arith_Cutsat_assertNatCast(x_1, x_541, x_542, x_543, x_544, x_545, x_546, x_547, x_548, x_549, x_617);
if (lean_obj_tag(x_618) == 0)
{
lean_object* x_619; lean_object* x_620; 
x_619 = lean_ctor_get(x_618, 1);
lean_inc(x_619);
lean_dec(x_618);
x_620 = l_Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg(x_1, x_542, x_543, x_544, x_545, x_546, x_547, x_548, x_549, x_619);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_620, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_622 = x_620;
} else {
 lean_dec_ref(x_620);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(0, 2, 0);
} else {
 x_623 = x_622;
}
lean_ctor_set(x_623, 0, x_541);
lean_ctor_set(x_623, 1, x_621);
return x_623;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; 
lean_dec(x_541);
x_624 = lean_ctor_get(x_620, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_620, 1);
lean_inc(x_625);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 lean_ctor_release(x_620, 1);
 x_626 = x_620;
} else {
 lean_dec_ref(x_620);
 x_626 = lean_box(0);
}
if (lean_is_scalar(x_626)) {
 x_627 = lean_alloc_ctor(1, 2, 0);
} else {
 x_627 = x_626;
}
lean_ctor_set(x_627, 0, x_624);
lean_ctor_set(x_627, 1, x_625);
return x_627;
}
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_1);
x_628 = lean_ctor_get(x_618, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_618, 1);
lean_inc(x_629);
if (lean_is_exclusive(x_618)) {
 lean_ctor_release(x_618, 0);
 lean_ctor_release(x_618, 1);
 x_630 = x_618;
} else {
 lean_dec_ref(x_618);
 x_630 = lean_box(0);
}
if (lean_is_scalar(x_630)) {
 x_631 = lean_alloc_ctor(1, 2, 0);
} else {
 x_631 = x_630;
}
lean_ctor_set(x_631, 0, x_628);
lean_ctor_set(x_631, 1, x_629);
return x_631;
}
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
lean_dec(x_549);
lean_dec(x_548);
lean_dec(x_547);
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_543);
lean_dec(x_542);
lean_dec(x_541);
lean_dec(x_1);
x_632 = lean_ctor_get(x_616, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_616, 1);
lean_inc(x_633);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_634 = x_616;
} else {
 lean_dec_ref(x_616);
 x_634 = lean_box(0);
}
if (lean_is_scalar(x_634)) {
 x_635 = lean_alloc_ctor(1, 2, 0);
} else {
 x_635 = x_634;
}
lean_ctor_set(x_635, 0, x_632);
lean_ctor_set(x_635, 1, x_633);
return x_635;
}
}
}
else
{
lean_object* x_650; lean_object* x_651; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_650 = lean_ctor_get(x_530, 0);
lean_inc(x_650);
lean_dec(x_530);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_528);
return x_651;
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
