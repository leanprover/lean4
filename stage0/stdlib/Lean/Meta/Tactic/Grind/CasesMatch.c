// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CasesMatch
// Imports: Lean.Meta.Tactic.Util Lean.Meta.Tactic.Cases Lean.Meta.Match.MatcherApp Lean.Meta.Tactic.Grind.MatchCond
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_updateTags(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_casesMatch_updateTags___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__2;
static lean_object* l_Lean_Meta_Grind_casesMatch___lambda__2___closed__1;
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_casesMatch___lambda__2___closed__6;
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCondCandidate(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_updateTags___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToAlt(lean_object*);
lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCondCandidate___boxed(lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_casesMatch___lambda__2___closed__5;
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_casesMatch___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_casesMatch_updateTags___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_casesMatch___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaBoundedTelescope(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* l_Lean_Meta_withNewEqs___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_get_match_equations_for(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_Grind_casesMatch___lambda__2___closed__4;
lean_object* l_Lean_MVarId_setTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_Grind_casesMatch___lambda__2___closed__2;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_Grind_casesMatch___lambda__2___closed__3;
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCondCandidate(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCondCandidate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isMatchCondCandidate(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToAlt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; size_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_3);
x_6 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_3);
lean_inc(x_4);
x_7 = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToAlt(x_4);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Expr_forallE___override(x_2, x_3, x_4, x_5);
x_9 = lean_ptr_addr(x_3);
if (x_6 == 0)
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_9, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_4);
x_11 = l_Lean_Expr_forallE___override(x_2, x_3, x_7, x_5);
return x_11;
}
else
{
size_t x_12; size_t x_13; uint8_t x_14; 
x_12 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_13 = lean_ptr_addr(x_7);
x_14 = lean_usize_dec_eq(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
x_15 = l_Lean_Expr_forallE___override(x_2, x_3, x_7, x_5);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_5, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_8);
x_17 = l_Lean_Expr_forallE___override(x_2, x_3, x_7, x_5);
return x_17;
}
else
{
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
}
}
else
{
lean_object* x_18; size_t x_19; uint8_t x_20; 
x_18 = l_Lean_Meta_Grind_markAsMatchCond(x_3);
x_19 = lean_ptr_addr(x_18);
x_20 = lean_usize_dec_eq(x_9, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_8);
lean_dec(x_4);
x_21 = l_Lean_Expr_forallE___override(x_2, x_18, x_7, x_5);
return x_21;
}
else
{
size_t x_22; size_t x_23; uint8_t x_24; 
x_22 = lean_ptr_addr(x_4);
lean_dec(x_4);
x_23 = lean_ptr_addr(x_7);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_8);
x_25 = l_Lean_Expr_forallE___override(x_2, x_18, x_7, x_5);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_5, x_5);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_8);
x_27 = l_Lean_Expr_forallE___override(x_2, x_18, x_7, x_5);
return x_27;
}
else
{
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; uint8_t x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
lean_inc(x_5);
x_8 = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToAlt(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
lean_inc(x_6);
x_11 = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(x_6, x_10);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Expr_forallE___override(x_4, x_5, x_6, x_7);
x_13 = lean_ptr_addr(x_5);
lean_dec(x_5);
x_14 = lean_ptr_addr(x_8);
x_15 = lean_usize_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_6);
x_16 = l_Lean_Expr_forallE___override(x_4, x_8, x_11, x_7);
return x_16;
}
else
{
size_t x_17; size_t x_18; uint8_t x_19; 
x_17 = lean_ptr_addr(x_6);
lean_dec(x_6);
x_18 = lean_ptr_addr(x_11);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_12);
x_20 = l_Lean_Expr_forallE___override(x_4, x_8, x_11, x_7);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_7, x_7);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
x_22 = l_Lean_Expr_forallE___override(x_4, x_8, x_11, x_7);
return x_22;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_4);
return x_12;
}
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___lambda__1(x_1, x_2, x_5);
return x_6;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___lambda__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = 0;
x_14 = 1;
x_15 = 1;
x_16 = l_Lean_Meta_mkForallFVars(x_3, x_11, x_13, x_14, x_15, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_mkLambdaFVars(x_2, x_17, x_13, x_14, x_13, x_15, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_4);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_4);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_4);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__1___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_3);
x_11 = l_Lean_Meta_withNewEqs___rarg(x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = l_Lean_Expr_getAppFn(x_2);
x_10 = lean_ctor_get(x_3, 4);
lean_inc(x_10);
x_11 = l_Lean_mkAppN(x_9, x_10);
lean_dec(x_10);
x_12 = l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__2;
x_13 = l_Lean_Expr_app___override(x_11, x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = lean_infer_type(x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_3, 6);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_array_get_size(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__2___boxed), 9, 2);
lean_closure_set(x_20, 0, x_1);
lean_closure_set(x_20, 1, x_17);
x_21 = 0;
x_22 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_15, x_19, x_20, x_21, x_4, x_5, x_6, x_7, x_16);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_casesMatch_updateTags___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_15 = lean_array_uget(x_4, x_6);
x_16 = l_Lean_Expr_mvarId_x21(x_15);
lean_dec(x_15);
lean_inc(x_7);
lean_inc(x_2);
x_17 = l_Lean_Name_num___override(x_2, x_7);
x_18 = l_Lean_MVarId_setTag(x_16, x_17, x_8, x_9, x_10, x_11, x_12);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_7, x_20);
lean_dec(x_7);
x_22 = 1;
x_23 = lean_usize_add(x_6, x_22);
x_6 = x_23;
x_7 = x_21;
x_12 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_updateTags(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_getTag(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_array_get_size(x_2);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_size(x_2);
x_16 = 0;
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_casesMatch_updateTags___spec__1(x_2, x_9, x_14, x_2, x_15, x_16, x_12, x_3, x_4, x_5, x_6, x_10);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_11);
lean_dec(x_11);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = l_Lean_instInhabitedExpr;
x_27 = l_outOfBounds___rarg(x_26);
x_28 = l_Lean_Expr_mvarId_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_MVarId_setTag(x_28, x_9, x_3, x_4, x_5, x_6, x_10);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_array_fget(x_2, x_24);
x_31 = l_Lean_Expr_mvarId_x21(x_30);
lean_dec(x_30);
x_32 = l_Lean_MVarId_setTag(x_31, x_9, x_3, x_4, x_5, x_6, x_10);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_casesMatch_updateTags___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_15 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_Grind_casesMatch_updateTags___spec__1(x_1, x_2, x_3, x_4, x_13, x_14, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch_updateTags___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_casesMatch_updateTags(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Lean_Meta_Grind_casesMatch___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___rarg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_mvarId_x21(x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Expr_mvarId_x21(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = lean_get_match_equations_for(x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_to_list(x_5);
x_18 = l_Lean_Expr_const___override(x_16, x_17);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
x_20 = l_Lean_mkAppN(x_18, x_19);
lean_dec(x_19);
x_21 = l_Lean_Expr_app___override(x_20, x_2);
x_22 = lean_ctor_get(x_1, 6);
lean_inc(x_22);
x_23 = l_Lean_mkAppN(x_21, x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_1, 8);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_array_get_size(x_24);
lean_dec(x_24);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_23);
x_26 = lean_infer_type(x_23, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = l___private_Lean_Meta_Tactic_Grind_CasesMatch_0__Lean_Meta_Grind_addMatchCondsToSplitter(x_27, x_25);
x_30 = 2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Meta_forallMetaBoundedTelescope(x_29, x_25, x_30, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_mkAppN(x_23, x_34);
x_36 = l_Lean_mkAppN(x_35, x_3);
lean_inc(x_4);
x_37 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_4, x_36, x_7, x_8, x_9, x_10, x_33);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Meta_Grind_casesMatch_updateTags(x_4, x_34, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_array_to_list(x_34);
x_43 = lean_box(0);
x_44 = l_List_mapTR_loop___at_Lean_Meta_Grind_casesMatch___spec__1(x_42, x_43);
lean_ctor_set(x_39, 0, x_44);
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_39, 1);
lean_inc(x_45);
lean_dec(x_39);
x_46 = lean_array_to_list(x_34);
x_47 = lean_box(0);
x_48 = l_List_mapTR_loop___at_Lean_Meta_Grind_casesMatch___spec__1(x_46, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_34);
x_50 = !lean_is_exclusive(x_39);
if (x_50 == 0)
{
return x_39;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_39, 0);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_31);
if (x_54 == 0)
{
return x_31;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_31, 0);
x_56 = lean_ctor_get(x_31, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_31);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_58 = !lean_is_exclusive(x_26);
if (x_58 == 0)
{
return x_26;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_26, 0);
x_60 = lean_ctor_get(x_26, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_26);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
return x_13;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_13);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("casesMatch", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_casesMatch___lambda__2___closed__1;
x_2 = l_Lean_Meta_Grind_casesMatch___lambda__2___closed__2;
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`match`-expression expected", 27, 27);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_casesMatch___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_casesMatch___lambda__2___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Meta_matchMatcherApp_x3f___at___private_Lean_Meta_Tactic_Split_0__Lean_Meta_Split_generalizeMatchDiscrs_mkNewTarget___spec__1(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_indentExpr(x_1);
x_13 = l_Lean_Meta_Grind_casesMatch___lambda__2___closed__5;
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = l_Lean_Meta_Grind_casesMatch___lambda__2___closed__7;
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_Grind_casesMatch___lambda__2___closed__3;
x_19 = l_Lean_Meta_throwTacticEx___rarg(x_18, x_2, x_17, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_21);
lean_inc(x_2);
x_22 = l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls(x_2, x_1, x_21, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_2);
x_27 = l_Lean_MVarId_getType(x_2, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_21, 2);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
x_31 = lean_box(0);
x_32 = l_Lean_Meta_Grind_casesMatch___lambda__1(x_21, x_25, x_26, x_2, x_30, x_31, x_3, x_4, x_5, x_6, x_29);
lean_dec(x_26);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_27, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_37 = l_Lean_Meta_getLevel(x_33, x_3, x_4, x_5, x_6, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_array_set(x_35, x_36, x_38);
lean_dec(x_36);
x_41 = lean_box(0);
x_42 = l_Lean_Meta_Grind_casesMatch___lambda__1(x_21, x_25, x_26, x_2, x_40, x_41, x_3, x_4, x_5, x_6, x_39);
lean_dec(x_26);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
return x_37;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_37, 0);
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_37);
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
uint8_t x_47; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_27);
if (x_47 == 0)
{
return x_27;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_27, 0);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_27);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_22);
if (x_51 == 0)
{
return x_22;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_22, 0);
x_53 = lean_ctor_get(x_22, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_22);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_9);
if (x_55 == 0)
{
return x_9;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 0);
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_9);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_casesMatch___lambda__2), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_casesMatch___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_casesMatch___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Match_MatcherApp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_MatchCond(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_MatcherApp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_MatchCond(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1 = _init_l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__1);
l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__2 = _init_l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_casesMatch_mkMotiveAndRefls___closed__2);
l_Lean_Meta_Grind_casesMatch___lambda__2___closed__1 = _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_casesMatch___lambda__2___closed__1);
l_Lean_Meta_Grind_casesMatch___lambda__2___closed__2 = _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_casesMatch___lambda__2___closed__2);
l_Lean_Meta_Grind_casesMatch___lambda__2___closed__3 = _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_casesMatch___lambda__2___closed__3);
l_Lean_Meta_Grind_casesMatch___lambda__2___closed__4 = _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_casesMatch___lambda__2___closed__4);
l_Lean_Meta_Grind_casesMatch___lambda__2___closed__5 = _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_casesMatch___lambda__2___closed__5);
l_Lean_Meta_Grind_casesMatch___lambda__2___closed__6 = _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_casesMatch___lambda__2___closed__6);
l_Lean_Meta_Grind_casesMatch___lambda__2___closed__7 = _init_l_Lean_Meta_Grind_casesMatch___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_casesMatch___lambda__2___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
