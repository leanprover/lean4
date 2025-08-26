// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Checker
// Imports: Std.Tactic.BVDecide.LRAT.Actions Std.Tactic.BVDecide.LRAT.Internal.Convert Std.Tactic.BVDecide.LRAT.Internal.LRATChecker Std.Tactic.BVDecide.LRAT.Internal.LRATCheckerSound Std.Sat.CNF
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_check(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_check_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_check_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_check_spec__1___lam__0(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_check___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_check_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_check_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at___Std_Tactic_BVDecide_LRAT_check_spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(uint8_t, uint8_t);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at___Std_Tactic_BVDecide_LRAT_check_spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_check___closed__0;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_check_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(x_1, x_6);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_8);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(x_1, x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_2 = x_11;
x_3 = x_13;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_check_spec__1___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
return x_1;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_check_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_array_to_list(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec_ref(x_2);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_inc_ref(x_5);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec_ref(x_5);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_9, 1);
x_14 = lean_ctor_get(x_9, 2);
x_15 = lean_alloc_closure((void*)(l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_check_spec__1___lam__0___boxed), 2, 0);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___boxed), 3, 1);
lean_closure_set(x_16, 0, x_1);
x_17 = l_instBEqOfDecidableEq___redArg(x_16);
x_18 = l_instBEqOfDecidableEq___redArg(x_15);
x_19 = l_instBEqProd___redArg(x_17, x_18);
lean_inc(x_13);
lean_inc_ref(x_14);
x_20 = l_List_elem___redArg(x_19, x_14, x_13);
if (x_20 == 0)
{
lean_dec_ref(x_9);
x_2 = x_8;
goto _start;
}
else
{
goto block_12;
}
}
else
{
goto block_12;
}
block_12:
{
lean_object* x_10; 
x_10 = lean_array_push(x_3, x_9);
x_2 = x_8;
x_3 = x_10;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at___Std_Tactic_BVDecide_LRAT_check_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_dec_ref(x_3);
x_6 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_6);
lean_dec_ref(x_5);
x_7 = lean_box(0);
x_8 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(x_1, x_2, x_7, x_6);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = 2;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_dec_ref(x_3);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_5);
x_16 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(x_1, x_2, x_14, x_15);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
uint8_t x_19; 
lean_dec_ref(x_16);
lean_dec(x_13);
x_19 = 2;
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec_ref(x_16);
x_2 = x_20;
x_3 = x_13;
goto _start;
}
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec_ref(x_3);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_24);
x_25 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_5, 4);
lean_inc_ref(x_26);
lean_dec_ref(x_5);
x_27 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(x_1, x_2, x_23, x_24, x_25, x_26);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec_ref(x_27);
lean_dec(x_22);
x_30 = 2;
return x_30;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec_ref(x_27);
x_2 = x_31;
x_3 = x_22;
goto _start;
}
}
default: 
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_3, 1);
lean_inc(x_33);
lean_dec_ref(x_3);
x_34 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_34);
lean_dec_ref(x_5);
x_35 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(x_1, x_2, x_34);
lean_dec_ref(x_34);
x_2 = x_35;
x_3 = x_33;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_check___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_check(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
lean_inc(x_2);
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(x_2);
x_4 = lean_array_to_list(x_1);
x_5 = l_Std_Sat_CNF_numLiterals(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_check_spec__0(x_7, x_4, x_8);
x_10 = l_Std_Tactic_BVDecide_LRAT_check___closed__0;
lean_inc(x_7);
x_11 = l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_check_spec__1(x_7, x_9, x_10);
x_12 = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at___Std_Tactic_BVDecide_LRAT_check_spec__2(x_7, x_3, x_11);
lean_dec(x_7);
x_13 = 0;
x_14 = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_check_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at___Std_Tactic_BVDecide_LRAT_check_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_check_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = l_List_filterMapTR_go___at___Std_Tactic_BVDecide_LRAT_check_spec__1___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at___Std_Tactic_BVDecide_LRAT_check_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at___Std_Tactic_BVDecide_LRAT_check_spec__2(x_1, x_2, x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_check___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_LRAT_check(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec_ref(x_1);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_7);
x_10 = lean_apply_2(x_3, x_8, x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_7);
x_14 = lean_apply_3(x_4, x_11, x_12, x_13);
return x_14;
}
case 2:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 2);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_7, 3);
lean_inc_ref(x_18);
x_19 = lean_ctor_get(x_7, 4);
lean_inc_ref(x_19);
lean_dec_ref(x_7);
x_20 = lean_apply_5(x_6, x_15, x_16, x_17, x_18, x_19);
return x_20;
}
default: 
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_21);
lean_dec_ref(x_7);
x_22 = lean_apply_1(x_5, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Checker(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATChecker(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_LRATCheckerSound(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_LRAT_check___closed__0 = _init_l_Std_Tactic_BVDecide_LRAT_check___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_check___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
