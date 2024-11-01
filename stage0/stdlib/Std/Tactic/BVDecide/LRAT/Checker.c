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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__2;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_check(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at_Std_Tactic_BVDecide_LRAT_check___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(lean_object*);
lean_object* l_instBEqProd___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__5;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_check___boxed(lean_object*, lean_object*);
lean_object* l_instDecidableEqBool___boxed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object*, lean_object*);
uint8_t l_List_elem___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at_Std_Tactic_BVDecide_LRAT_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___rarg___boxed(lean_object*, lean_object*);
static lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(uint8_t, uint8_t);
static lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__4;
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_array_mk(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_check___closed__1;
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Tactic_BVDecide_LRAT_check___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Tactic_BVDecide_LRAT_check___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Tactic_BVDecide_LRAT_check___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___rarg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(x_2, x_7);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_9);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(x_2, x_11);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
}
}
static lean_object* _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqPosFin___rarg___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__1;
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_instDecidableEqBool___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__3;
x_2 = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___rarg), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__2;
x_2 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__4;
x_3 = lean_alloc_closure((void*)(l_instBEqProd___rarg), 4, 2);
lean_closure_set(x_3, 0, x_1);
lean_closure_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = lean_array_to_list(x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
lean_dec(x_6);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_4, x_9);
x_3 = x_10;
x_4 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_push(x_4, x_16);
x_3 = x_10;
x_4 = x_17;
goto _start;
}
}
case 1:
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_3, 1);
lean_inc(x_19);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_array_push(x_4, x_9);
x_3 = x_19;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
x_25 = lean_ctor_get(x_9, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_array_push(x_4, x_26);
x_3 = x_19;
x_4 = x_27;
goto _start;
}
}
case 2:
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_9);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_31 = lean_ctor_get(x_9, 0);
x_32 = lean_ctor_get(x_9, 1);
x_33 = lean_ctor_get(x_9, 2);
x_34 = lean_ctor_get(x_9, 3);
x_35 = lean_ctor_get(x_9, 4);
x_36 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__5;
lean_inc(x_32);
lean_inc(x_33);
x_37 = l_List_elem___rarg(x_36, x_33, x_32);
if (x_37 == 0)
{
lean_free_object(x_9);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
x_3 = x_29;
goto _start;
}
else
{
lean_object* x_39; 
x_39 = lean_array_push(x_4, x_9);
x_3 = x_29;
x_4 = x_39;
goto _start;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_ctor_get(x_9, 1);
x_43 = lean_ctor_get(x_9, 2);
x_44 = lean_ctor_get(x_9, 3);
x_45 = lean_ctor_get(x_9, 4);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_9);
x_46 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__5;
lean_inc(x_42);
lean_inc(x_43);
x_47 = l_List_elem___rarg(x_46, x_43, x_42);
if (x_47 == 0)
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
x_3 = x_29;
goto _start;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set(x_49, 2, x_43);
lean_ctor_set(x_49, 3, x_44);
lean_ctor_set(x_49, 4, x_45);
x_50 = lean_array_push(x_4, x_49);
x_3 = x_29;
x_4 = x_50;
goto _start;
}
}
}
default: 
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
lean_dec(x_3);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_array_push(x_4, x_9);
x_3 = x_52;
x_4 = x_54;
goto _start;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_9, 0);
lean_inc(x_56);
lean_dec(x_9);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = lean_array_push(x_4, x_57);
x_3 = x_52;
x_4 = x_58;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at_Std_Tactic_BVDecide_LRAT_check___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
switch (lean_obj_tag(x_6)) {
case 0:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(x_2, x_3, x_8, x_7);
lean_dec(x_7);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = 2;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 2);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(x_2, x_3, x_15, x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_14);
x_20 = 2;
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_3 = x_21;
x_4 = x_14;
goto _start;
}
}
case 2:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_6, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_6, 3);
lean_inc(x_26);
x_27 = lean_ctor_get(x_6, 4);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(x_2, x_3, x_24, x_25, x_26, x_27);
lean_dec(x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_28);
lean_dec(x_23);
x_31 = 2;
return x_31;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
x_3 = x_32;
x_4 = x_23;
goto _start;
}
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_4, 1);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_6, 0);
lean_inc(x_35);
lean_dec(x_6);
x_36 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(x_2, x_3, x_35);
lean_dec(x_35);
x_3 = x_36;
x_4 = x_34;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_check___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
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
lean_inc(x_2);
x_5 = l_Std_Sat_CNF_numLiterals(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = l_List_mapTR_loop___at_Std_Tactic_BVDecide_LRAT_check___spec__1(x_2, x_7, x_4, x_8);
x_10 = l_Std_Tactic_BVDecide_LRAT_check___closed__1;
x_11 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2(x_2, x_7, x_9, x_10);
x_12 = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at_Std_Tactic_BVDecide_LRAT_check___spec__3(x_2, x_7, x_3, x_11);
lean_dec(x_7);
lean_dec(x_2);
x_13 = 0;
x_14 = l_Std_Tactic_BVDecide_LRAT_Internal_instDecidableEqResult(x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Tactic_BVDecide_LRAT_check___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at_Std_Tactic_BVDecide_LRAT_check___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at_Std_Tactic_BVDecide_LRAT_check___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Std_Tactic_BVDecide_LRAT_Internal_lratChecker___at_Std_Tactic_BVDecide_LRAT_check___spec__3(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_dec(x_1);
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
lean_inc(x_9);
lean_dec(x_7);
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
lean_inc(x_13);
lean_dec(x_7);
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
lean_inc(x_17);
x_18 = lean_ctor_get(x_7, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 4);
lean_inc(x_19);
lean_dec(x_7);
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
lean_inc(x_21);
lean_dec(x_7);
x_22 = lean_apply_1(x_5, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___rarg___boxed), 6, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___rarg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Checker_0__Std_Tactic_BVDecide_LRAT_check_match__1_splitter(x_1, x_2);
lean_dec(x_1);
return x_3;
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
l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__1 = _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__1();
lean_mark_persistent(l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__1);
l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__2 = _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__2();
lean_mark_persistent(l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__2);
l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__3 = _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__3();
lean_mark_persistent(l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__3);
l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__4 = _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__4();
lean_mark_persistent(l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__4);
l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__5 = _init_l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__5();
lean_mark_persistent(l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_check___spec__2___closed__5);
l_Std_Tactic_BVDecide_LRAT_check___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_check___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_check___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
