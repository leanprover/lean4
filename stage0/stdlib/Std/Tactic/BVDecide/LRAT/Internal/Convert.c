// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Convert
// Imports: Std.Sat.CNF.RelabelFin Std.Tactic.BVDecide.LRAT.Internal.Formula
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_relabelFin(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_relabel___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___boxed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift(lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter___boxed(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lambda__1___boxed(lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Std_Sat_CNF_relabelFin(x_1);
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__1;
x_4 = l_Std_Sat_CNF_relabel___rarg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_mk(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_array_to_list(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_Clause_convertLRAT_x27(x_1, x_5);
if (lean_obj_tag(x_7) == 0)
{
x_2 = x_6;
goto _start;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_array_push(x_3, x_7);
x_2 = x_6;
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 0);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_array_push(x_3, x_13);
x_2 = x_6;
x_3 = x_14;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___closed__1;
x_4 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___spec__1(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterMapTR_go___at_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray_match__1_splitter(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_2 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift(x_1);
x_3 = l_Std_Sat_CNF_numLiterals(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
x_6 = l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27(x_5, x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
x_9 = lean_array_mk(x_8);
x_10 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(x_5, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_2);
lean_inc(x_3);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___rarg___boxed), 3, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Tactic_BVDecide_LRAT_Internal_Convert_0__Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27_match__1_splitter(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Convert(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_RelabelFin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_CNF_lift___closed__1);
l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___closed__1 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_CNF_convertLRAT_x27___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
