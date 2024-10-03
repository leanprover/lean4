// Lean compiler output
// Module: Std.Sat.CNF.RelabelFin
// Imports: Init.Data.List.Nat.Basic Std.Sat.CNF.Relabel
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
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at_Std_Sat_CNF_Clause_maxLiteral___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_Clause_maxLiteral___spec__3___boxed(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_relabel___rarg(lean_object*, lean_object*);
uint8_t l_List_any___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object*);
static lean_object* l_Std_Sat_CNF_relabelFin___closed__1;
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
static lean_object* l_Std_Sat_CNF_maxLiteral___closed__1;
lean_object* l_List_replicateTR___rarg(lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___rarg___lambda__1___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Sat_CNF_Clause_maxLiteral___spec__1(lean_object*, lean_object*);
lean_object* l_List_reverse___rarg(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_Clause_maxLiteral___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Sat_CNF_maxLiteral___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_max_x3f___at_Std_Sat_CNF_Clause_maxLiteral___spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_Std_Sat_CNF_Clause_maxLiteral___spec__1(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
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
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
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
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_Clause_maxLiteral___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_nat_dec_le(x_1, x_3);
if (x_5 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
x_1 = x_3;
x_2 = x_4;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at_Std_Sat_CNF_Clause_maxLiteral___spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = l_List_foldl___at_Std_Sat_CNF_Clause_maxLiteral___spec__3(x_3, x_4);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_maxLiteral(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l_List_mapTR_loop___at_Std_Sat_CNF_Clause_maxLiteral___spec__1(x_1, x_2);
x_4 = l_List_max_x3f___at_Std_Sat_CNF_Clause_maxLiteral___spec__2(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_Clause_maxLiteral___spec__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Std_Sat_CNF_Clause_maxLiteral___spec__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_max_x3f___at_Std_Sat_CNF_Clause_maxLiteral___spec__2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_List_max_x3f___at_Std_Sat_CNF_Clause_maxLiteral___spec__2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterMapTR_go___at_Std_Sat_CNF_maxLiteral___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_array_to_list(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Std_Sat_CNF_Clause_maxLiteral(x_4);
if (lean_obj_tag(x_6) == 0)
{
x_1 = x_5;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_array_push(x_2, x_8);
x_1 = x_5;
x_2 = x_9;
goto _start;
}
}
}
}
static lean_object* _init_l_Std_Sat_CNF_maxLiteral___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_maxLiteral(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Std_Sat_CNF_maxLiteral___closed__1;
x_3 = l_List_filterMapTR_go___at_Std_Sat_CNF_maxLiteral___spec__1(x_1, x_2);
x_4 = l_List_max_x3f___at_Std_Sat_CNF_Clause_maxLiteral___spec__2(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_numLiterals(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_CNF_maxLiteral(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(0u);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Std_Sat_CNF_RelabelFin_0__Std_Sat_CNF_numLiterals_match__1_splitter___rarg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(0u);
return x_4;
}
else
{
lean_inc(x_2);
return x_2;
}
}
}
static lean_object* _init_l_Std_Sat_CNF_relabelFin___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Sat_CNF_instDecidableExistsMemOfDecidableEq___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Std_Sat_CNF_relabelFin___closed__1;
lean_inc(x_1);
x_3 = l_List_any___rarg(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_List_lengthTRAux___rarg(x_1, x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = l_List_replicateTR___rarg(x_5, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = l_Std_Sat_CNF_numLiterals(x_1);
x_9 = lean_alloc_closure((void*)(l_Std_Sat_CNF_relabelFin___lambda__1___boxed), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = l_Std_Sat_CNF_relabel___rarg(x_9, x_1);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_relabelFin___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_CNF_relabelFin___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init_Data_List_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_Relabel(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_Relabel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_CNF_maxLiteral___closed__1 = _init_l_Std_Sat_CNF_maxLiteral___closed__1();
lean_mark_persistent(l_Std_Sat_CNF_maxLiteral___closed__1);
l_Std_Sat_CNF_relabelFin___closed__1 = _init_l_Std_Sat_CNF_relabelFin___closed__1();
lean_mark_persistent(l_Std_Sat_CNF_relabelFin___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
