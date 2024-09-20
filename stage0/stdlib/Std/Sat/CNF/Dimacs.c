// Lean compiler output
// Module: Std.Sat.CNF.Dimacs
// Imports: Std.Sat.CNF.Basic Std.Sat.CNF.RelabelFin
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
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Sat_CNF_dimacs___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_dimacs___boxed(lean_object*);
static lean_object* l_Std_Sat_Literal_dimacs___closed__1;
static lean_object* l_Std_Sat_CNF_Clause_dimacs___closed__1;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
static lean_object* l_Std_Sat_CNF_dimacs___closed__2;
static lean_object* l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___closed__1;
static lean_object* l_Std_Sat_Literal_dimacs___closed__2;
static lean_object* l_Std_Sat_CNF_dimacs___closed__4;
static lean_object* l_Std_Sat_CNF_dimacs___closed__3;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_dimacs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___boxed(lean_object*, lean_object*);
static lean_object* l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___closed__1;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object*);
lean_object* l_Std_Sat_CNF_maxLiteral(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_dimacs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_Literal_dimacs(lean_object*);
static lean_object* _init_l_Std_Sat_Literal_dimacs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_Literal_dimacs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_Literal_dimacs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
x_6 = lean_unbox(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_8 = l_Std_Sat_Literal_dimacs___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_Std_Sat_Literal_dimacs___closed__2;
x_11 = lean_string_append(x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_13 = l_Std_Sat_Literal_dimacs___closed__2;
x_14 = lean_string_append(x_13, x_12);
lean_dec(x_12);
x_15 = lean_string_append(x_14, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_Literal_dimacs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_Literal_dimacs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Std_Sat_Literal_dimacs(x_3);
x_6 = lean_string_append(x_1, x_5);
lean_dec(x_5);
x_7 = l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Std_Sat_CNF_Clause_dimacs___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("0", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_dimacs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Std_Sat_Literal_dimacs___closed__2;
x_3 = l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1(x_2, x_1);
x_4 = l_Std_Sat_CNF_Clause_dimacs___closed__1;
x_5 = lean_string_append(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_Clause_dimacs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_CNF_Clause_dimacs(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Std_Sat_CNF_Clause_dimacs(x_3);
x_6 = lean_string_append(x_1, x_5);
lean_dec(x_5);
x_7 = l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("p cnf ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Sat_CNF_dimacs___closed__2;
x_2 = l_Std_Sat_CNF_dimacs___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_Sat_CNF_dimacs___closed__3;
x_2 = l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___closed__1;
x_3 = lean_string_append(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_lengthTRAux___rarg(x_1, x_2);
lean_inc(x_1);
x_4 = l_Std_Sat_CNF_maxLiteral(x_1);
x_5 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Std_Sat_CNF_dimacs___closed__4;
x_7 = lean_string_append(x_6, x_5);
lean_dec(x_5);
x_8 = l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___closed__1;
x_9 = lean_string_append(x_7, x_8);
x_10 = l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1(x_9, x_1);
lean_dec(x_1);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_11, x_12);
lean_dec(x_11);
x_14 = l___private_Init_Data_Repr_0__Nat_reprFast(x_13);
x_15 = l_Std_Sat_CNF_dimacs___closed__2;
x_16 = lean_string_append(x_15, x_14);
lean_dec(x_14);
x_17 = l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___closed__1;
x_18 = lean_string_append(x_16, x_17);
x_19 = lean_string_append(x_18, x_5);
lean_dec(x_5);
x_20 = l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___closed__1;
x_21 = lean_string_append(x_19, x_20);
x_22 = l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1(x_21, x_1);
lean_dec(x_1);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Dimacs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_RelabelFin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_Literal_dimacs___closed__1 = _init_l_Std_Sat_Literal_dimacs___closed__1();
lean_mark_persistent(l_Std_Sat_Literal_dimacs___closed__1);
l_Std_Sat_Literal_dimacs___closed__2 = _init_l_Std_Sat_Literal_dimacs___closed__2();
lean_mark_persistent(l_Std_Sat_Literal_dimacs___closed__2);
l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___closed__1 = _init_l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at_Std_Sat_CNF_Clause_dimacs___spec__1___closed__1);
l_Std_Sat_CNF_Clause_dimacs___closed__1 = _init_l_Std_Sat_CNF_Clause_dimacs___closed__1();
lean_mark_persistent(l_Std_Sat_CNF_Clause_dimacs___closed__1);
l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___closed__1 = _init_l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at_Std_Sat_CNF_dimacs___spec__1___closed__1);
l_Std_Sat_CNF_dimacs___closed__1 = _init_l_Std_Sat_CNF_dimacs___closed__1();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__1);
l_Std_Sat_CNF_dimacs___closed__2 = _init_l_Std_Sat_CNF_dimacs___closed__2();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__2);
l_Std_Sat_CNF_dimacs___closed__3 = _init_l_Std_Sat_CNF_dimacs___closed__3();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__3);
l_Std_Sat_CNF_dimacs___closed__4 = _init_l_Std_Sat_CNF_dimacs___closed__4();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
