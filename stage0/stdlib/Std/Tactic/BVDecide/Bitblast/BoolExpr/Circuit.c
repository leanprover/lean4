// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BoolExpr.Circuit
// Imports: Std.Sat.AIG.CachedGates Std.Sat.AIG.CachedGatesLemmas Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic
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
lean_object* l_Std_Sat_AIG_mkNotCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkXorCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkBEqCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_empty___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached(lean_object*);
lean_object* l_Std_Sat_AIG_mkAndCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_apply_2(x_6, x_4, x_8);
return x_9;
}
case 1:
{
uint8_t x_10; lean_object* x_11; 
lean_dec(x_6);
x_10 = lean_ctor_get_uint8(x_5, 0);
lean_dec(x_5);
x_11 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_4, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 0);
lean_inc(x_12);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_4, x_12, x_6, lean_box(0));
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Std_Sat_AIG_mkNotCached___rarg(x_1, x_2, x_14, x_15);
return x_16;
}
default: 
{
uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_17 = lean_ctor_get_uint8(x_5, sizeof(void*)*2);
x_18 = lean_ctor_get(x_5, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_20 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_4, x_18, x_6, lean_box(0));
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_2);
lean_inc(x_1);
x_23 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_21, x_19, x_6, lean_box(0));
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_23, 0);
lean_ctor_set(x_23, 0, x_22);
switch (x_17) {
case 0:
{
lean_object* x_26; 
x_26 = l_Std_Sat_AIG_mkAndCached___rarg(x_1, x_2, x_25, x_23);
return x_26;
}
case 1:
{
lean_object* x_27; 
x_27 = l_Std_Sat_AIG_mkXorCached___rarg(x_1, x_2, x_25, x_23);
return x_27;
}
default: 
{
lean_object* x_28; 
x_28 = l_Std_Sat_AIG_mkBEqCached___rarg(x_1, x_2, x_25, x_23);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 0);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_23);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_30);
switch (x_17) {
case 0:
{
lean_object* x_32; 
x_32 = l_Std_Sat_AIG_mkAndCached___rarg(x_1, x_2, x_29, x_31);
return x_32;
}
case 1:
{
lean_object* x_33; 
x_33 = l_Std_Sat_AIG_mkXorCached___rarg(x_1, x_2, x_29, x_31);
return x_33;
}
default: 
{
lean_object* x_34; 
x_34 = l_Std_Sat_AIG_mkBEqCached___rarg(x_1, x_2, x_29, x_31);
return x_34;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Std_Sat_AIG_empty___rarg(x_1, x_2);
x_8 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_7, x_4, x_5, lean_box(0));
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_ofBoolExprCached___rarg), 6, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 1:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
default: 
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_box(x_13);
x_17 = lean_apply_3(x_5, x_16, x_14, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter___rarg), 5, 0);
return x_3;
}
}
lean_object* initialize_Std_Sat_AIG_CachedGates(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_AIG_CachedGates(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_CachedGatesLemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
