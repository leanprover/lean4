// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BoolExpr.Circuit
// Imports: Std.Sat.AIG.CachedGates Std.Sat.AIG.CachedGatesLemmas Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic Std.Sat.AIG.If
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
lean_object* l_Std_Sat_AIG_mkImpCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkIfCached___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
case 3:
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
case 2:
{
lean_object* x_28; 
x_28 = l_Std_Sat_AIG_mkBEqCached___rarg(x_1, x_2, x_25, x_23);
return x_28;
}
default: 
{
lean_object* x_29; 
x_29 = l_Std_Sat_AIG_mkImpCached___rarg(x_1, x_2, x_25, x_23);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_23, 0);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_23);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
switch (x_17) {
case 0:
{
lean_object* x_33; 
x_33 = l_Std_Sat_AIG_mkAndCached___rarg(x_1, x_2, x_30, x_32);
return x_33;
}
case 1:
{
lean_object* x_34; 
x_34 = l_Std_Sat_AIG_mkXorCached___rarg(x_1, x_2, x_30, x_32);
return x_34;
}
case 2:
{
lean_object* x_35; 
x_35 = l_Std_Sat_AIG_mkBEqCached___rarg(x_1, x_2, x_30, x_32);
return x_35;
}
default: 
{
lean_object* x_36; 
x_36 = l_Std_Sat_AIG_mkImpCached___rarg(x_1, x_2, x_30, x_32);
return x_36;
}
}
}
}
default: 
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_5);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_5, 0);
x_39 = lean_ctor_get(x_5, 1);
x_40 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_41 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_4, x_38, x_6, lean_box(0));
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_42, x_39, x_6, lean_box(0));
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_inc(x_2);
lean_inc(x_1);
x_47 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_45, x_40, x_6, lean_box(0));
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 2, x_49);
lean_ctor_set(x_5, 1, x_46);
lean_ctor_set(x_5, 0, x_43);
x_50 = l_Std_Sat_AIG_mkIfCached___rarg(x_1, x_2, x_48, x_5);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_51 = lean_ctor_get(x_5, 0);
x_52 = lean_ctor_get(x_5, 1);
x_53 = lean_ctor_get(x_5, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_5);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_54 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_4, x_51, x_6, lean_box(0));
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_6);
lean_inc(x_2);
lean_inc(x_1);
x_57 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_55, x_52, x_6, lean_box(0));
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_2);
lean_inc(x_1);
x_60 = l_Std_Tactic_BVDecide_ofBoolExprCached_go___rarg(x_1, x_2, lean_box(0), x_58, x_53, x_6, lean_box(0));
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_59);
lean_ctor_set(x_63, 2, x_62);
x_64 = l_Std_Sat_AIG_mkIfCached___rarg(x_1, x_2, x_61, x_63);
return x_64;
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
case 3:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_box(x_14);
x_18 = lean_apply_3(x_6, x_17, x_15, x_16);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_3(x_5, x_19, x_20, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BoolExpr_Circuit_0__Std_Tactic_BVDecide_ofBoolExprCached_go_match__3_splitter___rarg), 6, 0);
return x_3;
}
}
lean_object* initialize_Std_Sat_AIG_CachedGates(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_CachedGatesLemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin, lean_object*);
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
res = initialize_Std_Sat_AIG_If(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
