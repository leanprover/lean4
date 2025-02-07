// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.GetLsbD Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Expr
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
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__2_splitter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__1_splitter(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1___closed__1;
lean_object* l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__1_splitter___rarg(uint8_t, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__1_splitter___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__2_splitter___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; 
x_6 = 0;
x_7 = l_Std_Sat_AIG_mkConstCached___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_go___spec__5(x_1, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_array_fget(x_8, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
lean_dec(x_2);
lean_inc(x_3);
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_3, x_1, x_4);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_3);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_3, x_8, x_6);
if (x_5 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_10, 0, x_9);
x_13 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_3, x_12, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Std_Tactic_BVDecide_BVPred_mkEq___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__8(x_3, x_14, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_10, 0);
lean_ctor_set(x_10, 0, x_9);
x_20 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(x_3, x_19, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Std_Tactic_BVDecide_BVPred_mkUlt___at_Std_Tactic_BVDecide_BVExpr_bitblast_go___spec__20(x_3, x_21, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_2);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_28 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_26, x_1, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_30);
x_31 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1(x_29, x_2);
lean_dec(x_2);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_32 = lean_ctor_get(x_2, 0);
x_33 = lean_ctor_get(x_2, 1);
x_34 = lean_ctor_get(x_2, 2);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_2);
lean_inc(x_32);
x_35 = l_Std_Tactic_BVDecide_BVExpr_bitblast_go(x_32, x_1, x_33);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_34);
x_39 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1(x_36, x_38);
lean_dec(x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__2_splitter___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(x_6);
x_9 = lean_apply_4(x_2, x_4, x_5, x_8, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_3(x_3, x_10, x_11, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__2_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__2_splitter___rarg), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__1_splitter___rarg(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (x_1 == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_inc(x_3);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__1_splitter(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__1_splitter___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__1_splitter___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__1_splitter___rarg(x_4, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_GetLsbD(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1___closed__1 = _init_l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_blastGetLsbD___at_Std_Tactic_BVDecide_BVPred_bitblast___spec__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
