// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
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
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___rarg(x_1, x_2, x_3, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 1;
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_9, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_ctor_set(x_5, 1, x_10);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_14);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___rarg(x_1, x_2, x_13, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Std_Sat_AIG_mkNotCached___rarg(x_1, x_2, x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_22 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___rarg(x_1, x_2, x_3, x_4, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = 1;
lean_inc(x_2);
lean_inc(x_1);
x_26 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_23, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_28);
lean_inc(x_2);
lean_inc(x_1);
x_31 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___rarg(x_1, x_2, x_27, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Std_Sat_AIG_mkNotCached___rarg(x_1, x_2, x_32, x_33);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVPred_mkUlt___rarg), 5, 0);
return x_2;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
