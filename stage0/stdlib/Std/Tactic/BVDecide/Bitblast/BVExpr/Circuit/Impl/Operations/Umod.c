// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
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
lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_BitVec_ofNat(x_3, x_9);
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(x_3, x_10);
lean_dec(x_10);
lean_inc(x_11);
lean_inc(x_8);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_12 = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_11);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_15 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(x_1, x_2, x_3, x_13, x_3, x_7, x_8, x_3, x_9, x_11, x_11);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; 
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 0, x_14);
x_20 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_17, x_15);
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_inc(x_21);
lean_dec(x_14);
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_22);
lean_ctor_set(x_15, 1, x_7);
lean_ctor_set(x_15, 0, x_23);
x_24 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_17, x_15);
lean_dec(x_3);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = lean_ctor_get(x_15, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_15);
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_29 = x_14;
} else {
 lean_dec_ref(x_14);
 x_29 = lean_box(0);
}
if (lean_is_scalar(x_29)) {
 x_30 = lean_alloc_ctor(0, 1, 1);
} else {
 x_30 = x_29;
}
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*1, x_28);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_7);
lean_ctor_set(x_31, 2, x_26);
x_32 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_25, x_31);
lean_dec(x_3);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get(x_5, 0);
x_34 = lean_ctor_get(x_5, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_5);
x_35 = lean_unsigned_to_nat(0u);
x_36 = l_BitVec_ofNat(x_3, x_35);
x_37 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(x_3, x_36);
lean_dec(x_36);
lean_inc(x_37);
lean_inc(x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_37);
lean_inc(x_2);
lean_inc(x_1);
x_39 = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(x_1, x_2, x_3, x_4, x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_37);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(x_1, x_2, x_3, x_40, x_3, x_33, x_34, x_3, x_35, x_37, x_37);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 2);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 lean_ctor_release(x_42, 2);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_48 = x_41;
} else {
 lean_dec_ref(x_41);
 x_48 = lean_box(0);
}
if (lean_is_scalar(x_48)) {
 x_49 = lean_alloc_ctor(0, 1, 1);
} else {
 x_49 = x_48;
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_47);
if (lean_is_scalar(x_45)) {
 x_50 = lean_alloc_ctor(0, 3, 0);
} else {
 x_50 = x_45;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_33);
lean_ctor_set(x_50, 2, x_44);
x_51 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_43, x_50);
lean_dec(x_3);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
