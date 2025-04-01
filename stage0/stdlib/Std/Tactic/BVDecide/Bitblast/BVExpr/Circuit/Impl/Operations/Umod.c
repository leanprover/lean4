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
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod(lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_BitVec_ofNat(x_3, x_6);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___rarg(x_1, x_2, x_3, x_4, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = !lean_is_exclusive(x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_13);
lean_ctor_set(x_5, 1, x_10);
lean_ctor_set(x_5, 0, x_13);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_14 = l_Std_Tactic_BVDecide_BVPred_mkEq___rarg(x_1, x_2, x_3, x_9, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 0;
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_17);
x_19 = 1;
x_20 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_19);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg(x_1, x_2, x_3, x_15, x_3, x_18, x_20, x_12, x_13, x_3, x_6, x_10, x_10);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_dec(x_24);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; 
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 0, x_16);
x_26 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_23, x_21);
lean_dec(x_3);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 0, x_29);
x_30 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_23, x_21);
lean_dec(x_3);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 2);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_ctor_get(x_16, 0);
lean_inc(x_33);
x_34 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_35 = x_16;
} else {
 lean_dec_ref(x_16);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(0, 1, 1);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_34);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_12);
lean_ctor_set(x_37, 2, x_32);
x_38 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_31, x_37);
lean_dec(x_3);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_39 = lean_ctor_get(x_5, 0);
x_40 = lean_ctor_get(x_5, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_5);
lean_inc(x_10);
lean_inc(x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Std_Tactic_BVDecide_BVPred_mkEq___rarg(x_1, x_2, x_3, x_9, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = 0;
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_6);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_45);
x_47 = 1;
x_48 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_48, 0, x_6);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_47);
lean_inc(x_10);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_49 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___rarg(x_1, x_2, x_3, x_43, x_3, x_46, x_48, x_39, x_40, x_3, x_6, x_10, x_10);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 2);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 lean_ctor_release(x_49, 2);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_44, 0);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_44, sizeof(void*)*1);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 x_55 = x_44;
} else {
 lean_dec_ref(x_44);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 1);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_54);
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(0, 3, 0);
} else {
 x_57 = x_52;
}
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_39);
lean_ctor_set(x_57, 2, x_51);
x_58 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_50, x_57);
lean_dec(x_3);
return x_58;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___rarg), 5, 0);
return x_2;
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
