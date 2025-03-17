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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
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
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___rarg(x_1, x_2, x_13, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*1);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_16, 1);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_17);
if (x_21 == 0)
{
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_11);
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_17, 0);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_11);
lean_ctor_set(x_16, 1, x_23);
return x_16;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_16, 0);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_26 = x_17;
} else {
 lean_dec_ref(x_17);
 x_26 = lean_box(0);
}
if (lean_is_scalar(x_26)) {
 x_27 = lean_alloc_ctor(0, 1, 1);
} else {
 x_27 = x_26;
}
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_11);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_16, 1);
lean_dec(x_30);
x_31 = !lean_is_exclusive(x_17);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = 0;
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_32);
return x_16;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
lean_inc(x_33);
lean_dec(x_17);
x_34 = 0;
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_34);
lean_ctor_set(x_16, 1, x_35);
return x_16;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_16, 0);
lean_inc(x_36);
lean_dec(x_16);
x_37 = lean_ctor_get(x_17, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_38 = x_17;
} else {
 lean_dec_ref(x_17);
 x_38 = lean_box(0);
}
x_39 = 0;
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 1, 1);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_42 = lean_ctor_get(x_5, 0);
x_43 = lean_ctor_get(x_5, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_5);
lean_inc(x_2);
lean_inc(x_1);
x_44 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___rarg(x_1, x_2, x_3, x_4, x_43);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = 1;
lean_inc(x_2);
lean_inc(x_1);
x_48 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_45, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_46);
x_52 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_52, 0, x_3);
lean_ctor_set(x_52, 1, x_51);
lean_ctor_set(x_52, 2, x_50);
x_53 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___rarg(x_1, x_2, x_49, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_54, sizeof(void*)*1);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_57 = x_53;
} else {
 lean_dec_ref(x_53);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_54, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_59 = x_54;
} else {
 lean_dec_ref(x_54);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 1, 1);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_47);
if (lean_is_scalar(x_57)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_57;
}
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_63 = x_53;
} else {
 lean_dec_ref(x_53);
 x_63 = lean_box(0);
}
x_64 = lean_ctor_get(x_54, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_65 = x_54;
} else {
 lean_dec_ref(x_54);
 x_65 = lean_box(0);
}
x_66 = 0;
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 1, 1);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_66);
if (lean_is_scalar(x_63)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_63;
}
lean_ctor_set(x_68, 0, x_62);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
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
