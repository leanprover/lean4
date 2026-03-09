// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
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
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_41; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_41 = !lean_is_exclusive(x_5);
if (x_41 == 0)
{
x_8 = x_5;
x_9 = x_41;
goto block_40;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_BitVec_ofNat(x_3, x_10);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(x_3, x_11);
lean_dec(x_11);
lean_inc_ref(x_12);
lean_inc_ref(x_7);
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_12);
lean_ctor_set(x_8, 0, x_7);
x_13 = x_8;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_7);
lean_ctor_set(x_39, 1, x_12);
x_13 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_36; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_14 = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(x_1, x_2, x_3, x_4, x_13);
lean_dec_ref(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
lean_dec_ref(x_14);
lean_inc_ref(x_12);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(x_1, x_2, x_3, x_15, x_3, x_6, x_7, x_3, x_10, x_12, x_12);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get(x_17, 2);
x_36 = !lean_is_exclusive(x_17);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_17, 1);
lean_dec(x_37);
x_20 = x_17;
x_21 = x_36;
goto block_35;
}
else
{
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_17);
x_20 = lean_box(0);
x_21 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_34; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*1);
x_34 = !lean_is_exclusive(x_16);
if (x_34 == 0)
{
x_24 = x_16;
x_25 = x_34;
goto block_33;
}
else
{
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_23);
x_26 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_27; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 0, x_26);
x_27 = x_20;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_19);
x_27 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_28; 
x_28 = l_Std_Sat_AIG_RefVec_ite___redArg(x_1, x_2, x_3, x_18, x_27);
lean_dec(x_3);
return x_28;
}
}
}
}
}
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
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin);
}
#ifdef __cplusplus
}
#endif
