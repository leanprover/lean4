// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Clz
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const Std.Sat.AIG.If
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__1(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_ite___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_ofNat(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_ofNat(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_6, x_3);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_10 = l_BitVec_ofNat(x_3, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_BitVec_ofNat(x_3, x_11);
x_13 = l_BitVec_sub(x_3, x_10, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = l_BitVec_ofNat(x_3, x_6);
x_15 = l_BitVec_sub(x_3, x_13, x_14);
lean_dec(x_14);
lean_dec(x_13);
x_16 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___rarg(x_1, x_2, x_3, x_4, x_15);
lean_dec(x_15);
x_17 = lean_nat_add(x_6, x_11);
x_18 = lean_array_fget(x_5, x_6);
lean_dec(x_6);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_div(x_18, x_19);
x_21 = lean_nat_land(x_11, x_18);
lean_dec(x_18);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_eq(x_21, x_22);
lean_dec(x_21);
if (x_23 == 0)
{
uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_24 = 1;
x_25 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_24);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_16);
lean_ctor_set(x_26, 2, x_7);
lean_inc(x_2);
lean_inc(x_1);
x_27 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_4, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_4 = x_28;
x_6 = x_17;
x_7 = x_29;
goto _start;
}
else
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = 0;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_16);
lean_ctor_set(x_33, 2, x_7);
lean_inc(x_2);
lean_inc(x_1);
x_34 = l_Std_Sat_AIG_RefVec_ite___rarg(x_1, x_2, x_3, x_4, x_33);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_4 = x_35;
x_6 = x_17;
x_7 = x_36;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___rarg___boxed), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_BitVec_ofNat(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_BitVec_ofNat(x_3, x_3);
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___rarg(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___rarg(x_1, x_2, x_3, x_4, x_5, x_8, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_cast___at_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_If(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin, lean_io_mk_world());
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
