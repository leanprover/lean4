// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_19; lean_object* x_20; 
x_19 = lean_nat_dec_lt(x_7, x_3);
if (x_19 == 0)
{
lean_object* x_31; 
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_4);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_array_fget_borrowed(x_5, x_7);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_shiftr(x_32, x_33);
x_35 = lean_nat_land(x_33, x_32);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_35, x_36);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_19);
x_20 = x_38;
goto block_30;
}
else
{
uint8_t x_39; lean_object* x_40; 
x_39 = 0;
x_40 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set_uint8(x_40, sizeof(void*)*1, x_39);
x_20 = x_40;
goto block_30;
}
}
block_18:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_11, 2, x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(x_1, x_2, x_4, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_4 = x_13;
x_7 = x_16;
x_8 = x_14;
goto _start;
}
block_30:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_21 = lean_array_fget_borrowed(x_6, x_7);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_shiftr(x_21, x_22);
x_24 = lean_nat_land(x_22, x_21);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_eq(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_19);
x_9 = x_20;
x_10 = x_27;
goto block_18;
}
else
{
uint8_t x_28; lean_object* x_29; 
x_28 = 0;
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_28);
x_9 = x_20;
x_10 = x_29;
goto block_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_4);
x_8 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_9);
lean_dec_ref(x_5);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(x_1, x_2, x_6, x_3, x_8, x_9, x_10, x_7);
lean_dec_ref(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
