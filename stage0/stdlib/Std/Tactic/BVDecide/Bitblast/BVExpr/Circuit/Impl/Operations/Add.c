// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Basic public import Std.Sat.AIG.LawfulVecOperator import Init.Omega
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkXorCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Bool_toNat(uint8_t);
lean_object* lean_nat_lor(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_nat_land(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_RefVec_countKnown___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_38; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_38 = !lean_is_exclusive(x_1);
if (x_38 == 0)
{
x_5 = x_1;
x_6 = x_38;
goto block_37;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_38;
goto block_37;
}
block_37:
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_36; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
x_9 = x_2;
x_10 = x_36;
goto block_35;
}
else
{
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; uint8_t x_14; uint8_t x_34; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_34 = !lean_is_exclusive(x_3);
if (x_34 == 0)
{
x_13 = x_3;
x_14 = x_34;
goto block_33;
}
else
{
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; uint8_t x_32; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
x_17 = x_4;
x_18 = x_32;
goto block_31;
}
else
{
lean_inc(x_15);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_19; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_7);
x_19 = x_17;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_30, 0, x_7);
x_19 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_20; 
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_8);
if (x_14 == 0)
{
x_20 = x_13;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_11);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_12);
x_20 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_21; 
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_15);
x_21 = x_9;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_26, 0, x_15);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_16);
if (x_6 == 0)
{
lean_ctor_set(x_5, 2, x_21);
lean_ctor_set(x_5, 1, x_20);
lean_ctor_set(x_5, 0, x_19);
x_22 = x_5;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_5);
lean_dec_ref(x_1);
x_6 = lean_apply_3(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___redArg(x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add_0__Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_28; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Std_Sat_AIG_mkXorCached___redArg(x_1, x_2, x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
x_12 = x_9;
x_13 = x_28;
goto block_27;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_26; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
x_16 = x_7;
x_17 = x_26;
goto block_25;
}
else
{
lean_inc(x_14);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_18; 
if (x_17 == 0)
{
x_18 = x_16;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_14);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_15);
x_18 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_19; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_18);
lean_ctor_set(x_12, 0, x_11);
x_19 = x_12;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_18);
x_19 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_20; 
x_20 = l_Std_Sat_AIG_mkXorCached___redArg(x_1, x_2, x_10, x_19);
return x_20;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_75; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_7);
lean_dec_ref(x_4);
lean_inc_ref(x_6);
lean_inc_ref(x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_9 = l_Std_Sat_AIG_mkXorCached___redArg(x_1, x_2, x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get(x_9, 1);
x_75 = !lean_is_exclusive(x_9);
if (x_75 == 0)
{
x_12 = x_9;
x_13 = x_75;
goto block_74;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_73; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_73 = !lean_is_exclusive(x_5);
if (x_73 == 0)
{
x_16 = x_5;
x_17 = x_73;
goto block_72;
}
else
{
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_box(0);
x_17 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; uint8_t x_71; 
x_18 = lean_ctor_get(x_6, 0);
x_19 = lean_ctor_get_uint8(x_6, sizeof(void*)*1);
x_71 = !lean_is_exclusive(x_6);
if (x_71 == 0)
{
x_20 = x_6;
x_21 = x_71;
goto block_70;
}
else
{
lean_inc(x_18);
lean_dec(x_6);
x_20 = lean_box(0);
x_21 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_69; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_69 = !lean_is_exclusive(x_7);
if (x_69 == 0)
{
x_24 = x_7;
x_25 = x_69;
goto block_68;
}
else
{
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_box(0);
x_25 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_66;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_67, 0, x_22);
lean_ctor_set_uint8(x_67, sizeof(void*)*1, x_23);
x_26 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_27; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_26);
lean_ctor_set(x_12, 0, x_11);
x_27 = x_12;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_11);
lean_ctor_set(x_65, 1, x_26);
x_27 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_63; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_28 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_10, x_27);
x_29 = lean_ctor_get(x_28, 0);
x_30 = lean_ctor_get(x_28, 1);
x_63 = !lean_is_exclusive(x_28);
if (x_63 == 0)
{
x_31 = x_28;
x_32 = x_63;
goto block_62;
}
else
{
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_28);
x_31 = lean_box(0);
x_32 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_33; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_14);
x_33 = x_20;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_61, 0, x_14);
x_33 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_34; 
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_15);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_18);
x_34 = x_16;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_18);
x_34 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_35; 
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_19);
if (x_32 == 0)
{
lean_ctor_set(x_31, 1, x_34);
lean_ctor_set(x_31, 0, x_33);
x_35 = x_31;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_33);
lean_ctor_set(x_57, 1, x_34);
x_35 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_55; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_36 = l_Std_Sat_AIG_mkGateCached___redArg(x_1, x_2, x_29, x_35);
x_37 = lean_ctor_get(x_36, 0);
x_38 = lean_ctor_get(x_36, 1);
x_55 = !lean_is_exclusive(x_36);
if (x_55 == 0)
{
x_39 = x_36;
x_40 = x_55;
goto block_54;
}
else
{
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_36);
x_39 = lean_box(0);
x_40 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; uint8_t x_53; 
x_41 = lean_ctor_get(x_30, 0);
x_42 = lean_ctor_get_uint8(x_30, sizeof(void*)*1);
x_53 = !lean_is_exclusive(x_30);
if (x_53 == 0)
{
x_43 = x_30;
x_44 = x_53;
goto block_52;
}
else
{
lean_inc(x_41);
lean_dec(x_30);
x_43 = lean_box(0);
x_44 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_41);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_42);
x_45 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_46; 
if (x_40 == 0)
{
lean_ctor_set(x_39, 0, x_45);
x_46 = x_39;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_38);
x_46 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_47; 
x_47 = l_Std_Sat_AIG_mkOrCached___redArg(x_1, x_2, x_37, x_46);
return x_47;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; uint8_t x_21; 
lean_inc_ref(x_4);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_5 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderOut___redArg(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_7);
lean_dec_ref(x_5);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_FullAdderInput_cast___redArg(x_4);
x_9 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(x_1, x_2, x_6, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get_uint8(x_7, sizeof(void*)*1);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
x_14 = x_7;
x_15 = x_21;
goto block_20;
}
else
{
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_box(0);
x_15 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_13);
x_16 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_11);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_28; lean_object* x_29; 
x_28 = lean_nat_dec_lt(x_7, x_3);
if (x_28 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_9);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_41 = lean_array_fget_borrowed(x_5, x_7);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_shiftr(x_41, x_42);
x_44 = lean_nat_land(x_42, x_41);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_eq(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_28);
x_29 = x_47;
goto block_39;
}
else
{
uint8_t x_48; lean_object* x_49; 
x_48 = 0;
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_48);
x_29 = x_49;
goto block_39;
}
}
block_27:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set(x_12, 2, x_8);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_13 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdder___redArg(x_1, x_2, x_4, x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_16);
lean_dec_ref(x_13);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_14, sizeof(void*)*1);
lean_dec_ref(x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_7, x_19);
lean_dec(x_7);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_mul(x_17, x_21);
lean_dec(x_17);
x_23 = l_Bool_toNat(x_18);
x_24 = lean_nat_lor(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = lean_array_push(x_9, x_24);
x_4 = x_15;
x_7 = x_20;
x_8 = x_16;
x_9 = x_25;
goto _start;
}
block_39:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_array_fget_borrowed(x_6, x_7);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_shiftr(x_30, x_31);
x_33 = lean_nat_land(x_31, x_30);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_28);
x_10 = x_29;
x_11 = x_36;
goto block_27;
}
else
{
uint8_t x_37; lean_object* x_38; 
x_37 = 0;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_10 = x_29;
x_11 = x_38;
goto block_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = ((lean_object*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___closed__0));
x_10 = lean_mk_empty_array_with_capacity(x_3);
x_11 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_go___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = l_Std_Sat_AIG_RefVec_countKnown___redArg(x_3, x_4, x_6);
x_9 = l_Std_Sat_AIG_RefVec_countKnown___redArg(x_3, x_4, x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; uint8_t x_18; 
lean_inc_ref(x_7);
lean_inc_ref(x_6);
x_18 = !lean_is_exclusive(x_5);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_5, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_5, 0);
lean_dec(x_20);
x_11 = x_5;
x_12 = x_18;
goto block_17;
}
else
{
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_6);
lean_ctor_set(x_11, 0, x_7);
x_13 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_6);
x_13 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_14; 
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(x_1, x_2, x_3, x_4, x_13);
lean_dec_ref(x_13);
return x_14;
}
}
}
else
{
lean_object* x_21; 
x_21 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd_blast___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_5);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
}
#ifdef __cplusplus
}
#endif
