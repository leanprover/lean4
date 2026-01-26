// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Ult
// Imports: public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry public import Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
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
static const lean_ctor_object l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0_value;
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_8 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(x_1, x_2, x_3, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_8);
x_11 = 1;
x_12 = ((lean_object*)(l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0));
lean_ctor_set(x_5, 1, x_10);
x_13 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_12);
x_14 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(x_1, x_2, x_9, x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_14, 1);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_11);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set_uint8(x_21, sizeof(void*)*1, x_11);
lean_ctor_set(x_14, 1, x_21);
return x_14;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_24 = x_15;
} else {
 lean_dec_ref(x_15);
 x_24 = lean_box(0);
}
if (lean_is_scalar(x_24)) {
 x_25 = lean_alloc_ctor(0, 1, 1);
} else {
 x_25 = x_24;
}
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_11);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_14, 1);
lean_dec(x_28);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = 0;
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_30);
return x_14;
}
else
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_15, 0);
lean_inc(x_31);
lean_dec(x_15);
x_32 = 0;
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_32);
lean_ctor_set(x_14, 1, x_33);
return x_14;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_14, 0);
lean_inc(x_34);
lean_dec(x_14);
x_35 = lean_ctor_get(x_15, 0);
lean_inc(x_35);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_36 = x_15;
} else {
 lean_dec_ref(x_15);
 x_36 = lean_box(0);
}
x_37 = 0;
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 1, 1);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_40 = lean_ctor_get(x_5, 0);
x_41 = lean_ctor_get(x_5, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_5);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_42 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(x_1, x_2, x_3, x_4, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc_ref(x_44);
lean_dec_ref(x_42);
x_45 = 1;
x_46 = ((lean_object*)(l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0));
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_44);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_3);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_46);
x_49 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(x_1, x_2, x_43, x_48);
x_50 = lean_ctor_get(x_49, 1);
lean_inc_ref(x_50);
x_51 = lean_ctor_get_uint8(x_50, sizeof(void*)*1);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_55 = x_50;
} else {
 lean_dec_ref(x_50);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 1);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_45);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_49, 0);
lean_inc_ref(x_58);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_59 = x_49;
} else {
 lean_dec_ref(x_49);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_50, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 x_61 = x_50;
} else {
 lean_dec_ref(x_50);
 x_61 = lean_box(0);
}
x_62 = 0;
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 1, 1);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_62);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_mkUlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
