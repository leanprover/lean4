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
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_58; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_58 = !lean_is_exclusive(x_5);
if (x_58 == 0)
{
x_8 = x_5;
x_9 = x_58;
goto block_57;
}
else
{
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_10 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(x_1, x_2, x_3, x_4, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_10);
x_13 = 1;
x_14 = ((lean_object*)(l_Std_Tactic_BVDecide_BVPred_mkUlt___redArg___closed__0));
if (x_9 == 0)
{
lean_ctor_set(x_8, 1, x_12);
x_15 = x_8;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_6);
lean_ctor_set(x_56, 1, x_12);
x_15 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set(x_16, 2, x_14);
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(x_1, x_2, x_11, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_18);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_35; 
x_20 = lean_ctor_get(x_17, 0);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_17, 1);
lean_dec(x_36);
x_21 = x_17;
x_22 = x_35;
goto block_34;
}
else
{
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_box(0);
x_22 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_33; 
x_23 = lean_ctor_get(x_18, 0);
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
x_24 = x_18;
x_25 = x_33;
goto block_32;
}
else
{
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_31, 0, x_23);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_13);
if (x_22 == 0)
{
lean_ctor_set(x_21, 1, x_26);
x_27 = x_21;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_53; 
x_37 = lean_ctor_get(x_17, 0);
x_53 = !lean_is_exclusive(x_17);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_17, 1);
lean_dec(x_54);
x_38 = x_17;
x_39 = x_53;
goto block_52;
}
else
{
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_box(0);
x_39 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_51; 
x_40 = lean_ctor_get(x_18, 0);
x_51 = !lean_is_exclusive(x_18);
if (x_51 == 0)
{
x_41 = x_18;
x_42 = x_51;
goto block_50;
}
else
{
lean_inc(x_40);
lean_dec(x_18);
x_41 = lean_box(0);
x_42 = x_51;
goto block_50;
}
block_50:
{
uint8_t x_43; lean_object* x_44; 
x_43 = 0;
if (x_42 == 0)
{
x_44 = x_41;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_49, 0, x_40);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_43);
if (x_39 == 0)
{
lean_ctor_set(x_38, 1, x_44);
x_45 = x_38;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_37);
lean_ctor_set(x_47, 1, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
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
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Ult(builtin);
}
#ifdef __cplusplus
}
#endif
