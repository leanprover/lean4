// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Extract
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorExtractTargetBlastExtract___rarg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorExtractTargetBlastExtract___rarg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkConstCached___rarg(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorExtractTargetBlastExtract(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_9, x_3);
if (x_12 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
return x_11;
}
else
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_nat_add(x_7, x_9);
x_14 = lean_nat_dec_lt(x_13, x_5);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_9, x_15);
lean_dec(x_9);
if (x_14 == 0)
{
lean_object* x_17; 
lean_dec(x_13);
lean_inc(x_8);
x_17 = lean_array_push(x_11, x_8);
x_9 = x_16;
x_10 = lean_box(0);
x_11 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_fget(x_6, x_13);
lean_dec(x_13);
x_20 = lean_array_push(x_11, x_19);
x_9 = x_16;
x_10 = lean_box(0);
x_11 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___rarg___boxed), 11, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 3);
x_10 = 0;
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Std_Sat_AIG_mkConstCached___rarg(x_1, x_2, x_4, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_nat_dec_le(x_9, x_8);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_nat_dec_lt(x_9, x_6);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1;
x_18 = lean_array_push(x_17, x_14);
lean_ctor_set(x_11, 1, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_14);
x_19 = lean_array_fget(x_7, x_9);
x_20 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1;
x_21 = lean_array_push(x_20, x_19);
lean_ctor_set(x_11, 1, x_21);
return x_11;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1;
x_24 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___rarg(x_1, x_2, x_3, x_13, x_6, x_7, x_9, x_14, x_22, lean_box(0), x_23);
lean_dec(x_2);
lean_dec(x_1);
lean_ctor_set(x_11, 1, x_24);
return x_11;
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_11, 0);
x_26 = lean_ctor_get(x_11, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_11);
x_27 = lean_nat_dec_le(x_9, x_8);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_nat_dec_lt(x_9, x_6);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1;
x_30 = lean_array_push(x_29, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
x_32 = lean_array_fget(x_7, x_9);
x_33 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1;
x_34 = lean_array_push(x_33, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1;
x_38 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract_go___rarg(x_1, x_2, x_3, x_25, x_6, x_7, x_9, x_26, x_36, lean_box(0), x_37);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___boxed), 5, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorExtractTargetBlastExtract___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorExtractTargetBlastExtract(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorExtractTargetBlastExtract___rarg___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorExtractTargetBlastExtract___rarg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_bitblast_instLawfulVecOperatorExtractTargetBlastExtract___rarg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_AIG_LawfulVecOperator(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Extract(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1 = _init_l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVExpr_bitblast_blastExtract___rarg___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
