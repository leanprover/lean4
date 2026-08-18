// Lean compiler output
// Module: Lean.Util.CollectLooseBVars
// Imports: public import Lean.Expr
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_looseBVarRange(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_CollectLooseBVars_main(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__0;
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__1;
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__2;
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__3;
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__4;
static lean_once_cell_t l_Lean_Expr_collectLooseBVars___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_collectLooseBVars___closed__5;
LEAN_EXPORT lean_object* l_Lean_Expr_collectLooseBVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
_start:
{
lean_object* v_zero_6_; uint8_t v_isZero_7_; 
v_zero_6_ = lean_unsigned_to_nat(0u);
v_isZero_7_ = lean_nat_dec_eq(v_x_4_, v_zero_6_);
if (v_isZero_7_ == 1)
{
lean_dec(v_x_5_);
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_box(2);
return v___x_8_;
}
else
{
lean_object* v_val_9_; lean_object* v___x_11_; uint8_t v_isShared_12_; uint8_t v_isSharedCheck_16_; 
v_val_9_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_16_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_16_ == 0)
{
v___x_11_ = v_x_3_;
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
else
{
lean_inc(v_val_9_);
lean_dec(v_x_3_);
v___x_11_ = lean_box(0);
v_isShared_12_ = v_isSharedCheck_16_;
goto v_resetjp_10_;
}
v_resetjp_10_:
{
lean_object* v___x_14_; 
if (v_isShared_12_ == 0)
{
v___x_14_ = v___x_11_;
goto v_reusejp_13_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v_val_9_);
v___x_14_ = v_reuseFailAlloc_15_;
goto v_reusejp_13_;
}
v_reusejp_13_:
{
return v___x_14_;
}
}
}
}
else
{
lean_object* v_keyArray_17_; lean_object* v_valueArray_18_; lean_object* v___x_19_; uint8_t v_isSome_20_; 
v_keyArray_17_ = lean_ctor_get(v_m_1_, 1);
v_valueArray_18_ = lean_ctor_get(v_m_1_, 2);
v___x_19_ = lean_array_fget_borrowed(v_keyArray_17_, v_x_5_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
lean_dec(v_x_4_);
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_21_; 
v___x_21_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_21_, 0, v_x_5_);
return v___x_21_;
}
else
{
lean_object* v_val_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_29_; 
lean_dec(v_x_5_);
v_val_22_ = lean_ctor_get(v_x_3_, 0);
v_isSharedCheck_29_ = !lean_is_exclusive(v_x_3_);
if (v_isSharedCheck_29_ == 0)
{
v___x_24_ = v_x_3_;
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_val_22_);
lean_dec(v_x_3_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_29_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_27_; 
if (v_isShared_25_ == 0)
{
v___x_27_ = v___x_24_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v_val_22_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
}
}
else
{
lean_object* v_one_30_; lean_object* v_n_31_; lean_object* v___y_33_; 
v_one_30_ = lean_unsigned_to_nat(1u);
v_n_31_ = lean_nat_sub(v_x_4_, v_one_30_);
lean_dec(v_x_4_);
if (v_isSome_20_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v___x_41_; uint8_t v_isSome_42_; 
v___x_41_ = lean_array_fget_borrowed(v_valueArray_18_, v_x_5_);
v_isSome_42_ = lean_noption_is_some(v___x_41_);
if (v_isSome_42_ == 0)
{
goto v___jp_39_;
}
else
{
lean_object* v_val_43_; lean_object* v_fst_44_; lean_object* v_snd_45_; lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v_val_48_; uint8_t v___y_50_; uint8_t v___x_57_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v_fst_44_ = lean_ctor_get(v_val_43_, 0);
lean_inc(v_fst_44_);
v_snd_45_ = lean_ctor_get(v_val_43_, 1);
lean_inc(v_snd_45_);
v_fst_46_ = lean_ctor_get(v_query_2_, 0);
v_snd_47_ = lean_ctor_get(v_query_2_, 1);
lean_inc(v___x_41_);
v_val_48_ = lean_noption_get(v___x_41_);
v___x_57_ = lean_nat_dec_eq(v_fst_44_, v_fst_46_);
lean_dec(v_fst_44_);
if (v___x_57_ == 0)
{
lean_dec(v_snd_45_);
v___y_50_ = v___x_57_;
goto v___jp_49_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = lean_expr_eqv(v_snd_45_, v_snd_47_);
lean_dec(v_snd_45_);
v___y_50_ = v___x_58_;
goto v___jp_49_;
}
v___jp_49_:
{
if (v___y_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; uint8_t v___x_53_; 
lean_dec(v_val_48_);
lean_dec(v_val_43_);
v___x_51_ = lean_array_get_size(v_keyArray_17_);
v___x_52_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_53_ = lean_nat_dec_lt(v___x_52_, v___x_51_);
if (v___x_53_ == 0)
{
lean_dec(v___x_52_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_52_;
goto _start;
}
}
else
{
lean_object* v___x_56_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
v___x_56_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_56_, 0, v_x_5_);
lean_ctor_set(v___x_56_, 1, v_val_43_);
lean_ctor_set(v___x_56_, 2, v_val_48_);
return v___x_56_;
}
}
}
}
v___jp_32_:
{
lean_object* v___x_34_; lean_object* v___x_35_; uint8_t v___x_36_; 
v___x_34_ = lean_array_get_size(v_keyArray_17_);
v___x_35_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_36_ = lean_nat_dec_lt(v___x_35_, v___x_34_);
if (v___x_36_ == 0)
{
lean_dec(v___x_35_);
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_3_ = v___y_33_;
v_x_4_ = v_n_31_;
v_x_5_ = v___x_35_;
goto _start;
}
}
v___jp_39_:
{
if (lean_obj_tag(v_x_3_) == 0)
{
lean_object* v___x_40_; 
lean_inc(v_x_5_);
v___x_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_40_, 0, v_x_5_);
v___y_33_ = v___x_40_;
goto v___jp_32_;
}
else
{
v___y_33_ = v_x_3_;
goto v___jp_32_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6___redArg___boxed(lean_object* v_m_59_, lean_object* v_query_60_, lean_object* v_x_61_, lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6___redArg(v_m_59_, v_query_60_, v_x_61_, v_x_62_, v_x_63_);
lean_dec_ref(v_query_60_);
lean_dec_ref(v_m_59_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg(lean_object* v_m_65_, lean_object* v_query_66_){
_start:
{
lean_object* v_keyArray_67_; lean_object* v_fst_68_; lean_object* v_snd_69_; lean_object* v___x_70_; uint64_t v___x_71_; uint64_t v___x_72_; uint64_t v___x_73_; uint64_t v___x_74_; uint64_t v___x_75_; uint64_t v_fold_76_; uint64_t v___x_77_; uint64_t v___x_78_; uint64_t v___x_79_; size_t v___x_80_; size_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_keyArray_67_ = lean_ctor_get(v_m_65_, 1);
v_fst_68_ = lean_ctor_get(v_query_66_, 0);
v_snd_69_ = lean_ctor_get(v_query_66_, 1);
v___x_70_ = lean_array_get_size(v_keyArray_67_);
v___x_71_ = lean_uint64_of_nat(v_fst_68_);
v___x_72_ = l_Lean_Expr_hash(v_snd_69_);
v___x_73_ = lean_uint64_mix_hash(v___x_71_, v___x_72_);
v___x_74_ = 32ULL;
v___x_75_ = lean_uint64_shift_right(v___x_73_, v___x_74_);
v_fold_76_ = lean_uint64_xor(v___x_73_, v___x_75_);
v___x_77_ = 16ULL;
v___x_78_ = lean_uint64_shift_right(v_fold_76_, v___x_77_);
v___x_79_ = lean_uint64_xor(v_fold_76_, v___x_78_);
v___x_80_ = lean_uint64_to_usize(v___x_79_);
v___x_81_ = lean_usize_of_nat(v___x_70_);
v___x_82_ = ((size_t)1ULL);
v___x_83_ = lean_usize_sub(v___x_81_, v___x_82_);
v___x_84_ = lean_usize_land(v___x_80_, v___x_83_);
v___x_85_ = lean_usize_to_nat(v___x_84_);
v___x_86_ = lean_box(0);
v___x_87_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6___redArg(v_m_65_, v_query_66_, v___x_86_, v___x_70_, v___x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg___boxed(lean_object* v_m_88_, lean_object* v_query_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg(v_m_88_, v_query_89_);
lean_dec_ref(v_query_89_);
lean_dec_ref(v_m_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(lean_object* v_m_91_, lean_object* v_query_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg(v_m_91_, v_query_92_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_index_94_; lean_object* v_key_95_; lean_object* v_value_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_103_; 
v_index_94_ = lean_ctor_get(v___x_93_, 0);
v_key_95_ = lean_ctor_get(v___x_93_, 1);
v_value_96_ = lean_ctor_get(v___x_93_, 2);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_103_ == 0)
{
v___x_98_ = v___x_93_;
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_value_96_);
lean_inc(v_key_95_);
lean_inc(v_index_94_);
lean_dec(v___x_93_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_103_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_index_94_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_key_95_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_value_96_);
v___x_101_ = v_reuseFailAlloc_102_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
return v___x_101_;
}
}
}
else
{
lean_object* v___x_104_; 
lean_dec(v___x_93_);
v___x_104_ = lean_box(1);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg___boxed(lean_object* v_m_105_, lean_object* v_query_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_m_105_, v_query_106_);
lean_dec_ref(v_query_106_);
lean_dec_ref(v_m_105_);
return v_res_107_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(lean_object* v_m_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_m_108_, v_a_109_);
if (lean_obj_tag(v___x_110_) == 0)
{
uint8_t v___x_111_; 
lean_dec_ref_known(v___x_110_, 3);
v___x_111_ = 1;
return v___x_111_;
}
else
{
uint8_t v___x_112_; 
v___x_112_ = 0;
return v___x_112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg___boxed(lean_object* v_m_113_, lean_object* v_a_114_){
_start:
{
uint8_t v_res_115_; lean_object* v_r_116_; 
v_res_115_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_m_113_, v_a_114_);
lean_dec_ref(v_a_114_);
lean_dec_ref(v_m_113_);
v_r_116_ = lean_box(v_res_115_);
return v_r_116_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(lean_object* v_m_117_, lean_object* v_query_118_, lean_object* v_x_119_, lean_object* v_x_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_zero_122_; uint8_t v_isZero_123_; 
v_zero_122_ = lean_unsigned_to_nat(0u);
v_isZero_123_ = lean_nat_dec_eq(v_x_120_, v_zero_122_);
if (v_isZero_123_ == 1)
{
lean_dec(v_x_121_);
lean_dec(v_x_120_);
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v___x_124_; 
v___x_124_ = lean_box(2);
return v___x_124_;
}
else
{
lean_object* v_val_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_val_125_ = lean_ctor_get(v_x_119_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_x_119_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v_x_119_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_val_125_);
lean_dec(v_x_119_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_val_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
else
{
lean_object* v_keyArray_133_; lean_object* v_valueArray_134_; lean_object* v___x_135_; uint8_t v_isSome_136_; 
v_keyArray_133_ = lean_ctor_get(v_m_117_, 1);
v_valueArray_134_ = lean_ctor_get(v_m_117_, 2);
v___x_135_ = lean_array_fget_borrowed(v_keyArray_133_, v_x_121_);
v_isSome_136_ = lean_noption_is_some(v___x_135_);
if (v_isSome_136_ == 0)
{
lean_dec(v_x_120_);
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v___x_137_; 
v___x_137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_137_, 0, v_x_121_);
return v___x_137_;
}
else
{
lean_object* v_val_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_x_121_);
v_val_138_ = lean_ctor_get(v_x_119_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v_x_119_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v_x_119_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_val_138_);
lean_dec(v_x_119_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_val_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v_one_146_; lean_object* v_n_147_; lean_object* v___y_149_; 
v_one_146_ = lean_unsigned_to_nat(1u);
v_n_147_ = lean_nat_sub(v_x_120_, v_one_146_);
lean_dec(v_x_120_);
if (v_isSome_136_ == 0)
{
goto v___jp_155_;
}
else
{
lean_object* v___x_157_; uint8_t v_isSome_158_; 
v___x_157_ = lean_array_fget_borrowed(v_valueArray_134_, v_x_121_);
v_isSome_158_ = lean_noption_is_some(v___x_157_);
if (v_isSome_158_ == 0)
{
goto v___jp_155_;
}
else
{
lean_object* v_val_159_; uint8_t v___x_160_; 
lean_inc(v___x_135_);
v_val_159_ = lean_noption_get(v___x_135_);
v___x_160_ = lean_nat_dec_eq(v_val_159_, v_query_118_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; uint8_t v___x_163_; 
lean_dec(v_val_159_);
v___x_161_ = lean_array_get_size(v_keyArray_133_);
v___x_162_ = lean_nat_add(v_x_121_, v_one_146_);
lean_dec(v_x_121_);
v___x_163_ = lean_nat_dec_lt(v___x_162_, v___x_161_);
if (v___x_163_ == 0)
{
lean_dec(v___x_162_);
v_x_120_ = v_n_147_;
v_x_121_ = v_zero_122_;
goto _start;
}
else
{
v_x_120_ = v_n_147_;
v_x_121_ = v___x_162_;
goto _start;
}
}
else
{
lean_object* v_val_166_; lean_object* v___x_167_; 
lean_dec(v_n_147_);
lean_dec(v_x_119_);
lean_inc(v___x_157_);
v_val_166_ = lean_noption_get(v___x_157_);
v___x_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_167_, 0, v_x_121_);
lean_ctor_set(v___x_167_, 1, v_val_159_);
lean_ctor_set(v___x_167_, 2, v_val_166_);
return v___x_167_;
}
}
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_150_ = lean_array_get_size(v_keyArray_133_);
v___x_151_ = lean_nat_add(v_x_121_, v_one_146_);
lean_dec(v_x_121_);
v___x_152_ = lean_nat_dec_lt(v___x_151_, v___x_150_);
if (v___x_152_ == 0)
{
lean_dec(v___x_151_);
v_x_119_ = v___y_149_;
v_x_120_ = v_n_147_;
v_x_121_ = v_zero_122_;
goto _start;
}
else
{
v_x_119_ = v___y_149_;
v_x_120_ = v_n_147_;
v_x_121_ = v___x_151_;
goto _start;
}
}
v___jp_155_:
{
if (lean_obj_tag(v_x_119_) == 0)
{
lean_object* v___x_156_; 
lean_inc(v_x_121_);
v___x_156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_156_, 0, v_x_121_);
v___y_149_ = v___x_156_;
goto v___jp_148_;
}
else
{
v___y_149_ = v_x_119_;
goto v___jp_148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg___boxed(lean_object* v_m_168_, lean_object* v_query_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_m_168_, v_query_169_, v_x_170_, v_x_171_, v_x_172_);
lean_dec(v_query_169_);
lean_dec_ref(v_m_168_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(lean_object* v_m_174_, lean_object* v_query_175_){
_start:
{
lean_object* v_keyArray_176_; lean_object* v___x_177_; uint64_t v___x_178_; uint64_t v___x_179_; uint64_t v___x_180_; uint64_t v_fold_181_; uint64_t v___x_182_; uint64_t v___x_183_; uint64_t v___x_184_; size_t v___x_185_; size_t v___x_186_; size_t v___x_187_; size_t v___x_188_; size_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_keyArray_176_ = lean_ctor_get(v_m_174_, 1);
v___x_177_ = lean_array_get_size(v_keyArray_176_);
v___x_178_ = lean_uint64_of_nat(v_query_175_);
v___x_179_ = 32ULL;
v___x_180_ = lean_uint64_shift_right(v___x_178_, v___x_179_);
v_fold_181_ = lean_uint64_xor(v___x_178_, v___x_180_);
v___x_182_ = 16ULL;
v___x_183_ = lean_uint64_shift_right(v_fold_181_, v___x_182_);
v___x_184_ = lean_uint64_xor(v_fold_181_, v___x_183_);
v___x_185_ = lean_uint64_to_usize(v___x_184_);
v___x_186_ = lean_usize_of_nat(v___x_177_);
v___x_187_ = ((size_t)1ULL);
v___x_188_ = lean_usize_sub(v___x_186_, v___x_187_);
v___x_189_ = lean_usize_land(v___x_185_, v___x_188_);
v___x_190_ = lean_usize_to_nat(v___x_189_);
v___x_191_ = lean_box(0);
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_m_174_, v_query_175_, v___x_191_, v___x_177_, v___x_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg___boxed(lean_object* v_m_193_, lean_object* v_query_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_193_, v_query_194_);
lean_dec(v_query_194_);
lean_dec_ref(v_m_193_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(lean_object* v_b_196_, lean_object* v_acc_197_, lean_object* v_i_198_){
_start:
{
lean_object* v___y_200_; lean_object* v_keyArray_208_; lean_object* v_valueArray_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_keyArray_208_ = lean_ctor_get(v_b_196_, 1);
v_valueArray_209_ = lean_ctor_get(v_b_196_, 2);
v___x_210_ = lean_array_get_size(v_keyArray_208_);
v___x_211_ = lean_nat_dec_lt(v_i_198_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec(v_i_198_);
return v_acc_197_;
}
else
{
lean_object* v___x_212_; uint8_t v_isSome_213_; 
v___x_212_ = lean_array_fget_borrowed(v_keyArray_208_, v_i_198_);
v_isSome_213_ = lean_noption_is_some(v___x_212_);
if (v_isSome_213_ == 0)
{
goto v___jp_204_;
}
else
{
lean_object* v___x_214_; uint8_t v_isSome_215_; 
v___x_214_ = lean_array_fget_borrowed(v_valueArray_209_, v_i_198_);
v_isSome_215_ = lean_noption_is_some(v___x_214_);
if (v_isSome_215_ == 0)
{
goto v___jp_204_;
}
else
{
lean_object* v_val_216_; lean_object* v_val_217_; lean_object* v_i_219_; lean_object* v___x_224_; 
lean_inc(v___x_212_);
v_val_216_ = lean_noption_get(v___x_212_);
lean_inc(v___x_214_);
v_val_217_ = lean_noption_get(v___x_214_);
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_acc_197_, v_val_216_);
switch(lean_obj_tag(v___x_224_))
{
case 0:
{
lean_object* v_index_225_; lean_object* v_size_226_; lean_object* v___x_227_; 
v_index_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_index_225_);
lean_dec_ref_known(v___x_224_, 3);
v_size_226_ = lean_ctor_get(v_acc_197_, 0);
lean_inc(v_size_226_);
v___x_227_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_197_, v_size_226_, v_index_225_, v_val_216_, v_val_217_);
lean_dec(v_index_225_);
v___y_200_ = v___x_227_;
goto v___jp_199_;
}
case 1:
{
lean_object* v_index_228_; 
v_index_228_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_index_228_);
lean_dec_ref_known(v___x_224_, 1);
v_i_219_ = v_index_228_;
goto v___jp_218_;
}
default: 
{
lean_object* v___x_229_; lean_object* v___x_230_; 
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_197_, v___x_229_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_index_231_; 
v_index_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_index_231_);
lean_dec_ref_known(v___x_230_, 1);
v_i_219_ = v_index_231_;
goto v___jp_218_;
}
else
{
lean_dec(v_val_217_);
lean_dec(v_val_216_);
v___y_200_ = v_acc_197_;
goto v___jp_199_;
}
}
}
v___jp_218_:
{
lean_object* v_size_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_size_220_ = lean_ctor_get(v_acc_197_, 0);
v___x_221_ = lean_unsigned_to_nat(1u);
v___x_222_ = lean_nat_add(v_size_220_, v___x_221_);
v___x_223_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_197_, v___x_222_, v_i_219_, v_val_216_, v_val_217_);
lean_dec(v_i_219_);
v___y_200_ = v___x_223_;
goto v___jp_199_;
}
}
}
}
v___jp_199_:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = lean_unsigned_to_nat(1u);
v___x_202_ = lean_nat_add(v_i_198_, v___x_201_);
lean_dec(v_i_198_);
v_acc_197_ = v___y_200_;
v_i_198_ = v___x_202_;
goto _start;
}
v___jp_204_:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(1u);
v___x_206_ = lean_nat_add(v_i_198_, v___x_205_);
lean_dec(v_i_198_);
v_i_198_ = v___x_206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_232_, lean_object* v_acc_233_, lean_object* v_i_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v_b_232_, v_acc_233_, v_i_234_);
lean_dec_ref(v_b_232_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(lean_object* v_init_236_, lean_object* v_b_237_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v_b_237_, v_init_236_, v___x_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg___boxed(lean_object* v_init_240_, lean_object* v_b_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_init_240_, v_b_241_);
lean_dec_ref(v_b_241_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(lean_object* v_m_243_){
_start:
{
lean_object* v_keyArray_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v_cellCount_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_target_251_; lean_object* v___x_252_; 
v_keyArray_244_ = lean_ctor_get(v_m_243_, 1);
v___x_245_ = lean_array_get_size(v_keyArray_244_);
v___x_246_ = lean_unsigned_to_nat(2u);
v_cellCount_247_ = lean_nat_mul(v___x_245_, v___x_246_);
v___x_248_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_247_);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_247_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_247_);
v_target_251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_251_, 0, v___x_248_);
lean_ctor_set(v_target_251_, 1, v___x_249_);
lean_ctor_set(v_target_251_, 2, v___x_250_);
v___x_252_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_target_251_, v_m_243_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg___boxed(lean_object* v_m_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_m_253_);
lean_dec_ref(v_m_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10___redArg(lean_object* v_b_255_, lean_object* v_acc_256_, lean_object* v_i_257_){
_start:
{
lean_object* v___y_259_; lean_object* v_keyArray_267_; lean_object* v_valueArray_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v_keyArray_267_ = lean_ctor_get(v_b_255_, 1);
v_valueArray_268_ = lean_ctor_get(v_b_255_, 2);
v___x_269_ = lean_array_get_size(v_keyArray_267_);
v___x_270_ = lean_nat_dec_lt(v_i_257_, v___x_269_);
if (v___x_270_ == 0)
{
lean_dec(v_i_257_);
return v_acc_256_;
}
else
{
lean_object* v___x_271_; uint8_t v_isSome_272_; 
v___x_271_ = lean_array_fget_borrowed(v_keyArray_267_, v_i_257_);
v_isSome_272_ = lean_noption_is_some(v___x_271_);
if (v_isSome_272_ == 0)
{
goto v___jp_263_;
}
else
{
lean_object* v___x_273_; uint8_t v_isSome_274_; 
v___x_273_ = lean_array_fget_borrowed(v_valueArray_268_, v_i_257_);
v_isSome_274_ = lean_noption_is_some(v___x_273_);
if (v_isSome_274_ == 0)
{
goto v___jp_263_;
}
else
{
lean_object* v_val_275_; lean_object* v_val_276_; lean_object* v_i_278_; lean_object* v___x_283_; 
lean_inc(v___x_271_);
v_val_275_ = lean_noption_get(v___x_271_);
lean_inc(v___x_273_);
v_val_276_ = lean_noption_get(v___x_273_);
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg(v_acc_256_, v_val_275_);
switch(lean_obj_tag(v___x_283_))
{
case 0:
{
lean_object* v_index_284_; lean_object* v_size_285_; lean_object* v___x_286_; 
v_index_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_index_284_);
lean_dec_ref_known(v___x_283_, 3);
v_size_285_ = lean_ctor_get(v_acc_256_, 0);
lean_inc(v_size_285_);
v___x_286_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_256_, v_size_285_, v_index_284_, v_val_275_, v_val_276_);
lean_dec(v_index_284_);
v___y_259_ = v___x_286_;
goto v___jp_258_;
}
case 1:
{
lean_object* v_index_287_; 
v_index_287_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_index_287_);
lean_dec_ref_known(v___x_283_, 1);
v_i_278_ = v_index_287_;
goto v___jp_277_;
}
default: 
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_256_, v___x_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_index_290_; 
v_index_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_index_290_);
lean_dec_ref_known(v___x_289_, 1);
v_i_278_ = v_index_290_;
goto v___jp_277_;
}
else
{
lean_dec(v_val_276_);
lean_dec(v_val_275_);
v___y_259_ = v_acc_256_;
goto v___jp_258_;
}
}
}
v___jp_277_:
{
lean_object* v_size_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v_size_279_ = lean_ctor_get(v_acc_256_, 0);
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_size_279_, v___x_280_);
v___x_282_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_256_, v___x_281_, v_i_278_, v_val_275_, v_val_276_);
lean_dec(v_i_278_);
v___y_259_ = v___x_282_;
goto v___jp_258_;
}
}
}
}
v___jp_258_:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_nat_add(v_i_257_, v___x_260_);
lean_dec(v_i_257_);
v_acc_256_ = v___y_259_;
v_i_257_ = v___x_261_;
goto _start;
}
v___jp_263_:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_i_257_, v___x_264_);
lean_dec(v_i_257_);
v_i_257_ = v___x_265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10___redArg___boxed(lean_object* v_b_291_, lean_object* v_acc_292_, lean_object* v_i_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10___redArg(v_b_291_, v_acc_292_, v_i_293_);
lean_dec_ref(v_b_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8___redArg(lean_object* v_init_295_, lean_object* v_b_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10___redArg(v_b_296_, v_init_295_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8___redArg___boxed(lean_object* v_init_299_, lean_object* v_b_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8___redArg(v_init_299_, v_b_300_);
lean_dec_ref(v_b_300_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___redArg(lean_object* v_m_302_){
_start:
{
lean_object* v_keyArray_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_cellCount_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_target_310_; lean_object* v___x_311_; 
v_keyArray_303_ = lean_ctor_get(v_m_302_, 1);
v___x_304_ = lean_array_get_size(v_keyArray_303_);
v___x_305_ = lean_unsigned_to_nat(2u);
v_cellCount_306_ = lean_nat_mul(v___x_304_, v___x_305_);
v___x_307_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_306_);
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_306_);
v___x_309_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_306_);
v_target_310_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_310_, 0, v___x_307_);
lean_ctor_set(v_target_310_, 1, v___x_308_);
lean_ctor_set(v_target_310_, 2, v___x_309_);
v___x_311_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8___redArg(v_target_310_, v_m_302_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___redArg___boxed(lean_object* v_m_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___redArg(v_m_312_);
lean_dec_ref(v_m_312_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_CollectLooseBVars_main(lean_object* v_e_314_, lean_object* v_offset_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___y_318_; lean_object* v___y_319_; lean_object* v___y_320_; lean_object* v___y_324_; lean_object* v___y_325_; lean_object* v___y_326_; lean_object* v___y_327_; lean_object* v_i_328_; lean_object* v___y_334_; lean_object* v___y_335_; lean_object* v___y_336_; lean_object* v___y_337_; lean_object* v___y_348_; lean_object* v___y_349_; lean_object* v___y_350_; lean_object* v___y_351_; lean_object* v_i_352_; lean_object* v___y_358_; lean_object* v___y_359_; lean_object* v___y_360_; lean_object* v___y_361_; lean_object* v_t_371_; lean_object* v_b_372_; lean_object* v___y_373_; lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = l_Lean_Expr_looseBVarRange(v_e_314_);
v___x_380_ = lean_nat_dec_lt(v_offset_315_, v___x_379_);
lean_dec(v___x_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_381_; lean_object* v___x_382_; 
lean_dec(v_offset_315_);
lean_dec_ref(v_e_314_);
v___x_381_ = lean_box(0);
v___x_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v_a_316_);
return v___x_382_;
}
else
{
lean_object* v_visited_383_; lean_object* v_bvars_384_; lean_object* v___y_386_; lean_object* v___x_443_; uint8_t v___x_444_; 
v_visited_383_ = lean_ctor_get(v_a_316_, 0);
v_bvars_384_ = lean_ctor_get(v_a_316_, 1);
lean_inc_ref(v_e_314_);
lean_inc(v_offset_315_);
v___x_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_443_, 0, v_offset_315_);
lean_ctor_set(v___x_443_, 1, v_e_314_);
v___x_444_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_visited_383_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___y_447_; lean_object* v_i_448_; lean_object* v___y_454_; lean_object* v___y_464_; lean_object* v_i_465_; lean_object* v___x_480_; 
lean_inc_ref(v_bvars_384_);
lean_inc_ref(v_visited_383_);
lean_dec_ref(v_a_316_);
v___x_445_ = lean_box(0);
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg(v_visited_383_, v___x_443_);
switch(lean_obj_tag(v___x_480_))
{
case 0:
{
lean_dec_ref_known(v___x_480_, 3);
lean_dec_ref_known(v___x_443_, 2);
v___y_386_ = v_visited_383_;
goto v___jp_385_;
}
case 1:
{
lean_object* v_index_481_; lean_object* v_size_482_; lean_object* v_keyArray_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_index_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_index_481_);
lean_dec_ref_known(v___x_480_, 1);
v_size_482_ = lean_ctor_get(v_visited_383_, 0);
v_keyArray_483_ = lean_ctor_get(v_visited_383_, 1);
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_size_482_, v___x_484_);
v___x_486_ = lean_array_get_size(v_keyArray_483_);
v___x_487_ = lean_nat_dec_lt(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_dec(v___x_485_);
lean_dec(v_index_481_);
goto v___jp_470_;
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_488_ = lean_unsigned_to_nat(4u);
v___x_489_ = lean_nat_mul(v___x_485_, v___x_488_);
v___x_490_ = lean_unsigned_to_nat(3u);
v___x_491_ = lean_nat_mul(v___x_486_, v___x_490_);
v___x_492_ = lean_nat_dec_le(v___x_489_, v___x_491_);
lean_dec(v___x_491_);
lean_dec(v___x_489_);
if (v___x_492_ == 0)
{
lean_dec(v___x_485_);
lean_dec(v_index_481_);
goto v___jp_470_;
}
else
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DHashMap_Raw_setEntry___redArg(v_visited_383_, v___x_485_, v_index_481_, v___x_443_, v___x_445_);
lean_dec(v_index_481_);
v___y_386_ = v___x_493_;
goto v___jp_385_;
}
}
}
default: 
{
lean_object* v_size_494_; lean_object* v_keyArray_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_size_494_ = lean_ctor_get(v_visited_383_, 0);
v_keyArray_495_ = lean_ctor_get(v_visited_383_, 1);
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_add(v_size_494_, v___x_496_);
v___x_498_ = lean_array_get_size(v_keyArray_495_);
v___x_499_ = lean_nat_dec_lt(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_object* v___x_500_; 
lean_dec(v___x_497_);
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___redArg(v_visited_383_);
lean_dec_ref(v_visited_383_);
v___y_454_ = v___x_500_;
goto v___jp_453_;
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_501_ = lean_unsigned_to_nat(4u);
v___x_502_ = lean_nat_mul(v___x_497_, v___x_501_);
lean_dec(v___x_497_);
v___x_503_ = lean_unsigned_to_nat(3u);
v___x_504_ = lean_nat_mul(v___x_498_, v___x_503_);
v___x_505_ = lean_nat_dec_le(v___x_502_, v___x_504_);
lean_dec(v___x_504_);
lean_dec(v___x_502_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
v___x_506_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___redArg(v_visited_383_);
lean_dec_ref(v_visited_383_);
v___y_454_ = v___x_506_;
goto v___jp_453_;
}
else
{
v___y_454_ = v_visited_383_;
goto v___jp_453_;
}
}
}
}
v___jp_446_:
{
lean_object* v_size_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_size_449_ = lean_ctor_get(v___y_447_, 0);
v___x_450_ = lean_unsigned_to_nat(1u);
v___x_451_ = lean_nat_add(v_size_449_, v___x_450_);
v___x_452_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_447_, v___x_451_, v_i_448_, v___x_443_, v___x_445_);
lean_dec(v_i_448_);
v___y_386_ = v___x_452_;
goto v___jp_385_;
}
v___jp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg(v___y_454_, v___x_443_);
switch(lean_obj_tag(v___x_455_))
{
case 0:
{
lean_object* v_index_456_; lean_object* v_size_457_; lean_object* v___x_458_; 
v_index_456_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_index_456_);
lean_dec_ref_known(v___x_455_, 3);
v_size_457_ = lean_ctor_get(v___y_454_, 0);
lean_inc(v_size_457_);
v___x_458_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_454_, v_size_457_, v_index_456_, v___x_443_, v___x_445_);
lean_dec(v_index_456_);
v___y_386_ = v___x_458_;
goto v___jp_385_;
}
case 1:
{
lean_object* v_index_459_; 
v_index_459_ = lean_ctor_get(v___x_455_, 0);
lean_inc(v_index_459_);
lean_dec_ref_known(v___x_455_, 1);
v___y_447_ = v___y_454_;
v_i_448_ = v_index_459_;
goto v___jp_446_;
}
default: 
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = lean_unsigned_to_nat(0u);
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_454_, v___x_460_);
if (lean_obj_tag(v___x_461_) == 0)
{
lean_object* v_index_462_; 
v_index_462_ = lean_ctor_get(v___x_461_, 0);
lean_inc(v_index_462_);
lean_dec_ref_known(v___x_461_, 1);
v___y_447_ = v___y_454_;
v_i_448_ = v_index_462_;
goto v___jp_446_;
}
else
{
lean_dec_ref_known(v___x_443_, 2);
v___y_386_ = v___y_454_;
goto v___jp_385_;
}
}
}
}
v___jp_463_:
{
lean_object* v_size_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v_size_466_ = lean_ctor_get(v___y_464_, 0);
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_add(v_size_466_, v___x_467_);
v___x_469_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_464_, v___x_468_, v_i_465_, v___x_443_, v___x_445_);
lean_dec(v_i_465_);
v___y_386_ = v___x_469_;
goto v___jp_385_;
}
v___jp_470_:
{
lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___redArg(v_visited_383_);
lean_dec_ref(v_visited_383_);
v___x_472_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg(v___x_471_, v___x_443_);
switch(lean_obj_tag(v___x_472_))
{
case 0:
{
lean_object* v_index_473_; lean_object* v_size_474_; lean_object* v___x_475_; 
v_index_473_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_index_473_);
lean_dec_ref_known(v___x_472_, 3);
v_size_474_ = lean_ctor_get(v___x_471_, 0);
lean_inc(v_size_474_);
v___x_475_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_471_, v_size_474_, v_index_473_, v___x_443_, v___x_445_);
lean_dec(v_index_473_);
v___y_386_ = v___x_475_;
goto v___jp_385_;
}
case 1:
{
lean_object* v_index_476_; 
v_index_476_ = lean_ctor_get(v___x_472_, 0);
lean_inc(v_index_476_);
lean_dec_ref_known(v___x_472_, 1);
v___y_464_ = v___x_471_;
v_i_465_ = v_index_476_;
goto v___jp_463_;
}
default: 
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_471_, v___x_477_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_index_479_; 
v_index_479_ = lean_ctor_get(v___x_478_, 0);
lean_inc(v_index_479_);
lean_dec_ref_known(v___x_478_, 1);
v___y_464_ = v___x_471_;
v_i_465_ = v_index_479_;
goto v___jp_463_;
}
else
{
lean_dec_ref_known(v___x_443_, 2);
v___y_386_ = v___x_471_;
goto v___jp_385_;
}
}
}
}
}
else
{
lean_object* v___x_507_; lean_object* v___x_508_; 
lean_dec_ref_known(v___x_443_, 2);
lean_dec(v_offset_315_);
lean_dec_ref(v_e_314_);
v___x_507_ = lean_box(0);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_507_);
lean_ctor_set(v___x_508_, 1, v_a_316_);
return v___x_508_;
}
v___jp_385_:
{
lean_object* v___x_387_; 
lean_inc_ref(v_bvars_384_);
lean_inc_ref(v___y_386_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v___y_386_);
lean_ctor_set(v___x_387_, 1, v_bvars_384_);
switch(lean_obj_tag(v_e_314_))
{
case 0:
{
lean_object* v_deBruijnIndex_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec_ref_known(v___x_387_, 2);
v_deBruijnIndex_388_ = lean_ctor_get(v_e_314_, 0);
lean_inc(v_deBruijnIndex_388_);
lean_dec_ref_known(v_e_314_, 1);
v___x_389_ = lean_box(0);
v___x_390_ = lean_nat_sub(v_deBruijnIndex_388_, v_offset_315_);
lean_dec(v_offset_315_);
lean_dec(v_deBruijnIndex_388_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_bvars_384_, v___x_390_);
switch(lean_obj_tag(v___x_391_))
{
case 0:
{
lean_dec_ref_known(v___x_391_, 3);
lean_dec(v___x_390_);
v___y_318_ = v___y_386_;
v___y_319_ = v___x_389_;
v___y_320_ = v_bvars_384_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_index_392_; lean_object* v_size_393_; lean_object* v_keyArray_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_index_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_index_392_);
lean_dec_ref_known(v___x_391_, 1);
v_size_393_ = lean_ctor_get(v_bvars_384_, 0);
v_keyArray_394_ = lean_ctor_get(v_bvars_384_, 1);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_nat_add(v_size_393_, v___x_395_);
v___x_397_ = lean_array_get_size(v_keyArray_394_);
v___x_398_ = lean_nat_dec_lt(v___x_396_, v___x_397_);
if (v___x_398_ == 0)
{
lean_dec(v___x_396_);
lean_dec(v_index_392_);
v___y_334_ = v___y_386_;
v___y_335_ = v___x_390_;
v___y_336_ = v___x_389_;
v___y_337_ = v_bvars_384_;
goto v___jp_333_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_399_ = lean_unsigned_to_nat(4u);
v___x_400_ = lean_nat_mul(v___x_396_, v___x_399_);
v___x_401_ = lean_unsigned_to_nat(3u);
v___x_402_ = lean_nat_mul(v___x_397_, v___x_401_);
v___x_403_ = lean_nat_dec_le(v___x_400_, v___x_402_);
lean_dec(v___x_402_);
lean_dec(v___x_400_);
if (v___x_403_ == 0)
{
lean_dec(v___x_396_);
lean_dec(v_index_392_);
v___y_334_ = v___y_386_;
v___y_335_ = v___x_390_;
v___y_336_ = v___x_389_;
v___y_337_ = v_bvars_384_;
goto v___jp_333_;
}
else
{
lean_object* v___x_404_; 
v___x_404_ = l_Std_DHashMap_Raw_setEntry___redArg(v_bvars_384_, v___x_396_, v_index_392_, v___x_390_, v___x_389_);
lean_dec(v_index_392_);
v___y_318_ = v___y_386_;
v___y_319_ = v___x_389_;
v___y_320_ = v___x_404_;
goto v___jp_317_;
}
}
}
default: 
{
lean_object* v_size_405_; lean_object* v_keyArray_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_size_405_ = lean_ctor_get(v_bvars_384_, 0);
v_keyArray_406_ = lean_ctor_get(v_bvars_384_, 1);
v___x_407_ = lean_unsigned_to_nat(1u);
v___x_408_ = lean_nat_add(v_size_405_, v___x_407_);
v___x_409_ = lean_array_get_size(v_keyArray_406_);
v___x_410_ = lean_nat_dec_lt(v___x_408_, v___x_409_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; 
lean_dec(v___x_408_);
v___x_411_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_bvars_384_);
lean_dec_ref(v_bvars_384_);
v___y_358_ = v___y_386_;
v___y_359_ = v___x_390_;
v___y_360_ = v___x_389_;
v___y_361_ = v___x_411_;
goto v___jp_357_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v___x_412_ = lean_unsigned_to_nat(4u);
v___x_413_ = lean_nat_mul(v___x_408_, v___x_412_);
lean_dec(v___x_408_);
v___x_414_ = lean_unsigned_to_nat(3u);
v___x_415_ = lean_nat_mul(v___x_409_, v___x_414_);
v___x_416_ = lean_nat_dec_le(v___x_413_, v___x_415_);
lean_dec(v___x_415_);
lean_dec(v___x_413_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_bvars_384_);
lean_dec_ref(v_bvars_384_);
v___y_358_ = v___y_386_;
v___y_359_ = v___x_390_;
v___y_360_ = v___x_389_;
v___y_361_ = v___x_417_;
goto v___jp_357_;
}
else
{
v___y_358_ = v___y_386_;
v___y_359_ = v___x_390_;
v___y_360_ = v___x_389_;
v___y_361_ = v_bvars_384_;
goto v___jp_357_;
}
}
}
}
}
case 5:
{
lean_object* v_fn_418_; lean_object* v_arg_419_; lean_object* v___x_420_; lean_object* v_snd_421_; 
lean_dec_ref(v___y_386_);
lean_dec_ref(v_bvars_384_);
v_fn_418_ = lean_ctor_get(v_e_314_, 0);
lean_inc_ref(v_fn_418_);
v_arg_419_ = lean_ctor_get(v_e_314_, 1);
lean_inc_ref(v_arg_419_);
lean_dec_ref_known(v_e_314_, 2);
lean_inc(v_offset_315_);
v___x_420_ = l_Lean_Expr_CollectLooseBVars_main(v_fn_418_, v_offset_315_, v___x_387_);
v_snd_421_ = lean_ctor_get(v___x_420_, 1);
lean_inc(v_snd_421_);
lean_dec_ref(v___x_420_);
v_e_314_ = v_arg_419_;
v_a_316_ = v_snd_421_;
goto _start;
}
case 6:
{
lean_object* v_binderType_423_; lean_object* v_body_424_; 
lean_dec_ref(v___y_386_);
lean_dec_ref(v_bvars_384_);
v_binderType_423_ = lean_ctor_get(v_e_314_, 1);
lean_inc_ref(v_binderType_423_);
v_body_424_ = lean_ctor_get(v_e_314_, 2);
lean_inc_ref(v_body_424_);
lean_dec_ref_known(v_e_314_, 3);
v_t_371_ = v_binderType_423_;
v_b_372_ = v_body_424_;
v___y_373_ = v___x_387_;
goto v___jp_370_;
}
case 7:
{
lean_object* v_binderType_425_; lean_object* v_body_426_; 
lean_dec_ref(v___y_386_);
lean_dec_ref(v_bvars_384_);
v_binderType_425_ = lean_ctor_get(v_e_314_, 1);
lean_inc_ref(v_binderType_425_);
v_body_426_ = lean_ctor_get(v_e_314_, 2);
lean_inc_ref(v_body_426_);
lean_dec_ref_known(v_e_314_, 3);
v_t_371_ = v_binderType_425_;
v_b_372_ = v_body_426_;
v___y_373_ = v___x_387_;
goto v___jp_370_;
}
case 8:
{
lean_object* v_type_427_; lean_object* v_value_428_; lean_object* v_body_429_; lean_object* v___x_430_; lean_object* v_snd_431_; lean_object* v___x_432_; lean_object* v_snd_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
lean_dec_ref(v___y_386_);
lean_dec_ref(v_bvars_384_);
v_type_427_ = lean_ctor_get(v_e_314_, 1);
lean_inc_ref(v_type_427_);
v_value_428_ = lean_ctor_get(v_e_314_, 2);
lean_inc_ref(v_value_428_);
v_body_429_ = lean_ctor_get(v_e_314_, 3);
lean_inc_ref(v_body_429_);
lean_dec_ref_known(v_e_314_, 4);
lean_inc_n(v_offset_315_, 2);
v___x_430_ = l_Lean_Expr_CollectLooseBVars_main(v_type_427_, v_offset_315_, v___x_387_);
v_snd_431_ = lean_ctor_get(v___x_430_, 1);
lean_inc(v_snd_431_);
lean_dec_ref(v___x_430_);
v___x_432_ = l_Lean_Expr_CollectLooseBVars_main(v_value_428_, v_offset_315_, v_snd_431_);
v_snd_433_ = lean_ctor_get(v___x_432_, 1);
lean_inc(v_snd_433_);
lean_dec_ref(v___x_432_);
v___x_434_ = lean_unsigned_to_nat(1u);
v___x_435_ = lean_nat_add(v_offset_315_, v___x_434_);
lean_dec(v_offset_315_);
v_e_314_ = v_body_429_;
v_offset_315_ = v___x_435_;
v_a_316_ = v_snd_433_;
goto _start;
}
case 10:
{
lean_object* v_expr_437_; 
lean_dec_ref(v___y_386_);
lean_dec_ref(v_bvars_384_);
v_expr_437_ = lean_ctor_get(v_e_314_, 1);
lean_inc_ref(v_expr_437_);
lean_dec_ref_known(v_e_314_, 2);
v_e_314_ = v_expr_437_;
v_a_316_ = v___x_387_;
goto _start;
}
case 11:
{
lean_object* v_struct_439_; 
lean_dec_ref(v___y_386_);
lean_dec_ref(v_bvars_384_);
v_struct_439_ = lean_ctor_get(v_e_314_, 2);
lean_inc_ref(v_struct_439_);
lean_dec_ref_known(v_e_314_, 3);
v_e_314_ = v_struct_439_;
v_a_316_ = v___x_387_;
goto _start;
}
default: 
{
lean_object* v___x_441_; lean_object* v___x_442_; 
lean_dec_ref(v___y_386_);
lean_dec_ref(v_bvars_384_);
lean_dec(v_offset_315_);
lean_dec_ref(v_e_314_);
v___x_441_ = lean_box(0);
v___x_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_442_, 0, v___x_441_);
lean_ctor_set(v___x_442_, 1, v___x_387_);
return v___x_442_;
}
}
}
}
v___jp_317_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___y_318_);
lean_ctor_set(v___x_321_, 1, v___y_320_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___y_319_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
return v___x_322_;
}
v___jp_323_:
{
lean_object* v_size_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v_size_329_ = lean_ctor_get(v___y_325_, 0);
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_add(v_size_329_, v___x_330_);
v___x_332_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_325_, v___x_331_, v_i_328_, v___y_326_, v___y_327_);
lean_dec(v_i_328_);
v___y_318_ = v___y_324_;
v___y_319_ = v___y_327_;
v___y_320_ = v___x_332_;
goto v___jp_317_;
}
v___jp_333_:
{
lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_338_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v___y_337_);
lean_dec_ref(v___y_337_);
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v___x_338_, v___y_335_);
switch(lean_obj_tag(v___x_339_))
{
case 0:
{
lean_object* v_index_340_; lean_object* v_size_341_; lean_object* v___x_342_; 
v_index_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_index_340_);
lean_dec_ref_known(v___x_339_, 3);
v_size_341_ = lean_ctor_get(v___x_338_, 0);
lean_inc(v_size_341_);
v___x_342_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_338_, v_size_341_, v_index_340_, v___y_335_, v___y_336_);
lean_dec(v_index_340_);
v___y_318_ = v___y_334_;
v___y_319_ = v___y_336_;
v___y_320_ = v___x_342_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_index_343_; 
v_index_343_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_index_343_);
lean_dec_ref_known(v___x_339_, 1);
v___y_324_ = v___y_334_;
v___y_325_ = v___x_338_;
v___y_326_ = v___y_335_;
v___y_327_ = v___y_336_;
v_i_328_ = v_index_343_;
goto v___jp_323_;
}
default: 
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_338_, v___x_344_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_index_346_; 
v_index_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_index_346_);
lean_dec_ref_known(v___x_345_, 1);
v___y_324_ = v___y_334_;
v___y_325_ = v___x_338_;
v___y_326_ = v___y_335_;
v___y_327_ = v___y_336_;
v_i_328_ = v_index_346_;
goto v___jp_323_;
}
else
{
lean_dec(v___y_335_);
v___y_318_ = v___y_334_;
v___y_319_ = v___y_336_;
v___y_320_ = v___x_338_;
goto v___jp_317_;
}
}
}
}
v___jp_347_:
{
lean_object* v_size_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_size_353_ = lean_ctor_get(v___y_349_, 0);
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_add(v_size_353_, v___x_354_);
v___x_356_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_349_, v___x_355_, v_i_352_, v___y_350_, v___y_351_);
lean_dec(v_i_352_);
v___y_318_ = v___y_348_;
v___y_319_ = v___y_351_;
v___y_320_ = v___x_356_;
goto v___jp_317_;
}
v___jp_357_:
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v___y_361_, v___y_359_);
switch(lean_obj_tag(v___x_362_))
{
case 0:
{
lean_object* v_index_363_; lean_object* v_size_364_; lean_object* v___x_365_; 
v_index_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_index_363_);
lean_dec_ref_known(v___x_362_, 3);
v_size_364_ = lean_ctor_get(v___y_361_, 0);
lean_inc(v_size_364_);
v___x_365_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_361_, v_size_364_, v_index_363_, v___y_359_, v___y_360_);
lean_dec(v_index_363_);
v___y_318_ = v___y_358_;
v___y_319_ = v___y_360_;
v___y_320_ = v___x_365_;
goto v___jp_317_;
}
case 1:
{
lean_object* v_index_366_; 
v_index_366_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_index_366_);
lean_dec_ref_known(v___x_362_, 1);
v___y_348_ = v___y_358_;
v___y_349_ = v___y_361_;
v___y_350_ = v___y_359_;
v___y_351_ = v___y_360_;
v_i_352_ = v_index_366_;
goto v___jp_347_;
}
default: 
{
lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_361_, v___x_367_);
if (lean_obj_tag(v___x_368_) == 0)
{
lean_object* v_index_369_; 
v_index_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_index_369_);
lean_dec_ref_known(v___x_368_, 1);
v___y_348_ = v___y_358_;
v___y_349_ = v___y_361_;
v___y_350_ = v___y_359_;
v___y_351_ = v___y_360_;
v_i_352_ = v_index_369_;
goto v___jp_347_;
}
else
{
lean_dec(v___y_359_);
v___y_318_ = v___y_358_;
v___y_319_ = v___y_360_;
v___y_320_ = v___y_361_;
goto v___jp_317_;
}
}
}
}
v___jp_370_:
{
lean_object* v___x_374_; lean_object* v_snd_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_inc(v_offset_315_);
v___x_374_ = l_Lean_Expr_CollectLooseBVars_main(v_t_371_, v_offset_315_, v___y_373_);
v_snd_375_ = lean_ctor_get(v___x_374_, 1);
lean_inc(v_snd_375_);
lean_dec_ref(v___x_374_);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_offset_315_, v___x_376_);
lean_dec(v_offset_315_);
v_e_314_ = v_b_372_;
v_offset_315_ = v___x_377_;
v_a_316_ = v_snd_375_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0(lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_query_511_){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___redArg(v_m_510_, v_query_511_);
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0___boxed(lean_object* v_00_u03b2_513_, lean_object* v_m_514_, lean_object* v_query_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0(v_00_u03b2_513_, v_m_514_, v_query_515_);
lean_dec(v_query_515_);
lean_dec_ref(v_m_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1(lean_object* v_00_u03b2_517_, lean_object* v_m_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___redArg(v_m_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1___boxed(lean_object* v_00_u03b2_520_, lean_object* v_m_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1(v_00_u03b2_520_, v_m_521_);
lean_dec_ref(v_m_521_);
return v_res_522_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2(lean_object* v_00_u03b2_523_, lean_object* v_m_524_, lean_object* v_a_525_){
_start:
{
uint8_t v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2___redArg(v_m_524_, v_a_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2___boxed(lean_object* v_00_u03b2_527_, lean_object* v_m_528_, lean_object* v_a_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2(v_00_u03b2_527_, v_m_528_, v_a_529_);
lean_dec_ref(v_a_529_);
lean_dec_ref(v_m_528_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3(lean_object* v_00_u03b2_532_, lean_object* v_m_533_, lean_object* v_query_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___redArg(v_m_533_, v_query_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3___boxed(lean_object* v_00_u03b2_536_, lean_object* v_m_537_, lean_object* v_query_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3(v_00_u03b2_536_, v_m_537_, v_query_538_);
lean_dec_ref(v_query_538_);
lean_dec_ref(v_m_537_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4(lean_object* v_00_u03b2_540_, lean_object* v_m_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___redArg(v_m_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4___boxed(lean_object* v_00_u03b2_543_, lean_object* v_m_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4(v_00_u03b2_543_, v_m_544_);
lean_dec_ref(v_m_544_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(lean_object* v_00_u03b2_546_, lean_object* v_m_547_, lean_object* v_query_548_, lean_object* v_x_549_, lean_object* v_x_550_, lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___redArg(v_m_547_, v_query_548_, v_x_549_, v_x_550_, v_x_551_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0___boxed(lean_object* v_00_u03b2_554_, lean_object* v_m_555_, lean_object* v_query_556_, lean_object* v_x_557_, lean_object* v_x_558_, lean_object* v_x_559_, lean_object* v_x_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__0_spec__0(v_00_u03b2_554_, v_m_555_, v_query_556_, v_x_557_, v_x_558_, v_x_559_, v_x_560_);
lean_dec(v_query_556_);
lean_dec_ref(v_m_555_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2(lean_object* v_00_u03b2_562_, lean_object* v_init_563_, lean_object* v_b_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___redArg(v_init_563_, v_b_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2___boxed(lean_object* v_00_u03b2_566_, lean_object* v_init_567_, lean_object* v_b_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2(v_00_u03b2_566_, v_init_567_, v_b_568_);
lean_dec_ref(v_b_568_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(lean_object* v_00_u03b2_570_, lean_object* v_m_571_, lean_object* v_query_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___redArg(v_m_571_, v_query_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4___boxed(lean_object* v_00_u03b2_574_, lean_object* v_m_575_, lean_object* v_query_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Expr_CollectLooseBVars_main_spec__2_spec__4(v_00_u03b2_574_, v_m_575_, v_query_576_);
lean_dec_ref(v_query_576_);
lean_dec_ref(v_m_575_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6(lean_object* v_00_u03b2_578_, lean_object* v_m_579_, lean_object* v_query_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6___redArg(v_m_579_, v_query_580_, v_x_581_, v_x_582_, v_x_583_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6___boxed(lean_object* v_00_u03b2_586_, lean_object* v_m_587_, lean_object* v_query_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Expr_CollectLooseBVars_main_spec__3_spec__6(v_00_u03b2_586_, v_m_587_, v_query_588_, v_x_589_, v_x_590_, v_x_591_, v_x_592_);
lean_dec_ref(v_query_588_);
lean_dec_ref(v_m_587_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8(lean_object* v_00_u03b2_594_, lean_object* v_init_595_, lean_object* v_b_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8___redArg(v_init_595_, v_b_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8___boxed(lean_object* v_00_u03b2_598_, lean_object* v_init_599_, lean_object* v_b_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8(v_00_u03b2_598_, v_init_599_, v_b_600_);
lean_dec_ref(v_b_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_602_, lean_object* v_b_603_, lean_object* v_acc_604_, lean_object* v_i_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___redArg(v_b_603_, v_acc_604_, v_i_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_607_, lean_object* v_b_608_, lean_object* v_acc_609_, lean_object* v_i_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__1_spec__2_spec__3(v_00_u03b2_607_, v_b_608_, v_acc_609_, v_i_610_);
lean_dec_ref(v_b_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10(lean_object* v_00_u03b2_612_, lean_object* v_b_613_, lean_object* v_acc_614_, lean_object* v_i_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10___redArg(v_b_613_, v_acc_614_, v_i_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10___boxed(lean_object* v_00_u03b2_617_, lean_object* v_b_618_, lean_object* v_acc_619_, lean_object* v_i_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Expr_CollectLooseBVars_main_spec__4_spec__8_spec__10(v_00_u03b2_617_, v_b_618_, v_acc_619_, v_i_620_);
lean_dec_ref(v_b_618_);
return v_res_621_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__0(void){
_start:
{
lean_object* v_cellCount_622_; lean_object* v___x_623_; 
v_cellCount_622_ = lean_unsigned_to_nat(16u);
v___x_623_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_622_);
return v___x_623_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__1(void){
_start:
{
lean_object* v_cellCount_624_; lean_object* v___x_625_; 
v_cellCount_624_ = lean_unsigned_to_nat(16u);
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__2(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__1, &l_Lean_Expr_collectLooseBVars___closed__1_once, _init_l_Lean_Expr_collectLooseBVars___closed__1);
v___x_627_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__0, &l_Lean_Expr_collectLooseBVars___closed__0_once, _init_l_Lean_Expr_collectLooseBVars___closed__0);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v___x_627_);
lean_ctor_set(v___x_629_, 2, v___x_626_);
return v___x_629_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__3(void){
_start:
{
lean_object* v_cellCount_630_; lean_object* v___x_631_; 
v_cellCount_630_ = lean_unsigned_to_nat(16u);
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_630_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__4(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_632_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__1, &l_Lean_Expr_collectLooseBVars___closed__1_once, _init_l_Lean_Expr_collectLooseBVars___closed__1);
v___x_633_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__3, &l_Lean_Expr_collectLooseBVars___closed__3_once, _init_l_Lean_Expr_collectLooseBVars___closed__3);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___x_633_);
lean_ctor_set(v___x_635_, 2, v___x_632_);
return v___x_635_;
}
}
static lean_object* _init_l_Lean_Expr_collectLooseBVars___closed__5(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_636_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__4, &l_Lean_Expr_collectLooseBVars___closed__4_once, _init_l_Lean_Expr_collectLooseBVars___closed__4);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_636_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_collectLooseBVars(lean_object* v_e_638_, lean_object* v_offset_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = l_Lean_Expr_hasLooseBVars(v_e_638_);
if (v___x_640_ == 0)
{
lean_object* v___x_641_; 
lean_dec(v_offset_639_);
lean_dec_ref(v_e_638_);
v___x_641_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__2, &l_Lean_Expr_collectLooseBVars___closed__2_once, _init_l_Lean_Expr_collectLooseBVars___closed__2);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v_snd_644_; lean_object* v_bvars_645_; 
v___x_642_ = lean_obj_once(&l_Lean_Expr_collectLooseBVars___closed__5, &l_Lean_Expr_collectLooseBVars___closed__5_once, _init_l_Lean_Expr_collectLooseBVars___closed__5);
v___x_643_ = l_Lean_Expr_CollectLooseBVars_main(v_e_638_, v_offset_639_, v___x_642_);
v_snd_644_ = lean_ctor_get(v___x_643_, 1);
lean_inc(v_snd_644_);
lean_dec_ref(v___x_643_);
v_bvars_645_ = lean_ctor_get(v_snd_644_, 1);
lean_inc_ref(v_bvars_645_);
lean_dec(v_snd_644_);
return v_bvars_645_;
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_CollectLooseBVars(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_CollectLooseBVars(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectLooseBVars(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectLooseBVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_CollectLooseBVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_CollectLooseBVars(builtin);
}
#ifdef __cplusplus
}
#endif
