// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.VarRename
// Imports: public import Init.Grind.Ordered.Linarith public import Lean.Meta.Tactic.Grind.VarRename
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
lean_object* l_Lean_Meta_Grind_collectVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_Linarith_Expr_renameVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_Linarith_Expr_renameVars___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_Expr_renameVars___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
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
lean_object* v_val_43_; uint8_t v___x_44_; 
lean_inc(v___x_19_);
v_val_43_ = lean_noption_get(v___x_19_);
v___x_44_ = lean_nat_dec_eq(v_val_43_, v_query_2_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; uint8_t v___x_47_; 
lean_dec(v_val_43_);
v___x_45_ = lean_array_get_size(v_keyArray_17_);
v___x_46_ = lean_nat_add(v_x_5_, v_one_30_);
lean_dec(v_x_5_);
v___x_47_ = lean_nat_dec_lt(v___x_46_, v___x_45_);
if (v___x_47_ == 0)
{
lean_dec(v___x_46_);
v_x_4_ = v_n_31_;
v_x_5_ = v_zero_6_;
goto _start;
}
else
{
v_x_4_ = v_n_31_;
v_x_5_ = v___x_46_;
goto _start;
}
}
else
{
lean_object* v_val_50_; lean_object* v___x_51_; 
lean_dec(v_n_31_);
lean_dec(v_x_3_);
lean_inc(v___x_41_);
v_val_50_ = lean_noption_get(v___x_41_);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v_x_5_);
lean_ctor_set(v___x_51_, 1, v_val_43_);
lean_ctor_set(v___x_51_, 2, v_val_50_);
return v___x_51_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(v_m_52_, v_query_53_, v_x_54_, v_x_55_, v_x_56_);
lean_dec(v_query_53_);
lean_dec_ref(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1___redArg(lean_object* v_m_58_, lean_object* v_query_59_){
_start:
{
lean_object* v_keyArray_60_; lean_object* v___x_61_; uint64_t v___x_62_; uint64_t v___x_63_; uint64_t v___x_64_; uint64_t v_fold_65_; uint64_t v___x_66_; uint64_t v___x_67_; uint64_t v___x_68_; size_t v___x_69_; size_t v___x_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_keyArray_60_ = lean_ctor_get(v_m_58_, 1);
v___x_61_ = lean_array_get_size(v_keyArray_60_);
v___x_62_ = lean_uint64_of_nat(v_query_59_);
v___x_63_ = 32ULL;
v___x_64_ = lean_uint64_shift_right(v___x_62_, v___x_63_);
v_fold_65_ = lean_uint64_xor(v___x_62_, v___x_64_);
v___x_66_ = 16ULL;
v___x_67_ = lean_uint64_shift_right(v_fold_65_, v___x_66_);
v___x_68_ = lean_uint64_xor(v_fold_65_, v___x_67_);
v___x_69_ = lean_uint64_to_usize(v___x_68_);
v___x_70_ = lean_usize_of_nat(v___x_61_);
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_sub(v___x_70_, v___x_71_);
v___x_73_ = lean_usize_land(v___x_69_, v___x_72_);
v___x_74_ = lean_usize_to_nat(v___x_73_);
v___x_75_ = lean_box(0);
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(v_m_58_, v_query_59_, v___x_75_, v___x_61_, v___x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_77_, lean_object* v_query_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1___redArg(v_m_77_, v_query_78_);
lean_dec(v_query_78_);
lean_dec_ref(v_m_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(lean_object* v_m_80_, lean_object* v_query_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1___redArg(v_m_80_, v_query_81_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v_index_83_; lean_object* v_key_84_; lean_object* v_value_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_92_; 
v_index_83_ = lean_ctor_get(v___x_82_, 0);
v_key_84_ = lean_ctor_get(v___x_82_, 1);
v_value_85_ = lean_ctor_get(v___x_82_, 2);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_92_ == 0)
{
v___x_87_ = v___x_82_;
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_value_85_);
lean_inc(v_key_84_);
lean_inc(v_index_83_);
lean_dec(v___x_82_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_92_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
lean_object* v___x_90_; 
if (v_isShared_88_ == 0)
{
v___x_90_ = v___x_87_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_index_83_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_key_84_);
lean_ctor_set(v_reuseFailAlloc_91_, 2, v_value_85_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
else
{
lean_object* v___x_93_; 
lean_dec(v___x_82_);
v___x_93_ = lean_box(1);
return v___x_93_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg___boxed(lean_object* v_m_94_, lean_object* v_query_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(v_m_94_, v_query_95_);
lean_dec(v_query_95_);
lean_dec_ref(v_m_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(lean_object* v_m_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(v_m_97_, v_a_98_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_value_100_; lean_object* v___x_101_; 
v_value_100_ = lean_ctor_get(v___x_99_, 2);
lean_inc(v_value_100_);
lean_dec_ref_known(v___x_99_, 3);
v___x_101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_101_, 0, v_value_100_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(0);
return v___x_102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg___boxed(lean_object* v_m_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(v_m_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_m_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_renameVars(lean_object* v_p_106_, lean_object* v_f_107_){
_start:
{
if (lean_obj_tag(v_p_106_) == 0)
{
return v_p_106_;
}
else
{
lean_object* v_k_108_; lean_object* v_v_109_; lean_object* v_p_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_123_; 
v_k_108_ = lean_ctor_get(v_p_106_, 0);
v_v_109_ = lean_ctor_get(v_p_106_, 1);
v_p_110_ = lean_ctor_get(v_p_106_, 2);
v_isSharedCheck_123_ = !lean_is_exclusive(v_p_106_);
if (v_isSharedCheck_123_ == 0)
{
v___x_112_ = v_p_106_;
v_isShared_113_ = v_isSharedCheck_123_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_p_110_);
lean_inc(v_v_109_);
lean_inc(v_k_108_);
lean_dec(v_p_106_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_123_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___y_115_; lean_object* v___x_120_; 
v___x_120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(v_f_107_, v_v_109_);
lean_dec(v_v_109_);
if (lean_obj_tag(v___x_120_) == 0)
{
lean_object* v___x_121_; 
v___x_121_ = lean_unsigned_to_nat(0u);
v___y_115_ = v___x_121_;
goto v___jp_114_;
}
else
{
lean_object* v_val_122_; 
v_val_122_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_val_122_);
lean_dec_ref_known(v___x_120_, 1);
v___y_115_ = v_val_122_;
goto v___jp_114_;
}
v___jp_114_:
{
lean_object* v___x_116_; lean_object* v___x_118_; 
v___x_116_ = l_Lean_Grind_Linarith_Poly_renameVars(v_p_110_, v_f_107_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 2, v___x_116_);
lean_ctor_set(v___x_112_, 1, v___y_115_);
v___x_118_ = v___x_112_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_k_108_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v___y_115_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v___x_116_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_renameVars___boxed(lean_object* v_p_124_, lean_object* v_f_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_Grind_Linarith_Poly_renameVars(v_p_124_, v_f_125_);
lean_dec_ref(v_f_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0(lean_object* v_00_u03b2_127_, lean_object* v_m_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_130_; 
v___x_130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(v_m_128_, v_a_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___boxed(lean_object* v_00_u03b2_131_, lean_object* v_m_132_, lean_object* v_a_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0(v_00_u03b2_131_, v_m_132_, v_a_133_);
lean_dec(v_a_133_);
lean_dec_ref(v_m_132_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0(lean_object* v_00_u03b2_135_, lean_object* v_m_136_, lean_object* v_query_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(v_m_136_, v_query_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_139_, lean_object* v_m_140_, lean_object* v_query_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0(v_00_u03b2_139_, v_m_140_, v_query_141_);
lean_dec(v_query_141_);
lean_dec_ref(v_m_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_143_, lean_object* v_m_144_, lean_object* v_query_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1___redArg(v_m_144_, v_query_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_147_, lean_object* v_m_148_, lean_object* v_query_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1(v_00_u03b2_147_, v_m_148_, v_query_149_);
lean_dec(v_query_149_);
lean_dec_ref(v_m_148_);
return v_res_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_151_, lean_object* v_m_152_, lean_object* v_query_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_, lean_object* v_x_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(v_m_152_, v_query_153_, v_x_154_, v_x_155_, v_x_156_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_159_, lean_object* v_m_160_, lean_object* v_query_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_159_, v_m_160_, v_query_161_, v_x_162_, v_x_163_, v_x_164_, v_x_165_);
lean_dec(v_query_161_);
lean_dec_ref(v_m_160_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_renameVars(lean_object* v_e_169_, lean_object* v_f_170_){
_start:
{
switch(lean_obj_tag(v_e_169_))
{
case 0:
{
return v_e_169_;
}
case 1:
{
lean_object* v_i_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_181_; 
v_i_171_ = lean_ctor_get(v_e_169_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v_e_169_);
if (v_isSharedCheck_181_ == 0)
{
v___x_173_ = v_e_169_;
v_isShared_174_ = v_isSharedCheck_181_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_i_171_);
lean_dec(v_e_169_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_181_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(v_f_170_, v_i_171_);
lean_dec(v_i_171_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_176_; 
lean_del_object(v___x_173_);
v___x_176_ = ((lean_object*)(l_Lean_Grind_Linarith_Expr_renameVars___closed__0));
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_179_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_177_);
lean_dec_ref_known(v___x_175_, 1);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v_val_177_);
v___x_179_ = v___x_173_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v_val_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
case 2:
{
lean_object* v_a_182_; lean_object* v_b_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_192_; 
v_a_182_ = lean_ctor_get(v_e_169_, 0);
v_b_183_ = lean_ctor_get(v_e_169_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_e_169_);
if (v_isSharedCheck_192_ == 0)
{
v___x_185_ = v_e_169_;
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_b_183_);
lean_inc(v_a_182_);
lean_dec(v_e_169_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_192_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_190_; 
v___x_187_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_182_, v_f_170_);
v___x_188_ = l_Lean_Grind_Linarith_Expr_renameVars(v_b_183_, v_f_170_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 1, v___x_188_);
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_190_ = v___x_185_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
case 3:
{
lean_object* v_a_193_; lean_object* v_b_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_203_; 
v_a_193_ = lean_ctor_get(v_e_169_, 0);
v_b_194_ = lean_ctor_get(v_e_169_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_e_169_);
if (v_isSharedCheck_203_ == 0)
{
v___x_196_ = v_e_169_;
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_b_194_);
lean_inc(v_a_193_);
lean_dec(v_e_169_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_203_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_198_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_193_, v_f_170_);
v___x_199_ = l_Lean_Grind_Linarith_Expr_renameVars(v_b_194_, v_f_170_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 1, v___x_199_);
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_201_ = v___x_196_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
case 4:
{
lean_object* v_a_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_212_; 
v_a_204_ = lean_ctor_get(v_e_169_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v_e_169_);
if (v_isSharedCheck_212_ == 0)
{
v___x_206_ = v_e_169_;
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_a_204_);
lean_dec(v_e_169_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_212_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_204_, v_f_170_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 0, v___x_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
case 5:
{
lean_object* v_k_213_; lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_222_; 
v_k_213_ = lean_ctor_get(v_e_169_, 0);
v_a_214_ = lean_ctor_get(v_e_169_, 1);
v_isSharedCheck_222_ = !lean_is_exclusive(v_e_169_);
if (v_isSharedCheck_222_ == 0)
{
v___x_216_ = v_e_169_;
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_inc(v_k_213_);
lean_dec(v_e_169_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_214_, v_f_170_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 1, v___x_218_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_k_213_);
lean_ctor_set(v_reuseFailAlloc_221_, 1, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
default: 
{
lean_object* v_k_223_; lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_232_; 
v_k_223_ = lean_ctor_get(v_e_169_, 0);
v_a_224_ = lean_ctor_get(v_e_169_, 1);
v_isSharedCheck_232_ = !lean_is_exclusive(v_e_169_);
if (v_isSharedCheck_232_ == 0)
{
v___x_226_ = v_e_169_;
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_inc(v_k_223_);
lean_dec(v_e_169_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_232_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_230_; 
v___x_228_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_224_, v_f_170_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_228_);
v___x_230_ = v___x_226_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_k_223_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v___x_228_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_renameVars___boxed(lean_object* v_e_233_, lean_object* v_f_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Grind_Linarith_Expr_renameVars(v_e_233_, v_f_234_);
lean_dec_ref(v_f_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_collectVars(lean_object* v_p_236_, lean_object* v_a_237_){
_start:
{
if (lean_obj_tag(v_p_236_) == 0)
{
return v_a_237_;
}
else
{
lean_object* v_v_238_; lean_object* v_p_239_; lean_object* v___x_240_; 
v_v_238_ = lean_ctor_get(v_p_236_, 1);
lean_inc(v_v_238_);
v_p_239_ = lean_ctor_get(v_p_236_, 2);
lean_inc(v_p_239_);
lean_dec_ref_known(v_p_236_, 3);
v___x_240_ = l_Lean_Meta_Grind_collectVar(v_v_238_, v_a_237_);
v_p_236_ = v_p_239_;
v_a_237_ = v___x_240_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_collectVars(lean_object* v_e_242_, lean_object* v_a_243_){
_start:
{
lean_object* v_a_245_; lean_object* v_b_246_; lean_object* v___y_247_; 
switch(lean_obj_tag(v_e_242_))
{
case 0:
{
return v_a_243_;
}
case 1:
{
lean_object* v_i_250_; lean_object* v___x_251_; 
v_i_250_ = lean_ctor_get(v_e_242_, 0);
lean_inc(v_i_250_);
lean_dec_ref_known(v_e_242_, 1);
v___x_251_ = l_Lean_Meta_Grind_collectVar(v_i_250_, v_a_243_);
return v___x_251_;
}
case 4:
{
lean_object* v_a_252_; 
v_a_252_ = lean_ctor_get(v_e_242_, 0);
lean_inc(v_a_252_);
lean_dec_ref_known(v_e_242_, 1);
v_e_242_ = v_a_252_;
goto _start;
}
case 5:
{
lean_object* v_a_254_; 
v_a_254_ = lean_ctor_get(v_e_242_, 1);
lean_inc(v_a_254_);
lean_dec_ref_known(v_e_242_, 2);
v_e_242_ = v_a_254_;
goto _start;
}
case 6:
{
lean_object* v_a_256_; 
v_a_256_ = lean_ctor_get(v_e_242_, 1);
lean_inc(v_a_256_);
lean_dec_ref_known(v_e_242_, 2);
v_e_242_ = v_a_256_;
goto _start;
}
default: 
{
lean_object* v_a_258_; lean_object* v_b_259_; 
v_a_258_ = lean_ctor_get(v_e_242_, 0);
lean_inc(v_a_258_);
v_b_259_ = lean_ctor_get(v_e_242_, 1);
lean_inc(v_b_259_);
lean_dec(v_e_242_);
v_a_245_ = v_a_258_;
v_b_246_ = v_b_259_;
v___y_247_ = v_a_243_;
goto v___jp_244_;
}
}
v___jp_244_:
{
lean_object* v___x_248_; 
v___x_248_ = l_Lean_Grind_Linarith_Expr_collectVars(v_a_245_, v___y_247_);
v_e_242_ = v_b_246_;
v_a_243_ = v___x_248_;
goto _start;
}
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
}
#ifdef __cplusplus
}
#endif
