// Lean compiler output
// Module: Lean.Meta.Sym.Arith.VarRename
// Imports: public import Init.Grind.Ring.CommSemiringAdapter public import Lean.Meta.Tactic.Grind.VarRename
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_CommRing_Expr_renameVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_Expr_renameVars___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_Expr_renameVars___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(v_m_52_, v_query_53_, v_x_54_, v_x_55_, v_x_56_);
lean_dec(v_query_53_);
lean_dec_ref(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1___redArg(lean_object* v_m_58_, lean_object* v_query_59_){
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
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(v_m_58_, v_query_59_, v___x_75_, v___x_61_, v___x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_77_, lean_object* v_query_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1___redArg(v_m_77_, v_query_78_);
lean_dec(v_query_78_);
lean_dec_ref(v_m_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(lean_object* v_m_80_, lean_object* v_query_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1___redArg(v_m_80_, v_query_81_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg___boxed(lean_object* v_m_94_, lean_object* v_query_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(v_m_94_, v_query_95_);
lean_dec(v_query_95_);
lean_dec_ref(v_m_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(lean_object* v_m_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(v_m_97_, v_a_98_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg___boxed(lean_object* v_m_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_m_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_m_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars(lean_object* v_pw_106_, lean_object* v_f_107_){
_start:
{
lean_object* v_x_108_; lean_object* v_k_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_122_; 
v_x_108_ = lean_ctor_get(v_pw_106_, 0);
v_k_109_ = lean_ctor_get(v_pw_106_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_pw_106_);
if (v_isSharedCheck_122_ == 0)
{
v___x_111_ = v_pw_106_;
v_isShared_112_ = v_isSharedCheck_122_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_k_109_);
lean_inc(v_x_108_);
lean_dec(v_pw_106_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_122_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_113_; 
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_f_107_, v_x_108_);
lean_dec(v_x_108_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_114_ = lean_unsigned_to_nat(0u);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_114_);
v___x_116_ = v___x_111_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_k_109_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
else
{
lean_object* v_val_118_; lean_object* v___x_120_; 
v_val_118_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_val_118_);
lean_dec_ref_known(v___x_113_, 1);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v_val_118_);
v___x_120_ = v___x_111_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_val_118_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_k_109_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars___boxed(lean_object* v_pw_123_, lean_object* v_f_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Grind_CommRing_Power_renameVars(v_pw_123_, v_f_124_);
lean_dec_ref(v_f_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0(lean_object* v_00_u03b2_126_, lean_object* v_m_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_m_127_, v_a_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___boxed(lean_object* v_00_u03b2_130_, lean_object* v_m_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0(v_00_u03b2_130_, v_m_131_, v_a_132_);
lean_dec(v_a_132_);
lean_dec_ref(v_m_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0(lean_object* v_00_u03b2_134_, lean_object* v_m_135_, lean_object* v_query_136_){
_start:
{
lean_object* v___x_137_; 
v___x_137_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(v_m_135_, v_query_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_138_, lean_object* v_m_139_, lean_object* v_query_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0(v_00_u03b2_138_, v_m_139_, v_query_140_);
lean_dec(v_query_140_);
lean_dec_ref(v_m_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_142_, lean_object* v_m_143_, lean_object* v_query_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1___redArg(v_m_143_, v_query_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_146_, lean_object* v_m_147_, lean_object* v_query_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1(v_00_u03b2_146_, v_m_147_, v_query_148_);
lean_dec(v_query_148_);
lean_dec_ref(v_m_147_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_150_, lean_object* v_m_151_, lean_object* v_query_152_, lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(v_m_151_, v_query_152_, v_x_153_, v_x_154_, v_x_155_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_158_, lean_object* v_m_159_, lean_object* v_query_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_158_, v_m_159_, v_query_160_, v_x_161_, v_x_162_, v_x_163_, v_x_164_);
lean_dec(v_query_160_);
lean_dec_ref(v_m_159_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars(lean_object* v_m_166_, lean_object* v_f_167_){
_start:
{
if (lean_obj_tag(v_m_166_) == 0)
{
return v_m_166_;
}
else
{
lean_object* v_p_168_; lean_object* v_m_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_178_; 
v_p_168_ = lean_ctor_get(v_m_166_, 0);
v_m_169_ = lean_ctor_get(v_m_166_, 1);
v_isSharedCheck_178_ = !lean_is_exclusive(v_m_166_);
if (v_isSharedCheck_178_ == 0)
{
v___x_171_ = v_m_166_;
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_m_169_);
lean_inc(v_p_168_);
lean_dec(v_m_166_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = l_Lean_Grind_CommRing_Power_renameVars(v_p_168_, v_f_167_);
v___x_174_ = l_Lean_Grind_CommRing_Mon_renameVars(v_m_169_, v_f_167_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_174_);
lean_ctor_set(v___x_171_, 0, v___x_173_);
v___x_176_ = v___x_171_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars___boxed(lean_object* v_m_179_, lean_object* v_f_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Grind_CommRing_Mon_renameVars(v_m_179_, v_f_180_);
lean_dec_ref(v_f_180_);
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars(lean_object* v_p_182_, lean_object* v_f_183_){
_start:
{
if (lean_obj_tag(v_p_182_) == 0)
{
return v_p_182_;
}
else
{
lean_object* v_k_184_; lean_object* v_v_185_; lean_object* v_p_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
v_k_184_ = lean_ctor_get(v_p_182_, 0);
v_v_185_ = lean_ctor_get(v_p_182_, 1);
v_p_186_ = lean_ctor_get(v_p_182_, 2);
v_isSharedCheck_195_ = !lean_is_exclusive(v_p_182_);
if (v_isSharedCheck_195_ == 0)
{
v___x_188_ = v_p_182_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_p_186_);
lean_inc(v_v_185_);
lean_inc(v_k_184_);
lean_dec(v_p_182_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = l_Lean_Grind_CommRing_Mon_renameVars(v_v_185_, v_f_183_);
v___x_191_ = l_Lean_Grind_CommRing_Poly_renameVars(v_p_186_, v_f_183_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 2, v___x_191_);
lean_ctor_set(v___x_188_, 1, v___x_190_);
v___x_193_ = v___x_188_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_k_184_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars___boxed(lean_object* v_p_196_, lean_object* v_f_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_Grind_CommRing_Poly_renameVars(v_p_196_, v_f_197_);
lean_dec_ref(v_f_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars(lean_object* v_e_201_, lean_object* v_f_202_){
_start:
{
switch(lean_obj_tag(v_e_201_))
{
case 3:
{
lean_object* v_i_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_213_; 
v_i_203_ = lean_ctor_get(v_e_201_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v_e_201_);
if (v_isSharedCheck_213_ == 0)
{
v___x_205_ = v_e_201_;
v_isShared_206_ = v_isSharedCheck_213_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_i_203_);
lean_dec(v_e_201_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_213_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; 
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_f_202_, v_i_203_);
lean_dec(v_i_203_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v___x_208_; 
lean_del_object(v___x_205_);
v___x_208_ = ((lean_object*)(l_Lean_Grind_CommRing_Expr_renameVars___closed__0));
return v___x_208_;
}
else
{
lean_object* v_val_209_; lean_object* v___x_211_; 
v_val_209_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_val_209_);
lean_dec_ref_known(v___x_207_, 1);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 0, v_val_209_);
v___x_211_ = v___x_205_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_val_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
case 4:
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_222_; 
v_a_214_ = lean_ctor_get(v_e_201_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_e_201_);
if (v_isSharedCheck_222_ == 0)
{
v___x_216_ = v_e_201_;
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v_e_201_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_222_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_218_; lean_object* v___x_220_; 
v___x_218_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_214_, v_f_202_);
if (v_isShared_217_ == 0)
{
lean_ctor_set(v___x_216_, 0, v___x_218_);
v___x_220_ = v___x_216_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v___x_218_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
case 5:
{
lean_object* v_a_223_; lean_object* v_b_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_233_; 
v_a_223_ = lean_ctor_get(v_e_201_, 0);
v_b_224_ = lean_ctor_get(v_e_201_, 1);
v_isSharedCheck_233_ = !lean_is_exclusive(v_e_201_);
if (v_isSharedCheck_233_ == 0)
{
v___x_226_ = v_e_201_;
v_isShared_227_ = v_isSharedCheck_233_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_b_224_);
lean_inc(v_a_223_);
lean_dec(v_e_201_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_233_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_228_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_223_, v_f_202_);
v___x_229_ = l_Lean_Grind_CommRing_Expr_renameVars(v_b_224_, v_f_202_);
if (v_isShared_227_ == 0)
{
lean_ctor_set(v___x_226_, 1, v___x_229_);
lean_ctor_set(v___x_226_, 0, v___x_228_);
v___x_231_ = v___x_226_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_228_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
case 6:
{
lean_object* v_a_234_; lean_object* v_b_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_244_; 
v_a_234_ = lean_ctor_get(v_e_201_, 0);
v_b_235_ = lean_ctor_get(v_e_201_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_e_201_);
if (v_isSharedCheck_244_ == 0)
{
v___x_237_ = v_e_201_;
v_isShared_238_ = v_isSharedCheck_244_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_b_235_);
lean_inc(v_a_234_);
lean_dec(v_e_201_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_244_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_239_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_234_, v_f_202_);
v___x_240_ = l_Lean_Grind_CommRing_Expr_renameVars(v_b_235_, v_f_202_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_240_);
lean_ctor_set(v___x_237_, 0, v___x_239_);
v___x_242_ = v___x_237_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
case 7:
{
lean_object* v_a_245_; lean_object* v_b_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_255_; 
v_a_245_ = lean_ctor_get(v_e_201_, 0);
v_b_246_ = lean_ctor_get(v_e_201_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_e_201_);
if (v_isSharedCheck_255_ == 0)
{
v___x_248_ = v_e_201_;
v_isShared_249_ = v_isSharedCheck_255_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_b_246_);
lean_inc(v_a_245_);
lean_dec(v_e_201_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_255_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_253_; 
v___x_250_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_245_, v_f_202_);
v___x_251_ = l_Lean_Grind_CommRing_Expr_renameVars(v_b_246_, v_f_202_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v___x_251_);
lean_ctor_set(v___x_248_, 0, v___x_250_);
v___x_253_ = v___x_248_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v___x_250_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v___x_251_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
case 8:
{
lean_object* v_a_256_; lean_object* v_k_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_265_; 
v_a_256_ = lean_ctor_get(v_e_201_, 0);
v_k_257_ = lean_ctor_get(v_e_201_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_e_201_);
if (v_isSharedCheck_265_ == 0)
{
v___x_259_ = v_e_201_;
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_k_257_);
lean_inc(v_a_256_);
lean_dec(v_e_201_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_265_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_263_; 
v___x_261_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_256_, v_f_202_);
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_261_);
v___x_263_ = v___x_259_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_261_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_k_257_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
default: 
{
return v_e_201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars___boxed(lean_object* v_e_266_, lean_object* v_f_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Grind_CommRing_Expr_renameVars(v_e_266_, v_f_267_);
lean_dec_ref(v_f_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_collectVars(lean_object* v_pw_269_, lean_object* v_a_270_){
_start:
{
lean_object* v_x_271_; lean_object* v___x_272_; 
v_x_271_ = lean_ctor_get(v_pw_269_, 0);
lean_inc(v_x_271_);
lean_dec_ref(v_pw_269_);
v___x_272_ = l_Lean_Meta_Grind_collectVar(v_x_271_, v_a_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_collectVars(lean_object* v_m_273_, lean_object* v_a_274_){
_start:
{
if (lean_obj_tag(v_m_273_) == 0)
{
return v_a_274_;
}
else
{
lean_object* v_p_275_; lean_object* v_m_276_; lean_object* v___x_277_; 
v_p_275_ = lean_ctor_get(v_m_273_, 0);
lean_inc_ref(v_p_275_);
v_m_276_ = lean_ctor_get(v_m_273_, 1);
lean_inc(v_m_276_);
lean_dec_ref_known(v_m_273_, 2);
v___x_277_ = l_Lean_Grind_CommRing_Power_collectVars(v_p_275_, v_a_274_);
v_m_273_ = v_m_276_;
v_a_274_ = v___x_277_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_collectVars(lean_object* v_p_279_, lean_object* v_a_280_){
_start:
{
if (lean_obj_tag(v_p_279_) == 0)
{
lean_dec_ref_known(v_p_279_, 1);
return v_a_280_;
}
else
{
lean_object* v_v_281_; lean_object* v_p_282_; lean_object* v___x_283_; 
v_v_281_ = lean_ctor_get(v_p_279_, 1);
lean_inc(v_v_281_);
v_p_282_ = lean_ctor_get(v_p_279_, 2);
lean_inc_ref(v_p_282_);
lean_dec_ref_known(v_p_279_, 3);
v___x_283_ = l_Lean_Grind_CommRing_Mon_collectVars(v_v_281_, v_a_280_);
v_p_279_ = v_p_282_;
v_a_280_ = v___x_283_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_collectVars(lean_object* v_e_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_a_288_; lean_object* v_b_289_; lean_object* v___y_290_; 
switch(lean_obj_tag(v_e_285_))
{
case 3:
{
lean_object* v_i_293_; lean_object* v___x_294_; 
v_i_293_ = lean_ctor_get(v_e_285_, 0);
lean_inc(v_i_293_);
lean_dec_ref_known(v_e_285_, 1);
v___x_294_ = l_Lean_Meta_Grind_collectVar(v_i_293_, v_a_286_);
return v___x_294_;
}
case 4:
{
lean_object* v_a_295_; 
v_a_295_ = lean_ctor_get(v_e_285_, 0);
lean_inc_ref(v_a_295_);
lean_dec_ref_known(v_e_285_, 1);
v_e_285_ = v_a_295_;
goto _start;
}
case 5:
{
lean_object* v_a_297_; lean_object* v_b_298_; 
v_a_297_ = lean_ctor_get(v_e_285_, 0);
lean_inc_ref(v_a_297_);
v_b_298_ = lean_ctor_get(v_e_285_, 1);
lean_inc_ref(v_b_298_);
lean_dec_ref_known(v_e_285_, 2);
v_a_288_ = v_a_297_;
v_b_289_ = v_b_298_;
v___y_290_ = v_a_286_;
goto v___jp_287_;
}
case 6:
{
lean_object* v_a_299_; lean_object* v_b_300_; 
v_a_299_ = lean_ctor_get(v_e_285_, 0);
lean_inc_ref(v_a_299_);
v_b_300_ = lean_ctor_get(v_e_285_, 1);
lean_inc_ref(v_b_300_);
lean_dec_ref_known(v_e_285_, 2);
v_a_288_ = v_a_299_;
v_b_289_ = v_b_300_;
v___y_290_ = v_a_286_;
goto v___jp_287_;
}
case 7:
{
lean_object* v_a_301_; lean_object* v_b_302_; 
v_a_301_ = lean_ctor_get(v_e_285_, 0);
lean_inc_ref(v_a_301_);
v_b_302_ = lean_ctor_get(v_e_285_, 1);
lean_inc_ref(v_b_302_);
lean_dec_ref_known(v_e_285_, 2);
v_a_288_ = v_a_301_;
v_b_289_ = v_b_302_;
v___y_290_ = v_a_286_;
goto v___jp_287_;
}
case 8:
{
lean_object* v_a_303_; 
v_a_303_ = lean_ctor_get(v_e_285_, 0);
lean_inc_ref(v_a_303_);
lean_dec_ref_known(v_e_285_, 2);
v_e_285_ = v_a_303_;
goto _start;
}
default: 
{
lean_dec_ref(v_e_285_);
return v_a_286_;
}
}
v___jp_287_:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_Grind_CommRing_Expr_collectVars(v_a_288_, v___y_290_);
v_e_285_ = v_b_289_;
v_a_286_ = v___x_291_;
goto _start;
}
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_VarRename(builtin);
}
#ifdef __cplusplus
}
#endif
