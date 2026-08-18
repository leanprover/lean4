// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.VarRename
// Imports: public import Init.Grind.AC public import Lean.Meta.Tactic.Grind.VarRename
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_Grind_collectVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_AC_Seq_renameVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_Seq_renameVars___closed__0 = (const lean_object*)&l_Lean_Grind_AC_Seq_renameVars___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_AC_Expr_renameVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_Expr_renameVars___closed__0 = (const lean_object*)&l_Lean_Grind_AC_Expr_renameVars___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_m_1_, lean_object* v_query_2_, lean_object* v_x_3_, lean_object* v_x_4_, lean_object* v_x_5_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_m_52_, lean_object* v_query_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(v_m_52_, v_query_53_, v_x_54_, v_x_55_, v_x_56_);
lean_dec(v_query_53_);
lean_dec_ref(v_m_52_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1___redArg(lean_object* v_m_58_, lean_object* v_query_59_){
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
v___x_76_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(v_m_58_, v_query_59_, v___x_75_, v___x_61_, v___x_74_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_m_77_, lean_object* v_query_78_){
_start:
{
lean_object* v_res_79_; 
v_res_79_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1___redArg(v_m_77_, v_query_78_);
lean_dec(v_query_78_);
lean_dec_ref(v_m_77_);
return v_res_79_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(lean_object* v_m_80_, lean_object* v_query_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1___redArg(v_m_80_, v_query_81_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg___boxed(lean_object* v_m_94_, lean_object* v_query_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(v_m_94_, v_query_95_);
lean_dec(v_query_95_);
lean_dec_ref(v_m_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(lean_object* v_m_97_, lean_object* v_a_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(v_m_97_, v_a_98_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg___boxed(lean_object* v_m_103_, lean_object* v_a_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_m_103_, v_a_104_);
lean_dec(v_a_104_);
lean_dec_ref(v_m_103_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_renameVars(lean_object* v_s_108_, lean_object* v_f_109_){
_start:
{
if (lean_obj_tag(v_s_108_) == 0)
{
lean_object* v_x_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_120_; 
v_x_110_ = lean_ctor_get(v_s_108_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_s_108_);
if (v_isSharedCheck_120_ == 0)
{
v___x_112_ = v_s_108_;
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_x_110_);
lean_dec(v_s_108_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_120_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_114_; 
v___x_114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_f_109_, v_x_110_);
lean_dec(v_x_110_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v___x_115_; 
lean_del_object(v___x_112_);
v___x_115_ = ((lean_object*)(l_Lean_Grind_AC_Seq_renameVars___closed__0));
return v___x_115_;
}
else
{
lean_object* v_val_116_; lean_object* v___x_118_; 
v_val_116_ = lean_ctor_get(v___x_114_, 0);
lean_inc(v_val_116_);
lean_dec_ref_known(v___x_114_, 1);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v_val_116_);
v___x_118_ = v___x_112_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v_val_116_);
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
else
{
lean_object* v_x_121_; lean_object* v_s_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_135_; 
v_x_121_ = lean_ctor_get(v_s_108_, 0);
v_s_122_ = lean_ctor_get(v_s_108_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_s_108_);
if (v_isSharedCheck_135_ == 0)
{
v___x_124_ = v_s_108_;
v_isShared_125_ = v_isSharedCheck_135_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_s_122_);
lean_inc(v_x_121_);
lean_dec(v_s_108_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_135_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___y_127_; lean_object* v___x_132_; 
v___x_132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_f_109_, v_x_121_);
lean_dec(v_x_121_);
if (lean_obj_tag(v___x_132_) == 0)
{
lean_object* v___x_133_; 
v___x_133_ = lean_unsigned_to_nat(0u);
v___y_127_ = v___x_133_;
goto v___jp_126_;
}
else
{
lean_object* v_val_134_; 
v_val_134_ = lean_ctor_get(v___x_132_, 0);
lean_inc(v_val_134_);
lean_dec_ref_known(v___x_132_, 1);
v___y_127_ = v_val_134_;
goto v___jp_126_;
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_128_ = l_Lean_Grind_AC_Seq_renameVars(v_s_122_, v_f_109_);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 1, v___x_128_);
lean_ctor_set(v___x_124_, 0, v___y_127_);
v___x_130_ = v___x_124_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___y_127_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_128_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_renameVars___boxed(lean_object* v_s_136_, lean_object* v_f_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_Grind_AC_Seq_renameVars(v_s_136_, v_f_137_);
lean_dec_ref(v_f_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0(lean_object* v_00_u03b2_139_, lean_object* v_m_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; 
v___x_142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_m_140_, v_a_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___boxed(lean_object* v_00_u03b2_143_, lean_object* v_m_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0(v_00_u03b2_143_, v_m_144_, v_a_145_);
lean_dec(v_a_145_);
lean_dec_ref(v_m_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0(lean_object* v_00_u03b2_147_, lean_object* v_m_148_, lean_object* v_query_149_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(v_m_148_, v_query_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_151_, lean_object* v_m_152_, lean_object* v_query_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0(v_00_u03b2_151_, v_m_152_, v_query_153_);
lean_dec(v_query_153_);
lean_dec_ref(v_m_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_155_, lean_object* v_m_156_, lean_object* v_query_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1___redArg(v_m_156_, v_query_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_159_, lean_object* v_m_160_, lean_object* v_query_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1(v_00_u03b2_159_, v_m_160_, v_query_161_);
lean_dec(v_query_161_);
lean_dec_ref(v_m_160_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_163_, lean_object* v_m_164_, lean_object* v_query_165_, lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_, lean_object* v_x_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2___redArg(v_m_164_, v_query_165_, v_x_166_, v_x_167_, v_x_168_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_171_, lean_object* v_m_172_, lean_object* v_query_173_, lean_object* v_x_174_, lean_object* v_x_175_, lean_object* v_x_176_, lean_object* v_x_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_171_, v_m_172_, v_query_173_, v_x_174_, v_x_175_, v_x_176_, v_x_177_);
lean_dec(v_query_173_);
lean_dec_ref(v_m_172_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_renameVars(lean_object* v_e_181_, lean_object* v_f_182_){
_start:
{
if (lean_obj_tag(v_e_181_) == 0)
{
lean_object* v_x_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_193_; 
v_x_183_ = lean_ctor_get(v_e_181_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v_e_181_);
if (v_isSharedCheck_193_ == 0)
{
v___x_185_ = v_e_181_;
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_x_183_);
lean_dec(v_e_181_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_193_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; 
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_f_182_, v_x_183_);
lean_dec(v_x_183_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v___x_188_; 
lean_del_object(v___x_185_);
v___x_188_ = ((lean_object*)(l_Lean_Grind_AC_Expr_renameVars___closed__0));
return v___x_188_;
}
else
{
lean_object* v_val_189_; lean_object* v___x_191_; 
v_val_189_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_val_189_);
lean_dec_ref_known(v___x_187_, 1);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v_val_189_);
v___x_191_ = v___x_185_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_val_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v_lhs_194_; lean_object* v_rhs_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_204_; 
v_lhs_194_ = lean_ctor_get(v_e_181_, 0);
v_rhs_195_ = lean_ctor_get(v_e_181_, 1);
v_isSharedCheck_204_ = !lean_is_exclusive(v_e_181_);
if (v_isSharedCheck_204_ == 0)
{
v___x_197_ = v_e_181_;
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_rhs_195_);
lean_inc(v_lhs_194_);
lean_dec(v_e_181_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_204_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_199_ = l_Lean_Grind_AC_Expr_renameVars(v_lhs_194_, v_f_182_);
v___x_200_ = l_Lean_Grind_AC_Expr_renameVars(v_rhs_195_, v_f_182_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 1, v___x_200_);
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_202_ = v___x_197_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_199_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_renameVars___boxed(lean_object* v_e_205_, lean_object* v_f_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Grind_AC_Expr_renameVars(v_e_205_, v_f_206_);
lean_dec_ref(v_f_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_collectVars(lean_object* v_s_208_, lean_object* v_a_209_){
_start:
{
if (lean_obj_tag(v_s_208_) == 0)
{
lean_object* v_x_210_; lean_object* v___x_211_; 
v_x_210_ = lean_ctor_get(v_s_208_, 0);
lean_inc(v_x_210_);
lean_dec_ref_known(v_s_208_, 1);
v___x_211_ = l_Lean_Meta_Grind_collectVar(v_x_210_, v_a_209_);
return v___x_211_;
}
else
{
lean_object* v_x_212_; lean_object* v_s_213_; lean_object* v___x_214_; 
v_x_212_ = lean_ctor_get(v_s_208_, 0);
lean_inc(v_x_212_);
v_s_213_ = lean_ctor_get(v_s_208_, 1);
lean_inc_ref(v_s_213_);
lean_dec_ref_known(v_s_208_, 2);
v___x_214_ = l_Lean_Meta_Grind_collectVar(v_x_212_, v_a_209_);
v_s_208_ = v_s_213_;
v_a_209_ = v___x_214_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_collectVars(lean_object* v_e_216_, lean_object* v_a_217_){
_start:
{
if (lean_obj_tag(v_e_216_) == 0)
{
lean_object* v_x_218_; lean_object* v___x_219_; 
v_x_218_ = lean_ctor_get(v_e_216_, 0);
lean_inc(v_x_218_);
lean_dec_ref_known(v_e_216_, 1);
v___x_219_ = l_Lean_Meta_Grind_collectVar(v_x_218_, v_a_217_);
return v___x_219_;
}
else
{
lean_object* v_lhs_220_; lean_object* v_rhs_221_; lean_object* v___x_222_; 
v_lhs_220_ = lean_ctor_get(v_e_216_, 0);
lean_inc_ref(v_lhs_220_);
v_rhs_221_ = lean_ctor_get(v_e_216_, 1);
lean_inc_ref(v_rhs_221_);
lean_dec_ref_known(v_e_216_, 2);
v___x_222_ = l_Lean_Grind_AC_Expr_collectVars(v_lhs_220_, v_a_217_);
v_e_216_ = v_rhs_221_;
v_a_217_ = v___x_222_;
goto _start;
}
}
}
lean_object* runtime_initialize_Init_Grind_AC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_AC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
}
#ifdef __cplusplus
}
#endif
