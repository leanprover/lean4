// Lean compiler output
// Module: Lean.Util.PtrSet
// Imports: public import Init.Data.Hashable public import Std.Data.HashSet.Basic
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashablePtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashablePtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashablePtr___closed__0 = (const lean_object*)&l_Lean_instHashablePtr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqPtr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqPtr___closed__0 = (const lean_object*)&l_Lean_instBEqPtr___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___lam__0(lean_object* v_a_1_){
_start:
{
size_t v___x_2_; uint64_t v___x_3_; uint64_t v___x_4_; uint64_t v___x_5_; 
v___x_2_ = lean_ptr_addr(v_a_1_);
v___x_3_ = lean_usize_to_uint64(v___x_2_);
v___x_4_ = 11ULL;
v___x_5_ = lean_uint64_mix_hash(v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object* v_a_6_){
_start:
{
uint64_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Lean_instHashablePtr___lam__0(v_a_6_);
lean_dec(v_a_6_);
v_r_8_ = lean_box_uint64(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object* v_00_u03b1_10_){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
return v___f_11_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___lam__0(lean_object* v_a_12_, lean_object* v_b_13_){
_start:
{
size_t v___x_14_; size_t v___x_15_; uint8_t v___x_16_; 
v___x_14_ = lean_ptr_addr(v_a_12_);
v___x_15_ = lean_ptr_addr(v_b_13_);
v___x_16_ = lean_usize_dec_eq(v___x_14_, v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
uint8_t v_res_19_; lean_object* v_r_20_; 
v_res_19_ = l_Lean_instBEqPtr___lam__0(v_a_17_, v_b_18_);
lean_dec(v_b_18_);
lean_dec(v_a_17_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object* v_00_u03b1_22_){
_start:
{
lean_object* v___f_23_; 
v___f_23_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
return v___f_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object* v_capacity_24_){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v_cellCount_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_25_ = lean_unsigned_to_nat(4u);
v___x_26_ = lean_nat_mul(v_capacity_24_, v___x_25_);
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = lean_nat_add(v___x_26_, v___x_27_);
lean_dec(v___x_26_);
v___x_29_ = lean_unsigned_to_nat(3u);
v___x_30_ = lean_nat_div(v___x_28_, v___x_29_);
lean_dec(v___x_28_);
v_cellCount_31_ = l_Nat_nextPowerOfTwo(v___x_30_);
lean_dec(v___x_30_);
v___x_32_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_31_);
v___x_33_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_31_);
v___x_34_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_31_);
v___x_35_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_35_, 0, v___x_32_);
lean_ctor_set(v___x_35_, 1, v___x_33_);
lean_ctor_set(v___x_35_, 2, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object* v_capacity_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_mkPtrSet___redArg(v_capacity_36_);
lean_dec(v_capacity_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object* v_00_u03b1_38_, lean_object* v_capacity_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_mkPtrSet___redArg(v_capacity_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object* v_00_u03b1_41_, lean_object* v_capacity_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_mkPtrSet(v_00_u03b1_41_, v_capacity_42_);
lean_dec(v_capacity_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object* v_s_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___f_46_; lean_object* v___f_47_; lean_object* v___x_48_; lean_object* v___y_50_; lean_object* v_i_51_; lean_object* v___y_57_; lean_object* v___y_67_; lean_object* v_i_68_; lean_object* v___x_83_; 
v___f_46_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_47_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_48_ = lean_box(0);
lean_inc(v_a_45_);
v___x_83_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_46_, v___f_47_, v_s_44_, v_a_45_);
switch(lean_obj_tag(v___x_83_))
{
case 0:
{
lean_dec_ref_known(v___x_83_, 3);
lean_dec(v_a_45_);
return v_s_44_;
}
case 1:
{
lean_object* v_index_84_; lean_object* v_size_85_; lean_object* v_keyArray_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_index_84_ = lean_ctor_get(v___x_83_, 0);
lean_inc(v_index_84_);
lean_dec_ref_known(v___x_83_, 1);
v_size_85_ = lean_ctor_get(v_s_44_, 0);
v_keyArray_86_ = lean_ctor_get(v_s_44_, 1);
v___x_87_ = lean_unsigned_to_nat(1u);
v___x_88_ = lean_nat_add(v_size_85_, v___x_87_);
v___x_89_ = lean_array_get_size(v_keyArray_86_);
v___x_90_ = lean_nat_dec_lt(v___x_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_dec(v___x_88_);
lean_dec(v_index_84_);
goto v___jp_73_;
}
else
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; uint8_t v___x_95_; 
v___x_91_ = lean_unsigned_to_nat(4u);
v___x_92_ = lean_nat_mul(v___x_88_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(3u);
v___x_94_ = lean_nat_mul(v___x_89_, v___x_93_);
v___x_95_ = lean_nat_dec_le(v___x_92_, v___x_94_);
lean_dec(v___x_94_);
lean_dec(v___x_92_);
if (v___x_95_ == 0)
{
lean_dec(v___x_88_);
lean_dec(v_index_84_);
goto v___jp_73_;
}
else
{
lean_object* v___x_96_; 
v___x_96_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_44_, v___x_88_, v_index_84_, v_a_45_, v___x_48_);
lean_dec(v_index_84_);
return v___x_96_;
}
}
}
default: 
{
lean_object* v_size_97_; lean_object* v_keyArray_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v_size_97_ = lean_ctor_get(v_s_44_, 0);
v_keyArray_98_ = lean_ctor_get(v_s_44_, 1);
v___x_99_ = lean_unsigned_to_nat(1u);
v___x_100_ = lean_nat_add(v_size_97_, v___x_99_);
v___x_101_ = lean_array_get_size(v_keyArray_98_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
lean_object* v___x_103_; 
lean_dec(v___x_100_);
v___x_103_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_46_, v___f_47_, v_s_44_);
v___y_57_ = v___x_103_;
goto v___jp_56_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_104_ = lean_unsigned_to_nat(4u);
v___x_105_ = lean_nat_mul(v___x_100_, v___x_104_);
lean_dec(v___x_100_);
v___x_106_ = lean_unsigned_to_nat(3u);
v___x_107_ = lean_nat_mul(v___x_101_, v___x_106_);
v___x_108_ = lean_nat_dec_le(v___x_105_, v___x_107_);
lean_dec(v___x_107_);
lean_dec(v___x_105_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_46_, v___f_47_, v_s_44_);
v___y_57_ = v___x_109_;
goto v___jp_56_;
}
else
{
v___y_57_ = v_s_44_;
goto v___jp_56_;
}
}
}
}
v___jp_49_:
{
lean_object* v_size_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v_size_52_ = lean_ctor_get(v___y_50_, 0);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_add(v_size_52_, v___x_53_);
v___x_55_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_50_, v___x_54_, v_i_51_, v_a_45_, v___x_48_);
lean_dec(v_i_51_);
return v___x_55_;
}
v___jp_56_:
{
lean_object* v___x_58_; 
lean_inc(v_a_45_);
v___x_58_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_46_, v___f_47_, v___y_57_, v_a_45_);
switch(lean_obj_tag(v___x_58_))
{
case 0:
{
lean_object* v_index_59_; lean_object* v_size_60_; lean_object* v___x_61_; 
v_index_59_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_index_59_);
lean_dec_ref_known(v___x_58_, 3);
v_size_60_ = lean_ctor_get(v___y_57_, 0);
lean_inc(v_size_60_);
v___x_61_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_57_, v_size_60_, v_index_59_, v_a_45_, v___x_48_);
lean_dec(v_index_59_);
return v___x_61_;
}
case 1:
{
lean_object* v_index_62_; 
v_index_62_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_index_62_);
lean_dec_ref_known(v___x_58_, 1);
v___y_50_ = v___y_57_;
v_i_51_ = v_index_62_;
goto v___jp_49_;
}
default: 
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_57_, v___x_63_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_index_65_; 
v_index_65_ = lean_ctor_get(v___x_64_, 0);
lean_inc(v_index_65_);
lean_dec_ref_known(v___x_64_, 1);
v___y_50_ = v___y_57_;
v_i_51_ = v_index_65_;
goto v___jp_49_;
}
else
{
lean_dec(v_a_45_);
return v___y_57_;
}
}
}
}
v___jp_66_:
{
lean_object* v_size_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_size_69_ = lean_ctor_get(v___y_67_, 0);
v___x_70_ = lean_unsigned_to_nat(1u);
v___x_71_ = lean_nat_add(v_size_69_, v___x_70_);
v___x_72_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_67_, v___x_71_, v_i_68_, v_a_45_, v___x_48_);
lean_dec(v_i_68_);
return v___x_72_;
}
v___jp_73_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_46_, v___f_47_, v_s_44_);
lean_inc(v_a_45_);
v___x_75_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_46_, v___f_47_, v___x_74_, v_a_45_);
switch(lean_obj_tag(v___x_75_))
{
case 0:
{
lean_object* v_index_76_; lean_object* v_size_77_; lean_object* v___x_78_; 
v_index_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_index_76_);
lean_dec_ref_known(v___x_75_, 3);
v_size_77_ = lean_ctor_get(v___x_74_, 0);
lean_inc(v_size_77_);
v___x_78_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_74_, v_size_77_, v_index_76_, v_a_45_, v___x_48_);
lean_dec(v_index_76_);
return v___x_78_;
}
case 1:
{
lean_object* v_index_79_; 
v_index_79_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_index_79_);
lean_dec_ref_known(v___x_75_, 1);
v___y_67_ = v___x_74_;
v_i_68_ = v_index_79_;
goto v___jp_66_;
}
default: 
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_74_, v___x_80_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_index_82_; 
v_index_82_ = lean_ctor_get(v___x_81_, 0);
lean_inc(v_index_82_);
lean_dec_ref_known(v___x_81_, 1);
v___y_67_ = v___x_74_;
v_i_68_ = v_index_82_;
goto v___jp_66_;
}
else
{
lean_dec(v_a_45_);
return v___x_74_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object* v_00_u03b1_110_, lean_object* v_s_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___y_117_; lean_object* v_i_118_; lean_object* v___y_124_; lean_object* v___y_134_; lean_object* v_i_135_; lean_object* v___x_150_; 
v___f_113_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_114_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_115_ = lean_box(0);
lean_inc(v_a_112_);
v___x_150_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_113_, v___f_114_, v_s_111_, v_a_112_);
switch(lean_obj_tag(v___x_150_))
{
case 0:
{
lean_dec_ref_known(v___x_150_, 3);
lean_dec(v_a_112_);
return v_s_111_;
}
case 1:
{
lean_object* v_index_151_; lean_object* v_size_152_; lean_object* v_keyArray_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v_index_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_index_151_);
lean_dec_ref_known(v___x_150_, 1);
v_size_152_ = lean_ctor_get(v_s_111_, 0);
v_keyArray_153_ = lean_ctor_get(v_s_111_, 1);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_add(v_size_152_, v___x_154_);
v___x_156_ = lean_array_get_size(v_keyArray_153_);
v___x_157_ = lean_nat_dec_lt(v___x_155_, v___x_156_);
if (v___x_157_ == 0)
{
lean_dec(v___x_155_);
lean_dec(v_index_151_);
goto v___jp_140_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_158_ = lean_unsigned_to_nat(4u);
v___x_159_ = lean_nat_mul(v___x_155_, v___x_158_);
v___x_160_ = lean_unsigned_to_nat(3u);
v___x_161_ = lean_nat_mul(v___x_156_, v___x_160_);
v___x_162_ = lean_nat_dec_le(v___x_159_, v___x_161_);
lean_dec(v___x_161_);
lean_dec(v___x_159_);
if (v___x_162_ == 0)
{
lean_dec(v___x_155_);
lean_dec(v_index_151_);
goto v___jp_140_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_111_, v___x_155_, v_index_151_, v_a_112_, v___x_115_);
lean_dec(v_index_151_);
return v___x_163_;
}
}
}
default: 
{
lean_object* v_size_164_; lean_object* v_keyArray_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_size_164_ = lean_ctor_get(v_s_111_, 0);
v_keyArray_165_ = lean_ctor_get(v_s_111_, 1);
v___x_166_ = lean_unsigned_to_nat(1u);
v___x_167_ = lean_nat_add(v_size_164_, v___x_166_);
v___x_168_ = lean_array_get_size(v_keyArray_165_);
v___x_169_ = lean_nat_dec_lt(v___x_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec(v___x_167_);
v___x_170_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_113_, v___f_114_, v_s_111_);
v___y_124_ = v___x_170_;
goto v___jp_123_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_171_ = lean_unsigned_to_nat(4u);
v___x_172_ = lean_nat_mul(v___x_167_, v___x_171_);
lean_dec(v___x_167_);
v___x_173_ = lean_unsigned_to_nat(3u);
v___x_174_ = lean_nat_mul(v___x_168_, v___x_173_);
v___x_175_ = lean_nat_dec_le(v___x_172_, v___x_174_);
lean_dec(v___x_174_);
lean_dec(v___x_172_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
v___x_176_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_113_, v___f_114_, v_s_111_);
v___y_124_ = v___x_176_;
goto v___jp_123_;
}
else
{
v___y_124_ = v_s_111_;
goto v___jp_123_;
}
}
}
}
v___jp_116_:
{
lean_object* v_size_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_size_119_ = lean_ctor_get(v___y_117_, 0);
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_add(v_size_119_, v___x_120_);
v___x_122_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_117_, v___x_121_, v_i_118_, v_a_112_, v___x_115_);
lean_dec(v_i_118_);
return v___x_122_;
}
v___jp_123_:
{
lean_object* v___x_125_; 
lean_inc(v_a_112_);
v___x_125_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_113_, v___f_114_, v___y_124_, v_a_112_);
switch(lean_obj_tag(v___x_125_))
{
case 0:
{
lean_object* v_index_126_; lean_object* v_size_127_; lean_object* v___x_128_; 
v_index_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_index_126_);
lean_dec_ref_known(v___x_125_, 3);
v_size_127_ = lean_ctor_get(v___y_124_, 0);
lean_inc(v_size_127_);
v___x_128_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_124_, v_size_127_, v_index_126_, v_a_112_, v___x_115_);
lean_dec(v_index_126_);
return v___x_128_;
}
case 1:
{
lean_object* v_index_129_; 
v_index_129_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_index_129_);
lean_dec_ref_known(v___x_125_, 1);
v___y_117_ = v___y_124_;
v_i_118_ = v_index_129_;
goto v___jp_116_;
}
default: 
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_124_, v___x_130_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_index_132_; 
v_index_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_index_132_);
lean_dec_ref_known(v___x_131_, 1);
v___y_117_ = v___y_124_;
v_i_118_ = v_index_132_;
goto v___jp_116_;
}
else
{
lean_dec(v_a_112_);
return v___y_124_;
}
}
}
}
v___jp_133_:
{
lean_object* v_size_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_size_136_ = lean_ctor_get(v___y_134_, 0);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = lean_nat_add(v_size_136_, v___x_137_);
v___x_139_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_134_, v___x_138_, v_i_135_, v_a_112_, v___x_115_);
lean_dec(v_i_135_);
return v___x_139_;
}
v___jp_140_:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_113_, v___f_114_, v_s_111_);
lean_inc(v_a_112_);
v___x_142_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_113_, v___f_114_, v___x_141_, v_a_112_);
switch(lean_obj_tag(v___x_142_))
{
case 0:
{
lean_object* v_index_143_; lean_object* v_size_144_; lean_object* v___x_145_; 
v_index_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_index_143_);
lean_dec_ref_known(v___x_142_, 3);
v_size_144_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_size_144_);
v___x_145_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_141_, v_size_144_, v_index_143_, v_a_112_, v___x_115_);
lean_dec(v_index_143_);
return v___x_145_;
}
case 1:
{
lean_object* v_index_146_; 
v_index_146_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_index_146_);
lean_dec_ref_known(v___x_142_, 1);
v___y_134_ = v___x_141_;
v_i_135_ = v_index_146_;
goto v___jp_133_;
}
default: 
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_unsigned_to_nat(0u);
v___x_148_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_141_, v___x_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_index_149_; 
v_index_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_index_149_);
lean_dec_ref_known(v___x_148_, 1);
v___y_134_ = v___x_141_;
v_i_135_ = v_index_149_;
goto v___jp_133_;
}
else
{
lean_dec(v_a_112_);
return v___x_141_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object* v_s_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___f_179_; lean_object* v___f_180_; uint8_t v___x_181_; 
v___f_179_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_180_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_181_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_179_, v___f_180_, v_s_177_, v_a_178_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object* v_s_182_, lean_object* v_a_183_){
_start:
{
uint8_t v_res_184_; lean_object* v_r_185_; 
v_res_184_ = l_Lean_PtrSet_contains___redArg(v_s_182_, v_a_183_);
lean_dec_ref(v_s_182_);
v_r_185_ = lean_box(v_res_184_);
return v_r_185_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object* v_00_u03b1_186_, lean_object* v_s_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___f_189_; lean_object* v___f_190_; uint8_t v___x_191_; 
v___f_189_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_190_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_189_, v___f_190_, v_s_187_, v_a_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object* v_00_u03b1_192_, lean_object* v_s_193_, lean_object* v_a_194_){
_start:
{
uint8_t v_res_195_; lean_object* v_r_196_; 
v_res_195_ = l_Lean_PtrSet_contains(v_00_u03b1_192_, v_s_193_, v_a_194_);
lean_dec_ref(v_s_193_);
v_r_196_ = lean_box(v_res_195_);
return v_r_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object* v_capacity_197_){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v_cellCount_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_198_ = lean_unsigned_to_nat(4u);
v___x_199_ = lean_nat_mul(v_capacity_197_, v___x_198_);
v___x_200_ = lean_unsigned_to_nat(2u);
v___x_201_ = lean_nat_add(v___x_199_, v___x_200_);
lean_dec(v___x_199_);
v___x_202_ = lean_unsigned_to_nat(3u);
v___x_203_ = lean_nat_div(v___x_201_, v___x_202_);
lean_dec(v___x_201_);
v_cellCount_204_ = l_Nat_nextPowerOfTwo(v___x_203_);
lean_dec(v___x_203_);
v___x_205_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_204_);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_204_);
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_204_);
v___x_208_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_208_, 0, v___x_205_);
lean_ctor_set(v___x_208_, 1, v___x_206_);
lean_ctor_set(v___x_208_, 2, v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object* v_capacity_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_mkPtrMap___redArg(v_capacity_209_);
lean_dec(v_capacity_209_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object* v_00_u03b1_211_, lean_object* v_00_u03b2_212_, lean_object* v_capacity_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_mkPtrMap___redArg(v_capacity_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_capacity_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_mkPtrMap(v_00_u03b1_215_, v_00_u03b2_216_, v_capacity_217_);
lean_dec(v_capacity_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object* v_s_219_, lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
lean_object* v___y_223_; lean_object* v_i_224_; lean_object* v___y_230_; lean_object* v_i_231_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___y_239_; lean_object* v___x_258_; 
v___f_236_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_237_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
lean_inc(v_a_220_);
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_236_, v___f_237_, v_s_219_, v_a_220_);
switch(lean_obj_tag(v___x_258_))
{
case 0:
{
lean_object* v_index_259_; lean_object* v_size_260_; lean_object* v___x_261_; 
v_index_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_index_259_);
lean_dec_ref_known(v___x_258_, 3);
v_size_260_ = lean_ctor_get(v_s_219_, 0);
lean_inc(v_size_260_);
v___x_261_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_219_, v_size_260_, v_index_259_, v_a_220_, v_b_221_);
lean_dec(v_index_259_);
return v___x_261_;
}
case 1:
{
lean_object* v_index_262_; lean_object* v_size_263_; lean_object* v_keyArray_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v_index_262_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_index_262_);
lean_dec_ref_known(v___x_258_, 1);
v_size_263_ = lean_ctor_get(v_s_219_, 0);
v_keyArray_264_ = lean_ctor_get(v_s_219_, 1);
v___x_265_ = lean_unsigned_to_nat(1u);
v___x_266_ = lean_nat_add(v_size_263_, v___x_265_);
v___x_267_ = lean_array_get_size(v_keyArray_264_);
v___x_268_ = lean_nat_dec_lt(v___x_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_dec(v___x_266_);
lean_dec(v_index_262_);
goto v___jp_248_;
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_269_ = lean_unsigned_to_nat(4u);
v___x_270_ = lean_nat_mul(v___x_266_, v___x_269_);
v___x_271_ = lean_unsigned_to_nat(3u);
v___x_272_ = lean_nat_mul(v___x_267_, v___x_271_);
v___x_273_ = lean_nat_dec_le(v___x_270_, v___x_272_);
lean_dec(v___x_272_);
lean_dec(v___x_270_);
if (v___x_273_ == 0)
{
lean_dec(v___x_266_);
lean_dec(v_index_262_);
goto v___jp_248_;
}
else
{
lean_object* v___x_274_; 
v___x_274_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_219_, v___x_266_, v_index_262_, v_a_220_, v_b_221_);
lean_dec(v_index_262_);
return v___x_274_;
}
}
}
default: 
{
lean_object* v_size_275_; lean_object* v_keyArray_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint8_t v___x_280_; 
v_size_275_ = lean_ctor_get(v_s_219_, 0);
v_keyArray_276_ = lean_ctor_get(v_s_219_, 1);
v___x_277_ = lean_unsigned_to_nat(1u);
v___x_278_ = lean_nat_add(v_size_275_, v___x_277_);
v___x_279_ = lean_array_get_size(v_keyArray_276_);
v___x_280_ = lean_nat_dec_lt(v___x_278_, v___x_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; 
lean_dec(v___x_278_);
v___x_281_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_236_, v___f_237_, v_s_219_);
v___y_239_ = v___x_281_;
goto v___jp_238_;
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_282_ = lean_unsigned_to_nat(4u);
v___x_283_ = lean_nat_mul(v___x_278_, v___x_282_);
lean_dec(v___x_278_);
v___x_284_ = lean_unsigned_to_nat(3u);
v___x_285_ = lean_nat_mul(v___x_279_, v___x_284_);
v___x_286_ = lean_nat_dec_le(v___x_283_, v___x_285_);
lean_dec(v___x_285_);
lean_dec(v___x_283_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_236_, v___f_237_, v_s_219_);
v___y_239_ = v___x_287_;
goto v___jp_238_;
}
else
{
v___y_239_ = v_s_219_;
goto v___jp_238_;
}
}
}
}
v___jp_222_:
{
lean_object* v_size_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_size_225_ = lean_ctor_get(v___y_223_, 0);
v___x_226_ = lean_unsigned_to_nat(1u);
v___x_227_ = lean_nat_add(v_size_225_, v___x_226_);
v___x_228_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_223_, v___x_227_, v_i_224_, v_a_220_, v_b_221_);
lean_dec(v_i_224_);
return v___x_228_;
}
v___jp_229_:
{
lean_object* v_size_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_size_232_ = lean_ctor_get(v___y_230_, 0);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_size_232_, v___x_233_);
v___x_235_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_230_, v___x_234_, v_i_231_, v_a_220_, v_b_221_);
lean_dec(v_i_231_);
return v___x_235_;
}
v___jp_238_:
{
lean_object* v___x_240_; 
lean_inc(v_a_220_);
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_236_, v___f_237_, v___y_239_, v_a_220_);
switch(lean_obj_tag(v___x_240_))
{
case 0:
{
lean_object* v_index_241_; lean_object* v_size_242_; lean_object* v___x_243_; 
v_index_241_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_index_241_);
lean_dec_ref_known(v___x_240_, 3);
v_size_242_ = lean_ctor_get(v___y_239_, 0);
lean_inc(v_size_242_);
v___x_243_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_239_, v_size_242_, v_index_241_, v_a_220_, v_b_221_);
lean_dec(v_index_241_);
return v___x_243_;
}
case 1:
{
lean_object* v_index_244_; 
v_index_244_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_index_244_);
lean_dec_ref_known(v___x_240_, 1);
v___y_223_ = v___y_239_;
v_i_224_ = v_index_244_;
goto v___jp_222_;
}
default: 
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_239_, v___x_245_);
if (lean_obj_tag(v___x_246_) == 0)
{
lean_object* v_index_247_; 
v_index_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_index_247_);
lean_dec_ref_known(v___x_246_, 1);
v___y_223_ = v___y_239_;
v_i_224_ = v_index_247_;
goto v___jp_222_;
}
else
{
lean_dec(v_b_221_);
lean_dec(v_a_220_);
return v___y_239_;
}
}
}
}
v___jp_248_:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_236_, v___f_237_, v_s_219_);
lean_inc(v_a_220_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_236_, v___f_237_, v___x_249_, v_a_220_);
switch(lean_obj_tag(v___x_250_))
{
case 0:
{
lean_object* v_index_251_; lean_object* v_size_252_; lean_object* v___x_253_; 
v_index_251_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_index_251_);
lean_dec_ref_known(v___x_250_, 3);
v_size_252_ = lean_ctor_get(v___x_249_, 0);
lean_inc(v_size_252_);
v___x_253_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_249_, v_size_252_, v_index_251_, v_a_220_, v_b_221_);
lean_dec(v_index_251_);
return v___x_253_;
}
case 1:
{
lean_object* v_index_254_; 
v_index_254_ = lean_ctor_get(v___x_250_, 0);
lean_inc(v_index_254_);
lean_dec_ref_known(v___x_250_, 1);
v___y_230_ = v___x_249_;
v_i_231_ = v_index_254_;
goto v___jp_229_;
}
default: 
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(0u);
v___x_256_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_249_, v___x_255_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v_index_257_; 
v_index_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_index_257_);
lean_dec_ref_known(v___x_256_, 1);
v___y_230_ = v___x_249_;
v_i_231_ = v_index_257_;
goto v___jp_229_;
}
else
{
lean_dec(v_b_221_);
lean_dec(v_a_220_);
return v___x_249_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object* v_00_u03b1_288_, lean_object* v_00_u03b2_289_, lean_object* v_s_290_, lean_object* v_a_291_, lean_object* v_b_292_){
_start:
{
lean_object* v___y_294_; lean_object* v_i_295_; lean_object* v___y_301_; lean_object* v_i_302_; lean_object* v___f_307_; lean_object* v___f_308_; lean_object* v___y_310_; lean_object* v___x_329_; 
v___f_307_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_308_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
lean_inc(v_a_291_);
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_307_, v___f_308_, v_s_290_, v_a_291_);
switch(lean_obj_tag(v___x_329_))
{
case 0:
{
lean_object* v_index_330_; lean_object* v_size_331_; lean_object* v___x_332_; 
v_index_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_index_330_);
lean_dec_ref_known(v___x_329_, 3);
v_size_331_ = lean_ctor_get(v_s_290_, 0);
lean_inc(v_size_331_);
v___x_332_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_290_, v_size_331_, v_index_330_, v_a_291_, v_b_292_);
lean_dec(v_index_330_);
return v___x_332_;
}
case 1:
{
lean_object* v_index_333_; lean_object* v_size_334_; lean_object* v_keyArray_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_index_333_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_index_333_);
lean_dec_ref_known(v___x_329_, 1);
v_size_334_ = lean_ctor_get(v_s_290_, 0);
v_keyArray_335_ = lean_ctor_get(v_s_290_, 1);
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_add(v_size_334_, v___x_336_);
v___x_338_ = lean_array_get_size(v_keyArray_335_);
v___x_339_ = lean_nat_dec_lt(v___x_337_, v___x_338_);
if (v___x_339_ == 0)
{
lean_dec(v___x_337_);
lean_dec(v_index_333_);
goto v___jp_319_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_340_ = lean_unsigned_to_nat(4u);
v___x_341_ = lean_nat_mul(v___x_337_, v___x_340_);
v___x_342_ = lean_unsigned_to_nat(3u);
v___x_343_ = lean_nat_mul(v___x_338_, v___x_342_);
v___x_344_ = lean_nat_dec_le(v___x_341_, v___x_343_);
lean_dec(v___x_343_);
lean_dec(v___x_341_);
if (v___x_344_ == 0)
{
lean_dec(v___x_337_);
lean_dec(v_index_333_);
goto v___jp_319_;
}
else
{
lean_object* v___x_345_; 
v___x_345_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_290_, v___x_337_, v_index_333_, v_a_291_, v_b_292_);
lean_dec(v_index_333_);
return v___x_345_;
}
}
}
default: 
{
lean_object* v_size_346_; lean_object* v_keyArray_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; 
v_size_346_ = lean_ctor_get(v_s_290_, 0);
v_keyArray_347_ = lean_ctor_get(v_s_290_, 1);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_size_346_, v___x_348_);
v___x_350_ = lean_array_get_size(v_keyArray_347_);
v___x_351_ = lean_nat_dec_lt(v___x_349_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
lean_dec(v___x_349_);
v___x_352_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_307_, v___f_308_, v_s_290_);
v___y_310_ = v___x_352_;
goto v___jp_309_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_353_ = lean_unsigned_to_nat(4u);
v___x_354_ = lean_nat_mul(v___x_349_, v___x_353_);
lean_dec(v___x_349_);
v___x_355_ = lean_unsigned_to_nat(3u);
v___x_356_ = lean_nat_mul(v___x_350_, v___x_355_);
v___x_357_ = lean_nat_dec_le(v___x_354_, v___x_356_);
lean_dec(v___x_356_);
lean_dec(v___x_354_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_307_, v___f_308_, v_s_290_);
v___y_310_ = v___x_358_;
goto v___jp_309_;
}
else
{
v___y_310_ = v_s_290_;
goto v___jp_309_;
}
}
}
}
v___jp_293_:
{
lean_object* v_size_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_size_296_ = lean_ctor_get(v___y_294_, 0);
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_nat_add(v_size_296_, v___x_297_);
v___x_299_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_294_, v___x_298_, v_i_295_, v_a_291_, v_b_292_);
lean_dec(v_i_295_);
return v___x_299_;
}
v___jp_300_:
{
lean_object* v_size_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_size_303_ = lean_ctor_get(v___y_301_, 0);
v___x_304_ = lean_unsigned_to_nat(1u);
v___x_305_ = lean_nat_add(v_size_303_, v___x_304_);
v___x_306_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_301_, v___x_305_, v_i_302_, v_a_291_, v_b_292_);
lean_dec(v_i_302_);
return v___x_306_;
}
v___jp_309_:
{
lean_object* v___x_311_; 
lean_inc(v_a_291_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_307_, v___f_308_, v___y_310_, v_a_291_);
switch(lean_obj_tag(v___x_311_))
{
case 0:
{
lean_object* v_index_312_; lean_object* v_size_313_; lean_object* v___x_314_; 
v_index_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_index_312_);
lean_dec_ref_known(v___x_311_, 3);
v_size_313_ = lean_ctor_get(v___y_310_, 0);
lean_inc(v_size_313_);
v___x_314_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_310_, v_size_313_, v_index_312_, v_a_291_, v_b_292_);
lean_dec(v_index_312_);
return v___x_314_;
}
case 1:
{
lean_object* v_index_315_; 
v_index_315_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_index_315_);
lean_dec_ref_known(v___x_311_, 1);
v___y_294_ = v___y_310_;
v_i_295_ = v_index_315_;
goto v___jp_293_;
}
default: 
{
lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_310_, v___x_316_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_index_318_; 
v_index_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_index_318_);
lean_dec_ref_known(v___x_317_, 1);
v___y_294_ = v___y_310_;
v_i_295_ = v_index_318_;
goto v___jp_293_;
}
else
{
lean_dec(v_b_292_);
lean_dec(v_a_291_);
return v___y_310_;
}
}
}
}
v___jp_319_:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v___f_307_, v___f_308_, v_s_290_);
lean_inc(v_a_291_);
v___x_321_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v___f_307_, v___f_308_, v___x_320_, v_a_291_);
switch(lean_obj_tag(v___x_321_))
{
case 0:
{
lean_object* v_index_322_; lean_object* v_size_323_; lean_object* v___x_324_; 
v_index_322_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_index_322_);
lean_dec_ref_known(v___x_321_, 3);
v_size_323_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_size_323_);
v___x_324_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_320_, v_size_323_, v_index_322_, v_a_291_, v_b_292_);
lean_dec(v_index_322_);
return v___x_324_;
}
case 1:
{
lean_object* v_index_325_; 
v_index_325_ = lean_ctor_get(v___x_321_, 0);
lean_inc(v_index_325_);
lean_dec_ref_known(v___x_321_, 1);
v___y_301_ = v___x_320_;
v_i_302_ = v_index_325_;
goto v___jp_300_;
}
default: 
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_320_, v___x_326_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_index_328_; 
v_index_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_index_328_);
lean_dec_ref_known(v___x_327_, 1);
v___y_301_ = v___x_320_;
v_i_302_ = v_index_328_;
goto v___jp_300_;
}
else
{
lean_dec(v_b_292_);
lean_dec(v_a_291_);
return v___x_320_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object* v_s_359_, lean_object* v_a_360_){
_start:
{
lean_object* v___f_361_; lean_object* v___f_362_; uint8_t v___x_363_; 
v___f_361_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_362_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_361_, v___f_362_, v_s_359_, v_a_360_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object* v_s_364_, lean_object* v_a_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Lean_PtrMap_contains___redArg(v_s_364_, v_a_365_);
lean_dec_ref(v_s_364_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object* v_00_u03b1_368_, lean_object* v_00_u03b2_369_, lean_object* v_s_370_, lean_object* v_a_371_){
_start:
{
lean_object* v___f_372_; lean_object* v___f_373_; uint8_t v___x_374_; 
v___f_372_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_373_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_372_, v___f_373_, v_s_370_, v_a_371_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object* v_00_u03b1_375_, lean_object* v_00_u03b2_376_, lean_object* v_s_377_, lean_object* v_a_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_Lean_PtrMap_contains(v_00_u03b1_375_, v_00_u03b2_376_, v_s_377_, v_a_378_);
lean_dec_ref(v_s_377_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object* v_s_381_, lean_object* v_a_382_){
_start:
{
lean_object* v___f_383_; lean_object* v___f_384_; lean_object* v___x_385_; 
v___f_383_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_384_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_383_, v___f_384_, v_s_381_, v_a_382_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object* v_s_386_, lean_object* v_a_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_PtrMap_find_x3f___redArg(v_s_386_, v_a_387_);
lean_dec_ref(v_s_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object* v_00_u03b1_389_, lean_object* v_00_u03b2_390_, lean_object* v_s_391_, lean_object* v_a_392_){
_start:
{
lean_object* v___f_393_; lean_object* v___f_394_; lean_object* v___x_395_; 
v___f_393_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_394_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_395_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_393_, v___f_394_, v_s_391_, v_a_392_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object* v_00_u03b1_396_, lean_object* v_00_u03b2_397_, lean_object* v_s_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_PtrMap_find_x3f(v_00_u03b1_396_, v_00_u03b2_397_, v_s_398_, v_a_399_);
lean_dec_ref(v_s_398_);
return v_res_400_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Util_PtrSet(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_PtrSet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Util_PtrSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Util_PtrSet(builtin);
}
#ifdef __cplusplus
}
#endif
