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
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instHashablePtr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashablePtr___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instHashablePtr___redArg___closed__0 = (const lean_object*)&l_Lean_instHashablePtr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___redArg();
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___redArg___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instBEqPtr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqPtr___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instBEqPtr___redArg___closed__0 = (const lean_object*)&l_Lean_instBEqPtr___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___redArg();
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___redArg___boxed(lean_object*);
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
LEAN_EXPORT uint64_t l_Lean_instHashablePtr___redArg___lam__0(lean_object* v_a_1_){
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
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___redArg___lam__0___boxed(lean_object* v_a_6_){
_start:
{
uint64_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l_Lean_instHashablePtr___redArg___lam__0(v_a_6_);
lean_dec(v_a_6_);
v_r_8_ = lean_box_uint64(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___redArg(){
_start:
{
lean_object* v___f_11_; 
v___f_11_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
return v___f_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___redArg___boxed(lean_object* v___dummy_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_instHashablePtr___redArg();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object* v_00_u03b1_14_){
_start:
{
lean_object* v___f_15_; 
v___f_15_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
return v___f_15_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqPtr___redArg___lam__0(lean_object* v_a_16_, lean_object* v_b_17_){
_start:
{
size_t v___x_18_; size_t v___x_19_; uint8_t v___x_20_; 
v___x_18_ = lean_ptr_addr(v_a_16_);
v___x_19_ = lean_ptr_addr(v_b_17_);
v___x_20_ = lean_usize_dec_eq(v___x_18_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___redArg___lam__0___boxed(lean_object* v_a_21_, lean_object* v_b_22_){
_start:
{
uint8_t v_res_23_; lean_object* v_r_24_; 
v_res_23_ = l_Lean_instBEqPtr___redArg___lam__0(v_a_21_, v_b_22_);
lean_dec(v_b_22_);
lean_dec(v_a_21_);
v_r_24_ = lean_box(v_res_23_);
return v_r_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___redArg(){
_start:
{
lean_object* v___f_27_; 
v___f_27_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
return v___f_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instBEqPtr___redArg();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object* v_00_u03b1_30_){
_start:
{
lean_object* v___f_31_; 
v___f_31_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
return v___f_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object* v_capacity_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_unsigned_to_nat(4u);
v___x_35_ = lean_nat_mul(v_capacity_32_, v___x_34_);
v___x_36_ = lean_unsigned_to_nat(3u);
v___x_37_ = lean_nat_div(v___x_35_, v___x_36_);
lean_dec(v___x_35_);
v___x_38_ = l_Nat_nextPowerOfTwo(v___x_37_);
lean_dec(v___x_37_);
v___x_39_ = lean_box(0);
v___x_40_ = lean_mk_array(v___x_38_, v___x_39_);
v___x_41_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_41_, 0, v___x_33_);
lean_ctor_set(v___x_41_, 1, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object* v_capacity_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_mkPtrSet___redArg(v_capacity_42_);
lean_dec(v_capacity_42_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object* v_00_u03b1_44_, lean_object* v_capacity_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_mkPtrSet___redArg(v_capacity_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object* v_00_u03b1_47_, lean_object* v_capacity_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Lean_mkPtrSet(v_00_u03b1_47_, v_capacity_48_);
lean_dec(v_capacity_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object* v_s_50_, lean_object* v_a_51_){
_start:
{
lean_object* v___f_52_; lean_object* v___f_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___f_52_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_53_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_54_ = lean_box(0);
v___x_55_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_52_, v___f_53_, v_s_50_, v_a_51_, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object* v_00_u03b1_56_, lean_object* v_s_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___f_59_; lean_object* v___f_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___f_59_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_60_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_61_ = lean_box(0);
v___x_62_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_59_, v___f_60_, v_s_57_, v_a_58_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object* v_s_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___f_65_; lean_object* v___f_66_; uint8_t v___x_67_; 
v___f_65_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_66_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_67_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_65_, v___f_66_, v_s_63_, v_a_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object* v_s_68_, lean_object* v_a_69_){
_start:
{
uint8_t v_res_70_; lean_object* v_r_71_; 
v_res_70_ = l_Lean_PtrSet_contains___redArg(v_s_68_, v_a_69_);
lean_dec_ref(v_s_68_);
v_r_71_ = lean_box(v_res_70_);
return v_r_71_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object* v_00_u03b1_72_, lean_object* v_s_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___f_75_; lean_object* v___f_76_; uint8_t v___x_77_; 
v___f_75_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_76_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_77_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_75_, v___f_76_, v_s_73_, v_a_74_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object* v_00_u03b1_78_, lean_object* v_s_79_, lean_object* v_a_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lean_PtrSet_contains(v_00_u03b1_78_, v_s_79_, v_a_80_);
lean_dec_ref(v_s_79_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object* v_capacity_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = lean_unsigned_to_nat(4u);
v___x_86_ = lean_nat_mul(v_capacity_83_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(3u);
v___x_88_ = lean_nat_div(v___x_86_, v___x_87_);
lean_dec(v___x_86_);
v___x_89_ = l_Nat_nextPowerOfTwo(v___x_88_);
lean_dec(v___x_88_);
v___x_90_ = lean_box(0);
v___x_91_ = lean_mk_array(v___x_89_, v___x_90_);
v___x_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_84_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object* v_capacity_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_mkPtrMap___redArg(v_capacity_93_);
lean_dec(v_capacity_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_capacity_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_mkPtrMap___redArg(v_capacity_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object* v_00_u03b1_99_, lean_object* v_00_u03b2_100_, lean_object* v_capacity_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_mkPtrMap(v_00_u03b1_99_, v_00_u03b2_100_, v_capacity_101_);
lean_dec(v_capacity_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object* v_s_103_, lean_object* v_a_104_, lean_object* v_b_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v___f_106_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_107_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_106_, v___f_107_, v_s_103_, v_a_104_, v_b_105_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object* v_00_u03b1_109_, lean_object* v_00_u03b2_110_, lean_object* v_s_111_, lean_object* v_a_112_, lean_object* v_b_113_){
_start:
{
lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___x_116_; 
v___f_114_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_115_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_116_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_114_, v___f_115_, v_s_111_, v_a_112_, v_b_113_);
return v___x_116_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object* v_s_117_, lean_object* v_a_118_){
_start:
{
lean_object* v___f_119_; lean_object* v___f_120_; uint8_t v___x_121_; 
v___f_119_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_120_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_121_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_119_, v___f_120_, v_s_117_, v_a_118_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object* v_s_122_, lean_object* v_a_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Lean_PtrMap_contains___redArg(v_s_122_, v_a_123_);
lean_dec_ref(v_s_122_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object* v_00_u03b1_126_, lean_object* v_00_u03b2_127_, lean_object* v_s_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___f_130_; lean_object* v___f_131_; uint8_t v___x_132_; 
v___f_130_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_131_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_132_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_130_, v___f_131_, v_s_128_, v_a_129_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_s_135_, lean_object* v_a_136_){
_start:
{
uint8_t v_res_137_; lean_object* v_r_138_; 
v_res_137_ = l_Lean_PtrMap_contains(v_00_u03b1_133_, v_00_u03b2_134_, v_s_135_, v_a_136_);
lean_dec_ref(v_s_135_);
v_r_138_ = lean_box(v_res_137_);
return v_r_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object* v_s_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___f_141_; lean_object* v___f_142_; lean_object* v___x_143_; 
v___f_141_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_142_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_143_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_141_, v___f_142_, v_s_139_, v_a_140_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object* v_s_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_PtrMap_find_x3f___redArg(v_s_144_, v_a_145_);
lean_dec_ref(v_s_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v_s_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___x_153_; 
v___f_151_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_152_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_153_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_151_, v___f_152_, v_s_149_, v_a_150_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object* v_00_u03b1_154_, lean_object* v_00_u03b2_155_, lean_object* v_s_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_PtrMap_find_x3f(v_00_u03b1_154_, v_00_u03b2_155_, v_s_156_, v_a_157_);
lean_dec_ref(v_s_156_);
return v_res_158_;
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
