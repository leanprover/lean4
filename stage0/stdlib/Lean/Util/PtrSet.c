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
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_25_ = lean_unsigned_to_nat(0u);
v___x_26_ = lean_unsigned_to_nat(4u);
v___x_27_ = lean_nat_mul(v_capacity_24_, v___x_26_);
v___x_28_ = lean_unsigned_to_nat(3u);
v___x_29_ = lean_nat_div(v___x_27_, v___x_28_);
lean_dec(v___x_27_);
v___x_30_ = l_Nat_nextPowerOfTwo(v___x_29_);
lean_dec(v___x_29_);
v___x_31_ = lean_box(0);
v___x_32_ = lean_mk_array(v___x_30_, v___x_31_);
v___x_33_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_25_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object* v_capacity_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_mkPtrSet___redArg(v_capacity_34_);
lean_dec(v_capacity_34_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object* v_00_u03b1_36_, lean_object* v_capacity_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_mkPtrSet___redArg(v_capacity_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object* v_00_u03b1_39_, lean_object* v_capacity_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_mkPtrSet(v_00_u03b1_39_, v_capacity_40_);
lean_dec(v_capacity_40_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object* v_s_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___f_44_; lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___f_44_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_45_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_46_ = lean_box(0);
v___x_47_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_44_, v___f_45_, v_s_42_, v_a_43_, v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object* v_00_u03b1_48_, lean_object* v_s_49_, lean_object* v_a_50_){
_start:
{
lean_object* v___f_51_; lean_object* v___f_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___f_51_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_52_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_53_ = lean_box(0);
v___x_54_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_51_, v___f_52_, v_s_49_, v_a_50_, v___x_53_);
return v___x_54_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains___redArg(lean_object* v_s_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___f_57_; lean_object* v___f_58_; uint8_t v___x_59_; 
v___f_57_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_58_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_59_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_57_, v___f_58_, v_s_55_, v_a_56_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object* v_s_60_, lean_object* v_a_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_Lean_PtrSet_contains___redArg(v_s_60_, v_a_61_);
lean_dec_ref(v_s_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrSet_contains(lean_object* v_00_u03b1_64_, lean_object* v_s_65_, lean_object* v_a_66_){
_start:
{
lean_object* v___f_67_; lean_object* v___f_68_; uint8_t v___x_69_; 
v___f_67_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_68_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_69_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_67_, v___f_68_, v_s_65_, v_a_66_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object* v_00_u03b1_70_, lean_object* v_s_71_, lean_object* v_a_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = l_Lean_PtrSet_contains(v_00_u03b1_70_, v_s_71_, v_a_72_);
lean_dec_ref(v_s_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object* v_capacity_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_unsigned_to_nat(4u);
v___x_78_ = lean_nat_mul(v_capacity_75_, v___x_77_);
v___x_79_ = lean_unsigned_to_nat(3u);
v___x_80_ = lean_nat_div(v___x_78_, v___x_79_);
lean_dec(v___x_78_);
v___x_81_ = l_Nat_nextPowerOfTwo(v___x_80_);
lean_dec(v___x_80_);
v___x_82_ = lean_box(0);
v___x_83_ = lean_mk_array(v___x_81_, v___x_82_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_76_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object* v_capacity_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_mkPtrMap___redArg(v_capacity_85_);
lean_dec(v_capacity_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object* v_00_u03b1_87_, lean_object* v_00_u03b2_88_, lean_object* v_capacity_89_){
_start:
{
lean_object* v___x_90_; 
v___x_90_ = l_Lean_mkPtrMap___redArg(v_capacity_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object* v_00_u03b1_91_, lean_object* v_00_u03b2_92_, lean_object* v_capacity_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_mkPtrMap(v_00_u03b1_91_, v_00_u03b2_92_, v_capacity_93_);
lean_dec(v_capacity_93_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object* v_s_95_, lean_object* v_a_96_, lean_object* v_b_97_){
_start:
{
lean_object* v___f_98_; lean_object* v___f_99_; lean_object* v___x_100_; 
v___f_98_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_99_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_100_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_98_, v___f_99_, v_s_95_, v_a_96_, v_b_97_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_s_103_, lean_object* v_a_104_, lean_object* v_b_105_){
_start:
{
lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; 
v___f_106_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_107_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_108_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_106_, v___f_107_, v_s_103_, v_a_104_, v_b_105_);
return v___x_108_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains___redArg(lean_object* v_s_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___f_111_; lean_object* v___f_112_; uint8_t v___x_113_; 
v___f_111_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_112_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_113_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_111_, v___f_112_, v_s_109_, v_a_110_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object* v_s_114_, lean_object* v_a_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = l_Lean_PtrMap_contains___redArg(v_s_114_, v_a_115_);
lean_dec_ref(v_s_114_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT uint8_t l_Lean_PtrMap_contains(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_s_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___f_122_; lean_object* v___f_123_; uint8_t v___x_124_; 
v___f_122_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_123_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_124_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_122_, v___f_123_, v_s_120_, v_a_121_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object* v_00_u03b1_125_, lean_object* v_00_u03b2_126_, lean_object* v_s_127_, lean_object* v_a_128_){
_start:
{
uint8_t v_res_129_; lean_object* v_r_130_; 
v_res_129_ = l_Lean_PtrMap_contains(v_00_u03b1_125_, v_00_u03b2_126_, v_s_127_, v_a_128_);
lean_dec_ref(v_s_127_);
v_r_130_ = lean_box(v_res_129_);
return v_r_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object* v_s_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___f_133_; lean_object* v___f_134_; lean_object* v___x_135_; 
v___f_133_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_134_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_135_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_133_, v___f_134_, v_s_131_, v_a_132_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object* v_s_136_, lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l_Lean_PtrMap_find_x3f___redArg(v_s_136_, v_a_137_);
lean_dec_ref(v_s_136_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object* v_00_u03b1_139_, lean_object* v_00_u03b2_140_, lean_object* v_s_141_, lean_object* v_a_142_){
_start:
{
lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_145_; 
v___f_143_ = ((lean_object*)(l_Lean_instBEqPtr___closed__0));
v___f_144_ = ((lean_object*)(l_Lean_instHashablePtr___closed__0));
v___x_145_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_143_, v___f_144_, v_s_141_, v_a_142_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object* v_00_u03b1_146_, lean_object* v_00_u03b2_147_, lean_object* v_s_148_, lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l_Lean_PtrMap_find_x3f(v_00_u03b1_146_, v_00_u03b2_147_, v_s_148_, v_a_149_);
lean_dec_ref(v_s_148_);
return v_res_150_;
}
}
lean_object* runtime_initialize_Init_Data_Hashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Util_PtrSet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
