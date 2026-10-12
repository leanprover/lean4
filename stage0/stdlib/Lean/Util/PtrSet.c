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
uint64_t l_Lean_instHashablePtr___redArg___lam__0(lean_object* v_a_1_){
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
LEAN_EXPORT void l_Lean_instHashablePtr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1_ = stack[0].m_obj;
uint64_t v_res_6_;
v_res_6_ = l_Lean_instHashablePtr___redArg___lam__0(v_a_1_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___redArg___lam__0___boxed(lean_object* v_a_7_){
_start:
{
uint64_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_Lean_instHashablePtr___redArg___lam__0(v_a_7_);
lean_dec(v_a_7_);
v_r_9_ = lean_box_uint64(v_res_8_);
return v_r_9_;
}
}
lean_object* l_Lean_instHashablePtr___redArg(){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
return v___f_12_;
}
}
LEAN_EXPORT void l_Lean_instHashablePtr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_13_;
v_res_13_ = l_Lean_instHashablePtr___redArg();
stack->m_obj
 = v_res_13_;
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr___redArg___boxed(lean_object* v___dummy_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Lean_instHashablePtr___redArg();
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_instHashablePtr(lean_object* v_00_u03b1_16_){
_start:
{
lean_object* v___f_17_; 
v___f_17_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
return v___f_17_;
}
}
uint8_t l_Lean_instBEqPtr___redArg___lam__0(lean_object* v_a_18_, lean_object* v_b_19_){
_start:
{
size_t v___x_20_; size_t v___x_21_; uint8_t v___x_22_; 
v___x_20_ = lean_ptr_addr(v_a_18_);
v___x_21_ = lean_ptr_addr(v_b_19_);
v___x_22_ = lean_usize_dec_eq(v___x_20_, v___x_21_);
return v___x_22_;
}
}
LEAN_EXPORT void l_Lean_instBEqPtr___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_18_ = stack[0].m_obj;
lean_object* v_b_19_ = stack[1].m_obj;
uint8_t v_res_23_;
v_res_23_ = l_Lean_instBEqPtr___redArg___lam__0(v_a_18_, v_b_19_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___redArg___lam__0___boxed(lean_object* v_a_24_, lean_object* v_b_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = l_Lean_instBEqPtr___redArg___lam__0(v_a_24_, v_b_25_);
lean_dec(v_b_25_);
lean_dec(v_a_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
lean_object* l_Lean_instBEqPtr___redArg(){
_start:
{
lean_object* v___f_30_; 
v___f_30_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
return v___f_30_;
}
}
LEAN_EXPORT void l_Lean_instBEqPtr___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_31_;
v_res_31_ = l_Lean_instBEqPtr___redArg();
stack->m_obj
 = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr___redArg___boxed(lean_object* v___dummy_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_instBEqPtr___redArg();
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqPtr(lean_object* v_00_u03b1_34_){
_start:
{
lean_object* v___f_35_; 
v___f_35_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
return v___f_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg(lean_object* v_capacity_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_unsigned_to_nat(4u);
v___x_39_ = lean_nat_mul(v_capacity_36_, v___x_38_);
v___x_40_ = lean_unsigned_to_nat(3u);
v___x_41_ = lean_nat_div(v___x_39_, v___x_40_);
lean_dec(v___x_39_);
v___x_42_ = l_Nat_nextPowerOfTwo(v___x_41_);
lean_dec(v___x_41_);
v___x_43_ = lean_box(0);
v___x_44_ = lean_mk_array(v___x_42_, v___x_43_);
v___x_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_37_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___redArg___boxed(lean_object* v_capacity_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_mkPtrSet___redArg(v_capacity_46_);
lean_dec(v_capacity_46_);
return v_res_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet(lean_object* v_00_u03b1_48_, lean_object* v_capacity_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_mkPtrSet___redArg(v_capacity_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrSet___boxed(lean_object* v_00_u03b1_51_, lean_object* v_capacity_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_mkPtrSet(v_00_u03b1_51_, v_capacity_52_);
lean_dec(v_capacity_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert___redArg(lean_object* v_s_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___f_56_; lean_object* v___f_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___f_56_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_57_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_58_ = lean_box(0);
v___x_59_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_56_, v___f_57_, v_s_54_, v_a_55_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_insert(lean_object* v_00_u03b1_60_, lean_object* v_s_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___f_63_; lean_object* v___f_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___f_63_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_64_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_65_ = lean_box(0);
v___x_66_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v___f_63_, v___f_64_, v_s_61_, v_a_62_, v___x_65_);
return v___x_66_;
}
}
uint8_t l_Lean_PtrSet_contains___redArg(lean_object* v_s_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___f_69_; lean_object* v___f_70_; uint8_t v___x_71_; 
v___f_69_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_70_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_71_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_69_, v___f_70_, v_s_67_, v_a_68_);
return v___x_71_;
}
}
LEAN_EXPORT void l_Lean_PtrSet_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_67_ = stack[0].m_obj;
lean_object* v_a_68_ = stack[1].m_obj;
uint8_t v_res_72_;
v_res_72_ = l_Lean_PtrSet_contains___redArg(v_s_67_, v_a_68_);
stack->m_num = v_res_72_;
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___redArg___boxed(lean_object* v_s_73_, lean_object* v_a_74_){
_start:
{
uint8_t v_res_75_; lean_object* v_r_76_; 
v_res_75_ = l_Lean_PtrSet_contains___redArg(v_s_73_, v_a_74_);
lean_dec_ref(v_s_73_);
v_r_76_ = lean_box(v_res_75_);
return v_r_76_;
}
}
uint8_t l_Lean_PtrSet_contains(lean_object* v_00_u03b1_77_, lean_object* v_s_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___f_80_; lean_object* v___f_81_; uint8_t v___x_82_; 
v___f_80_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_81_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_82_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_80_, v___f_81_, v_s_78_, v_a_79_);
return v___x_82_;
}
}
LEAN_EXPORT void l_Lean_PtrSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_78_ = stack[1].m_obj;
lean_object* v_a_79_ = stack[2].m_obj;
uint8_t v_res_83_;
v_res_83_ = l_Lean_PtrSet_contains(lean_box(0), v_s_78_, v_a_79_);
stack->m_num = v_res_83_;
}
LEAN_EXPORT lean_object* l_Lean_PtrSet_contains___boxed(lean_object* v_00_u03b1_84_, lean_object* v_s_85_, lean_object* v_a_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_PtrSet_contains(v_00_u03b1_84_, v_s_85_, v_a_86_);
lean_dec_ref(v_s_85_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg(lean_object* v_capacity_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_90_ = lean_unsigned_to_nat(0u);
v___x_91_ = lean_unsigned_to_nat(4u);
v___x_92_ = lean_nat_mul(v_capacity_89_, v___x_91_);
v___x_93_ = lean_unsigned_to_nat(3u);
v___x_94_ = lean_nat_div(v___x_92_, v___x_93_);
lean_dec(v___x_92_);
v___x_95_ = l_Nat_nextPowerOfTwo(v___x_94_);
lean_dec(v___x_94_);
v___x_96_ = lean_box(0);
v___x_97_ = lean_mk_array(v___x_95_, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_90_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___redArg___boxed(lean_object* v_capacity_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_mkPtrMap___redArg(v_capacity_99_);
lean_dec(v_capacity_99_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap(lean_object* v_00_u03b1_101_, lean_object* v_00_u03b2_102_, lean_object* v_capacity_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_mkPtrMap___redArg(v_capacity_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPtrMap___boxed(lean_object* v_00_u03b1_105_, lean_object* v_00_u03b2_106_, lean_object* v_capacity_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_mkPtrMap(v_00_u03b1_105_, v_00_u03b2_106_, v_capacity_107_);
lean_dec(v_capacity_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert___redArg(lean_object* v_s_109_, lean_object* v_a_110_, lean_object* v_b_111_){
_start:
{
lean_object* v___f_112_; lean_object* v___f_113_; lean_object* v___x_114_; 
v___f_112_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_113_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_114_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_112_, v___f_113_, v_s_109_, v_a_110_, v_b_111_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_insert(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_s_117_, lean_object* v_a_118_, lean_object* v_b_119_){
_start:
{
lean_object* v___f_120_; lean_object* v___f_121_; lean_object* v___x_122_; 
v___f_120_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_121_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_122_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_120_, v___f_121_, v_s_117_, v_a_118_, v_b_119_);
return v___x_122_;
}
}
uint8_t l_Lean_PtrMap_contains___redArg(lean_object* v_s_123_, lean_object* v_a_124_){
_start:
{
lean_object* v___f_125_; lean_object* v___f_126_; uint8_t v___x_127_; 
v___f_125_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_126_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_125_, v___f_126_, v_s_123_, v_a_124_);
return v___x_127_;
}
}
LEAN_EXPORT void l_Lean_PtrMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_123_ = stack[0].m_obj;
lean_object* v_a_124_ = stack[1].m_obj;
uint8_t v_res_128_;
v_res_128_ = l_Lean_PtrMap_contains___redArg(v_s_123_, v_a_124_);
stack->m_num = v_res_128_;
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___redArg___boxed(lean_object* v_s_129_, lean_object* v_a_130_){
_start:
{
uint8_t v_res_131_; lean_object* v_r_132_; 
v_res_131_ = l_Lean_PtrMap_contains___redArg(v_s_129_, v_a_130_);
lean_dec_ref(v_s_129_);
v_r_132_ = lean_box(v_res_131_);
return v_r_132_;
}
}
uint8_t l_Lean_PtrMap_contains(lean_object* v_00_u03b1_133_, lean_object* v_00_u03b2_134_, lean_object* v_s_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___f_137_; lean_object* v___f_138_; uint8_t v___x_139_; 
v___f_137_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_138_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_139_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v___f_137_, v___f_138_, v_s_135_, v_a_136_);
return v___x_139_;
}
}
LEAN_EXPORT void l_Lean_PtrMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_135_ = stack[2].m_obj;
lean_object* v_a_136_ = stack[3].m_obj;
uint8_t v_res_140_;
v_res_140_ = l_Lean_PtrMap_contains(lean_box(0), lean_box(0), v_s_135_, v_a_136_);
stack->m_num = v_res_140_;
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_contains___boxed(lean_object* v_00_u03b1_141_, lean_object* v_00_u03b2_142_, lean_object* v_s_143_, lean_object* v_a_144_){
_start:
{
uint8_t v_res_145_; lean_object* v_r_146_; 
v_res_145_ = l_Lean_PtrMap_contains(v_00_u03b1_141_, v_00_u03b2_142_, v_s_143_, v_a_144_);
lean_dec_ref(v_s_143_);
v_r_146_ = lean_box(v_res_145_);
return v_r_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg(lean_object* v_s_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___f_149_; lean_object* v___f_150_; lean_object* v___x_151_; 
v___f_149_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_150_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_149_, v___f_150_, v_s_147_, v_a_148_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___redArg___boxed(lean_object* v_s_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_PtrMap_find_x3f___redArg(v_s_152_, v_a_153_);
lean_dec_ref(v_s_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_s_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___f_159_; lean_object* v___f_160_; lean_object* v___x_161_; 
v___f_159_ = ((lean_object*)(l_Lean_instBEqPtr___redArg___closed__0));
v___f_160_ = ((lean_object*)(l_Lean_instHashablePtr___redArg___closed__0));
v___x_161_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_159_, v___f_160_, v_s_157_, v_a_158_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PtrMap_find_x3f___boxed(lean_object* v_00_u03b1_162_, lean_object* v_00_u03b2_163_, lean_object* v_s_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_PtrMap_find_x3f(v_00_u03b1_162_, v_00_u03b2_163_, v_s_164_, v_a_165_);
lean_dec_ref(v_s_164_);
return v_res_166_;
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
