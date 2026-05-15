// Lean compiler output
// Module: Lean.Data.LOption
// Imports: public import Init.Data.String.Basic
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
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_none_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_some_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_some_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_undef_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_undef_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption(lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqLOption_beq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instBEqLOption_beq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqLOption(lean_object*, lean_object*);
static const lean_string_object l_Lean_instToStringLOption___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_instToStringLOption___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instToStringLOption___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToStringLOption___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "(some "};
static const lean_object* l_Lean_instToStringLOption___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instToStringLOption___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToStringLOption___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_instToStringLOption___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_instToStringLOption___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_instToStringLOption___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "undef"};
static const lean_object* l_Lean_instToStringLOption___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_instToStringLOption___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToStringLOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_toOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_toOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_toLOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Option_toLOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toLOptionM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toLOptionM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_toLOptionM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___redArg___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_LOption_ctorIdx___redArg(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx(lean_object* v_00_u03b1_7_, lean_object* v_x_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_LOption_ctorIdx___redArg(v_x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___boxed(lean_object* v_00_u03b1_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Lean_LOption_ctorIdx(v_00_u03b1_10_, v_x_11_);
lean_dec(v_x_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim___redArg(lean_object* v_t_13_, lean_object* v_k_14_){
_start:
{
if (lean_obj_tag(v_t_13_) == 1)
{
lean_object* v_a_15_; lean_object* v___x_16_; 
v_a_15_ = lean_ctor_get(v_t_13_, 0);
lean_inc(v_a_15_);
lean_dec_ref(v_t_13_);
v___x_16_ = lean_apply_1(v_k_14_, v_a_15_);
return v___x_16_;
}
else
{
lean_dec(v_t_13_);
return v_k_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim(lean_object* v_00_u03b1_17_, lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Lean_LOption_ctorElim___redArg(v_t_20_, v_k_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim___boxed(lean_object* v_00_u03b1_24_, lean_object* v_motive_25_, lean_object* v_ctorIdx_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_k_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_LOption_ctorElim(v_00_u03b1_24_, v_motive_25_, v_ctorIdx_26_, v_t_27_, v_h_28_, v_k_29_);
lean_dec(v_ctorIdx_26_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_none_elim___redArg(lean_object* v_t_31_, lean_object* v_none_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_LOption_ctorElim___redArg(v_t_31_, v_none_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_none_elim(lean_object* v_00_u03b1_34_, lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_none_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_LOption_ctorElim___redArg(v_t_36_, v_none_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_some_elim___redArg(lean_object* v_t_40_, lean_object* v_some_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_LOption_ctorElim___redArg(v_t_40_, v_some_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_some_elim(lean_object* v_00_u03b1_43_, lean_object* v_motive_44_, lean_object* v_t_45_, lean_object* v_h_46_, lean_object* v_some_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_LOption_ctorElim___redArg(v_t_45_, v_some_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_undef_elim___redArg(lean_object* v_t_49_, lean_object* v_undef_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_LOption_ctorElim___redArg(v_t_49_, v_undef_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_undef_elim(lean_object* v_00_u03b1_52_, lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_undef_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_LOption_ctorElim___redArg(v_t_54_, v_undef_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default(lean_object* v_00_u03b1_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(0);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption(lean_object* v_a_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_box(0);
return v___x_61_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLOption_beq___redArg(lean_object* v_inst_62_, lean_object* v_x_63_, lean_object* v_x_64_){
_start:
{
switch(lean_obj_tag(v_x_63_))
{
case 0:
{
lean_dec_ref(v_inst_62_);
if (lean_obj_tag(v_x_64_) == 0)
{
uint8_t v___x_65_; 
v___x_65_ = 1;
return v___x_65_;
}
else
{
uint8_t v___x_66_; 
lean_dec(v_x_64_);
v___x_66_ = 0;
return v___x_66_;
}
}
case 1:
{
if (lean_obj_tag(v_x_64_) == 1)
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_a_67_ = lean_ctor_get(v_x_63_, 0);
lean_inc(v_a_67_);
lean_dec_ref(v_x_63_);
v_a_68_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_a_68_);
lean_dec_ref(v_x_64_);
v___x_69_ = lean_apply_2(v_inst_62_, v_a_67_, v_a_68_);
v___x_70_ = lean_unbox(v___x_69_);
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
lean_dec_ref(v_x_63_);
lean_dec(v_x_64_);
lean_dec_ref(v_inst_62_);
v___x_71_ = 0;
return v___x_71_;
}
}
default: 
{
lean_dec_ref(v_inst_62_);
if (lean_obj_tag(v_x_64_) == 2)
{
uint8_t v___x_72_; 
v___x_72_ = 1;
return v___x_72_;
}
else
{
uint8_t v___x_73_; 
lean_dec(v_x_64_);
v___x_73_ = 0;
return v___x_73_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___redArg___boxed(lean_object* v_inst_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
uint8_t v_res_77_; lean_object* v_r_78_; 
v_res_77_ = l_Lean_instBEqLOption_beq___redArg(v_inst_74_, v_x_75_, v_x_76_);
v_r_78_ = lean_box(v_res_77_);
return v_r_78_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLOption_beq(lean_object* v_00_u03b1_79_, lean_object* v_inst_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v___x_83_; 
v___x_83_ = l_Lean_instBEqLOption_beq___redArg(v_inst_80_, v_x_81_, v_x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___boxed(lean_object* v_00_u03b1_84_, lean_object* v_inst_85_, lean_object* v_x_86_, lean_object* v_x_87_){
_start:
{
uint8_t v_res_88_; lean_object* v_r_89_; 
v_res_88_ = l_Lean_instBEqLOption_beq(v_00_u03b1_84_, v_inst_85_, v_x_86_, v_x_87_);
v_r_89_ = lean_box(v_res_88_);
return v_r_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption___redArg(lean_object* v_inst_90_){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = lean_alloc_closure((void*)(l_Lean_instBEqLOption_beq___boxed), 4, 2);
lean_closure_set(v___x_91_, 0, lean_box(0));
lean_closure_set(v___x_91_, 1, v_inst_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption(lean_object* v_00_u03b1_92_, lean_object* v_inst_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_alloc_closure((void*)(l_Lean_instBEqLOption_beq___boxed), 4, 2);
lean_closure_set(v___x_94_, 0, lean_box(0));
lean_closure_set(v___x_94_, 1, v_inst_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg___lam__0(lean_object* v_inst_99_, lean_object* v_x_100_){
_start:
{
switch(lean_obj_tag(v_x_100_))
{
case 0:
{
lean_object* v___x_101_; 
lean_dec_ref(v_inst_99_);
v___x_101_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__0));
return v___x_101_;
}
case 1:
{
lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_a_102_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_a_102_);
lean_dec_ref(v_x_100_);
v___x_103_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__1));
v___x_104_ = lean_apply_1(v_inst_99_, v_a_102_);
v___x_105_ = lean_string_append(v___x_103_, v___x_104_);
lean_dec_ref(v___x_104_);
v___x_106_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__2));
v___x_107_ = lean_string_append(v___x_105_, v___x_106_);
return v___x_107_;
}
default: 
{
lean_object* v___x_108_; 
lean_dec_ref(v_inst_99_);
v___x_108_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__3));
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg(lean_object* v_inst_109_){
_start:
{
lean_object* v___f_110_; 
v___f_110_ = lean_alloc_closure((void*)(l_Lean_instToStringLOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_110_, 0, v_inst_109_);
return v___f_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption(lean_object* v_00_u03b1_111_, lean_object* v_inst_112_){
_start:
{
lean_object* v___f_113_; 
v___f_113_ = lean_alloc_closure((void*)(l_Lean_instToStringLOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_113_, 0, v_inst_112_);
return v___f_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption___redArg(lean_object* v_x_114_){
_start:
{
if (lean_obj_tag(v_x_114_) == 1)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
v_a_115_ = lean_ctor_get(v_x_114_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_114_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v_x_114_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v_x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_object* v___x_123_; 
lean_dec(v_x_114_);
v___x_123_ = lean_box(0);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption(lean_object* v_00_u03b1_124_, lean_object* v_x_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_LOption_toOption___redArg(v_x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Option_toLOption___redArg(lean_object* v_x_127_){
_start:
{
if (lean_obj_tag(v_x_127_) == 0)
{
lean_object* v___x_128_; 
v___x_128_ = lean_box(0);
return v___x_128_;
}
else
{
lean_object* v_val_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_136_; 
v_val_129_ = lean_ctor_get(v_x_127_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v_x_127_);
if (v_isSharedCheck_136_ == 0)
{
v___x_131_ = v_x_127_;
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_val_129_);
lean_dec(v_x_127_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_136_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_134_; 
if (v_isShared_132_ == 0)
{
v___x_134_ = v___x_131_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_val_129_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_toLOption(lean_object* v_00_u03b1_137_, lean_object* v_x_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_Option_toLOption___redArg(v_x_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_toLOptionM___redArg___lam__0(lean_object* v_toPure_140_, lean_object* v_b_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = l_Option_toLOption___redArg(v_b_141_);
v___x_143_ = lean_apply_2(v_toPure_140_, lean_box(0), v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_toLOptionM___redArg(lean_object* v_inst_144_, lean_object* v_x_145_){
_start:
{
lean_object* v_toApplicative_146_; lean_object* v_toBind_147_; lean_object* v_toPure_148_; lean_object* v___f_149_; lean_object* v___x_150_; 
v_toApplicative_146_ = lean_ctor_get(v_inst_144_, 0);
lean_inc_ref(v_toApplicative_146_);
v_toBind_147_ = lean_ctor_get(v_inst_144_, 1);
lean_inc(v_toBind_147_);
lean_dec_ref(v_inst_144_);
v_toPure_148_ = lean_ctor_get(v_toApplicative_146_, 1);
lean_inc(v_toPure_148_);
lean_dec_ref(v_toApplicative_146_);
v___f_149_ = lean_alloc_closure((void*)(l_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_149_, 0, v_toPure_148_);
v___x_150_ = lean_apply_4(v_toBind_147_, lean_box(0), lean_box(0), v_x_145_, v___f_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_toLOptionM(lean_object* v_00_u03b1_151_, lean_object* v_m_152_, lean_object* v_inst_153_, lean_object* v_x_154_){
_start:
{
lean_object* v_toApplicative_155_; lean_object* v_toBind_156_; lean_object* v_toPure_157_; lean_object* v___f_158_; lean_object* v___x_159_; 
v_toApplicative_155_ = lean_ctor_get(v_inst_153_, 0);
lean_inc_ref(v_toApplicative_155_);
v_toBind_156_ = lean_ctor_get(v_inst_153_, 1);
lean_inc(v_toBind_156_);
lean_dec_ref(v_inst_153_);
v_toPure_157_ = lean_ctor_get(v_toApplicative_155_, 1);
lean_inc(v_toPure_157_);
lean_dec_ref(v_toApplicative_155_);
v___f_158_ = lean_alloc_closure((void*)(l_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_158_, 0, v_toPure_157_);
v___x_159_ = lean_apply_4(v_toBind_156_, lean_box(0), lean_box(0), v_x_154_, v___f_158_);
return v___x_159_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_LOption(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_LOption(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_LOption(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_LOption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_LOption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_LOption(builtin);
}
#ifdef __cplusplus
}
#endif
