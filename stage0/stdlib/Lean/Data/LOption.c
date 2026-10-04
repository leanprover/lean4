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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_none_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_none_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_some_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_some_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_undef_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_undef_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_toLOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_toLOption(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toLOptionM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toLOptionM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_toLOptionM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___impl___redArg(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___impl___redArg___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_LOption_ctorIdx___impl___redArg(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___impl(lean_object* v_00_u03b1_5_, lean_object* v_x_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_tag_nat(v_x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorIdx___impl___boxed(lean_object* v_00_u03b1_8_, lean_object* v_x_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_Lean_LOption_ctorIdx___impl(v_00_u03b1_8_, v_x_9_);
lean_dec(v_x_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim___redArg(lean_object* v_t_11_, lean_object* v_k_12_){
_start:
{
if (lean_obj_tag(v_t_11_) == 1)
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v_t_11_, 0);
lean_inc(v_a_13_);
lean_dec_ref_known(v_t_11_, 1);
v___x_14_ = lean_apply_1(v_k_12_, v_a_13_);
return v___x_14_;
}
else
{
lean_dec(v_t_11_);
return v_k_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim(lean_object* v_00_u03b1_15_, lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = l_Lean_LOption_ctorElim___redArg(v_t_18_, v_k_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_ctorElim___boxed(lean_object* v_00_u03b1_22_, lean_object* v_motive_23_, lean_object* v_ctorIdx_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_k_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_LOption_ctorElim(v_00_u03b1_22_, v_motive_23_, v_ctorIdx_24_, v_t_25_, v_h_26_, v_k_27_);
lean_dec(v_ctorIdx_24_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_none_elim___redArg(lean_object* v_t_29_, lean_object* v_none_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_LOption_ctorElim___redArg(v_t_29_, v_none_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_none_elim(lean_object* v_00_u03b1_32_, lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_none_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_LOption_ctorElim___redArg(v_t_34_, v_none_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_some_elim___redArg(lean_object* v_t_38_, lean_object* v_some_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_LOption_ctorElim___redArg(v_t_38_, v_some_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_some_elim(lean_object* v_00_u03b1_41_, lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_some_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Lean_LOption_ctorElim___redArg(v_t_43_, v_some_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_undef_elim___redArg(lean_object* v_t_47_, lean_object* v_undef_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_LOption_ctorElim___redArg(v_t_47_, v_undef_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_undef_elim(lean_object* v_00_u03b1_50_, lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_undef_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = l_Lean_LOption_ctorElim___redArg(v_t_52_, v_undef_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default___redArg(){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default___redArg___boxed(lean_object* v___dummy_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_instInhabitedLOption_default___redArg();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default(lean_object* v_00_u03b1_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = lean_box(0);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption___redArg(){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption___redArg___boxed(lean_object* v___dummy_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_instInhabitedLOption___redArg();
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption(lean_object* v_a_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_box(0);
return v___x_67_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLOption_beq___redArg(lean_object* v_inst_68_, lean_object* v_x_69_, lean_object* v_x_70_){
_start:
{
switch(lean_obj_tag(v_x_69_))
{
case 0:
{
lean_dec_ref(v_inst_68_);
if (lean_obj_tag(v_x_70_) == 0)
{
uint8_t v___x_71_; 
v___x_71_ = 1;
return v___x_71_;
}
else
{
uint8_t v___x_72_; 
lean_dec(v_x_70_);
v___x_72_ = 0;
return v___x_72_;
}
}
case 1:
{
if (lean_obj_tag(v_x_70_) == 1)
{
lean_object* v_a_73_; lean_object* v_a_74_; lean_object* v___x_75_; uint8_t v___x_76_; 
v_a_73_ = lean_ctor_get(v_x_69_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v_x_69_, 1);
v_a_74_ = lean_ctor_get(v_x_70_, 0);
lean_inc(v_a_74_);
lean_dec_ref_known(v_x_70_, 1);
v___x_75_ = lean_apply_2(v_inst_68_, v_a_73_, v_a_74_);
v___x_76_ = lean_unbox(v___x_75_);
return v___x_76_;
}
else
{
uint8_t v___x_77_; 
lean_dec_ref_known(v_x_69_, 1);
lean_dec(v_x_70_);
lean_dec_ref(v_inst_68_);
v___x_77_ = 0;
return v___x_77_;
}
}
default: 
{
lean_dec_ref(v_inst_68_);
if (lean_obj_tag(v_x_70_) == 2)
{
uint8_t v___x_78_; 
v___x_78_ = 1;
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
lean_dec(v_x_70_);
v___x_79_ = 0;
return v___x_79_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___redArg___boxed(lean_object* v_inst_80_, lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Lean_instBEqLOption_beq___redArg(v_inst_80_, v_x_81_, v_x_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLOption_beq(lean_object* v_00_u03b1_85_, lean_object* v_inst_86_, lean_object* v_x_87_, lean_object* v_x_88_){
_start:
{
uint8_t v___x_89_; 
v___x_89_ = l_Lean_instBEqLOption_beq___redArg(v_inst_86_, v_x_87_, v_x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___boxed(lean_object* v_00_u03b1_90_, lean_object* v_inst_91_, lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Lean_instBEqLOption_beq(v_00_u03b1_90_, v_inst_91_, v_x_92_, v_x_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption___redArg(lean_object* v_inst_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_closure((void*)(l_Lean_instBEqLOption_beq___boxed), 4, 2);
lean_closure_set(v___x_97_, 0, lean_box(0));
lean_closure_set(v___x_97_, 1, v_inst_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption(lean_object* v_00_u03b1_98_, lean_object* v_inst_99_){
_start:
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_closure((void*)(l_Lean_instBEqLOption_beq___boxed), 4, 2);
lean_closure_set(v___x_100_, 0, lean_box(0));
lean_closure_set(v___x_100_, 1, v_inst_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg___lam__0(lean_object* v_inst_105_, lean_object* v_x_106_){
_start:
{
switch(lean_obj_tag(v_x_106_))
{
case 0:
{
lean_object* v___x_107_; 
lean_dec_ref(v_inst_105_);
v___x_107_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__0));
return v___x_107_;
}
case 1:
{
lean_object* v_a_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_a_108_ = lean_ctor_get(v_x_106_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v_x_106_, 1);
v___x_109_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__1));
v___x_110_ = lean_apply_1(v_inst_105_, v_a_108_);
v___x_111_ = lean_string_append(v___x_109_, v___x_110_);
lean_dec_ref(v___x_110_);
v___x_112_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__2));
v___x_113_ = lean_string_append(v___x_111_, v___x_112_);
return v___x_113_;
}
default: 
{
lean_object* v___x_114_; 
lean_dec_ref(v_inst_105_);
v___x_114_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__3));
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg(lean_object* v_inst_115_){
_start:
{
lean_object* v___f_116_; 
v___f_116_ = lean_alloc_closure((void*)(l_Lean_instToStringLOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_116_, 0, v_inst_115_);
return v___f_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption(lean_object* v_00_u03b1_117_, lean_object* v_inst_118_){
_start:
{
lean_object* v___f_119_; 
v___f_119_ = lean_alloc_closure((void*)(l_Lean_instToStringLOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_119_, 0, v_inst_118_);
return v___f_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption___redArg(lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 1)
{
lean_object* v_a_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_128_; 
v_a_121_ = lean_ctor_get(v_x_120_, 0);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_128_ == 0)
{
v___x_123_ = v_x_120_;
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_a_121_);
lean_dec(v_x_120_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_128_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_126_; 
if (v_isShared_124_ == 0)
{
v___x_126_ = v___x_123_;
goto v_reusejp_125_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_a_121_);
v___x_126_ = v_reuseFailAlloc_127_;
goto v_reusejp_125_;
}
v_reusejp_125_:
{
return v___x_126_;
}
}
}
else
{
lean_object* v___x_129_; 
lean_dec(v_x_120_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption(lean_object* v_00_u03b1_130_, lean_object* v_x_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_Lean_LOption_toOption___redArg(v_x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toLOption___redArg(lean_object* v_x_133_){
_start:
{
if (lean_obj_tag(v_x_133_) == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_box(0);
return v___x_134_;
}
else
{
lean_object* v_val_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_142_; 
v_val_135_ = lean_ctor_get(v_x_133_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_133_);
if (v_isSharedCheck_142_ == 0)
{
v___x_137_ = v_x_133_;
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_val_135_);
lean_dec(v_x_133_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_142_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_140_; 
if (v_isShared_138_ == 0)
{
v___x_140_ = v___x_137_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_val_135_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toLOption(lean_object* v_00_u03b1_143_, lean_object* v_x_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Option_toLOption___redArg(v_x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLOptionM___redArg___lam__0(lean_object* v_toPure_146_, lean_object* v_b_147_){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = l_Lean_Option_toLOption___redArg(v_b_147_);
v___x_149_ = lean_apply_2(v_toPure_146_, lean_box(0), v___x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLOptionM___redArg(lean_object* v_inst_150_, lean_object* v_x_151_){
_start:
{
lean_object* v_toApplicative_152_; lean_object* v_toBind_153_; lean_object* v_toPure_154_; lean_object* v___f_155_; lean_object* v___x_156_; 
v_toApplicative_152_ = lean_ctor_get(v_inst_150_, 0);
lean_inc_ref(v_toApplicative_152_);
v_toBind_153_ = lean_ctor_get(v_inst_150_, 1);
lean_inc(v_toBind_153_);
lean_dec_ref(v_inst_150_);
v_toPure_154_ = lean_ctor_get(v_toApplicative_152_, 1);
lean_inc(v_toPure_154_);
lean_dec_ref(v_toApplicative_152_);
v___f_155_ = lean_alloc_closure((void*)(l_Lean_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_155_, 0, v_toPure_154_);
v___x_156_ = lean_apply_4(v_toBind_153_, lean_box(0), lean_box(0), v_x_151_, v___f_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLOptionM(lean_object* v_00_u03b1_157_, lean_object* v_m_158_, lean_object* v_inst_159_, lean_object* v_x_160_){
_start:
{
lean_object* v_toApplicative_161_; lean_object* v_toBind_162_; lean_object* v_toPure_163_; lean_object* v___f_164_; lean_object* v___x_165_; 
v_toApplicative_161_ = lean_ctor_get(v_inst_159_, 0);
lean_inc_ref(v_toApplicative_161_);
v_toBind_162_ = lean_ctor_get(v_inst_159_, 1);
lean_inc(v_toBind_162_);
lean_dec_ref(v_inst_159_);
v_toPure_163_ = lean_ctor_get(v_toApplicative_161_, 1);
lean_inc(v_toPure_163_);
lean_dec_ref(v_toApplicative_161_);
v___f_164_ = lean_alloc_closure((void*)(l_Lean_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_164_, 0, v_toPure_163_);
v___x_165_ = lean_apply_4(v_toBind_162_, lean_box(0), lean_box(0), v_x_160_, v___f_164_);
return v___x_165_;
}
}
lean_object* runtime_initialize_Init_Data_String_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_LOption(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
