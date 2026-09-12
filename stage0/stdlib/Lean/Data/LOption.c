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
lean_dec_ref_known(v_t_13_, 1);
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
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default___redArg(){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_box(0);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default___redArg___boxed(lean_object* v___dummy_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_instInhabitedLOption_default___redArg();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default(lean_object* v_00_u03b1_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption___redArg(){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_box(0);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption___redArg___boxed(lean_object* v___dummy_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_instInhabitedLOption___redArg();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption(lean_object* v_a_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(0);
return v___x_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLOption_beq___redArg(lean_object* v_inst_70_, lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
switch(lean_obj_tag(v_x_71_))
{
case 0:
{
lean_dec_ref(v_inst_70_);
if (lean_obj_tag(v_x_72_) == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 1;
return v___x_73_;
}
else
{
uint8_t v___x_74_; 
lean_dec(v_x_72_);
v___x_74_ = 0;
return v___x_74_;
}
}
case 1:
{
if (lean_obj_tag(v_x_72_) == 1)
{
lean_object* v_a_75_; lean_object* v_a_76_; lean_object* v___x_77_; uint8_t v___x_78_; 
v_a_75_ = lean_ctor_get(v_x_71_, 0);
lean_inc(v_a_75_);
lean_dec_ref_known(v_x_71_, 1);
v_a_76_ = lean_ctor_get(v_x_72_, 0);
lean_inc(v_a_76_);
lean_dec_ref_known(v_x_72_, 1);
v___x_77_ = lean_apply_2(v_inst_70_, v_a_75_, v_a_76_);
v___x_78_ = lean_unbox(v___x_77_);
return v___x_78_;
}
else
{
uint8_t v___x_79_; 
lean_dec_ref_known(v_x_71_, 1);
lean_dec(v_x_72_);
lean_dec_ref(v_inst_70_);
v___x_79_ = 0;
return v___x_79_;
}
}
default: 
{
lean_dec_ref(v_inst_70_);
if (lean_obj_tag(v_x_72_) == 2)
{
uint8_t v___x_80_; 
v___x_80_ = 1;
return v___x_80_;
}
else
{
uint8_t v___x_81_; 
lean_dec(v_x_72_);
v___x_81_ = 0;
return v___x_81_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___redArg___boxed(lean_object* v_inst_82_, lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
uint8_t v_res_85_; lean_object* v_r_86_; 
v_res_85_ = l_Lean_instBEqLOption_beq___redArg(v_inst_82_, v_x_83_, v_x_84_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT uint8_t l_Lean_instBEqLOption_beq(lean_object* v_00_u03b1_87_, lean_object* v_inst_88_, lean_object* v_x_89_, lean_object* v_x_90_){
_start:
{
uint8_t v___x_91_; 
v___x_91_ = l_Lean_instBEqLOption_beq___redArg(v_inst_88_, v_x_89_, v_x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___boxed(lean_object* v_00_u03b1_92_, lean_object* v_inst_93_, lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_Lean_instBEqLOption_beq(v_00_u03b1_92_, v_inst_93_, v_x_94_, v_x_95_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption___redArg(lean_object* v_inst_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_alloc_closure((void*)(l_Lean_instBEqLOption_beq___boxed), 4, 2);
lean_closure_set(v___x_99_, 0, lean_box(0));
lean_closure_set(v___x_99_, 1, v_inst_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption(lean_object* v_00_u03b1_100_, lean_object* v_inst_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_alloc_closure((void*)(l_Lean_instBEqLOption_beq___boxed), 4, 2);
lean_closure_set(v___x_102_, 0, lean_box(0));
lean_closure_set(v___x_102_, 1, v_inst_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg___lam__0(lean_object* v_inst_107_, lean_object* v_x_108_){
_start:
{
switch(lean_obj_tag(v_x_108_))
{
case 0:
{
lean_object* v___x_109_; 
lean_dec_ref(v_inst_107_);
v___x_109_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__0));
return v___x_109_;
}
case 1:
{
lean_object* v_a_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_a_110_ = lean_ctor_get(v_x_108_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v_x_108_, 1);
v___x_111_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__1));
v___x_112_ = lean_apply_1(v_inst_107_, v_a_110_);
v___x_113_ = lean_string_append(v___x_111_, v___x_112_);
lean_dec_ref(v___x_112_);
v___x_114_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__2));
v___x_115_ = lean_string_append(v___x_113_, v___x_114_);
return v___x_115_;
}
default: 
{
lean_object* v___x_116_; 
lean_dec_ref(v_inst_107_);
v___x_116_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__3));
return v___x_116_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg(lean_object* v_inst_117_){
_start:
{
lean_object* v___f_118_; 
v___f_118_ = lean_alloc_closure((void*)(l_Lean_instToStringLOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_118_, 0, v_inst_117_);
return v___f_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption(lean_object* v_00_u03b1_119_, lean_object* v_inst_120_){
_start:
{
lean_object* v___f_121_; 
v___f_121_ = lean_alloc_closure((void*)(l_Lean_instToStringLOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_121_, 0, v_inst_120_);
return v___f_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption___redArg(lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_122_) == 1)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_130_; 
v_a_123_ = lean_ctor_get(v_x_122_, 0);
v_isSharedCheck_130_ = !lean_is_exclusive(v_x_122_);
if (v_isSharedCheck_130_ == 0)
{
v___x_125_ = v_x_122_;
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v_x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_130_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_128_; 
if (v_isShared_126_ == 0)
{
v___x_128_ = v___x_125_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_129_; 
v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_129_, 0, v_a_123_);
v___x_128_ = v_reuseFailAlloc_129_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
return v___x_128_;
}
}
}
else
{
lean_object* v___x_131_; 
lean_dec(v_x_122_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption(lean_object* v_00_u03b1_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_LOption_toOption___redArg(v_x_133_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toLOption___redArg(lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_object* v___x_136_; 
v___x_136_ = lean_box(0);
return v___x_136_;
}
else
{
lean_object* v_val_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
v_val_137_ = lean_ctor_get(v_x_135_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v_x_135_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_val_137_);
lean_dec(v_x_135_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_val_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toLOption(lean_object* v_00_u03b1_145_, lean_object* v_x_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Lean_Option_toLOption___redArg(v_x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLOptionM___redArg___lam__0(lean_object* v_toPure_148_, lean_object* v_b_149_){
_start:
{
lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_150_ = l_Lean_Option_toLOption___redArg(v_b_149_);
v___x_151_ = lean_apply_2(v_toPure_148_, lean_box(0), v___x_150_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLOptionM___redArg(lean_object* v_inst_152_, lean_object* v_x_153_){
_start:
{
lean_object* v_toApplicative_154_; lean_object* v_toBind_155_; lean_object* v_toPure_156_; lean_object* v___f_157_; lean_object* v___x_158_; 
v_toApplicative_154_ = lean_ctor_get(v_inst_152_, 0);
lean_inc_ref(v_toApplicative_154_);
v_toBind_155_ = lean_ctor_get(v_inst_152_, 1);
lean_inc(v_toBind_155_);
lean_dec_ref(v_inst_152_);
v_toPure_156_ = lean_ctor_get(v_toApplicative_154_, 1);
lean_inc(v_toPure_156_);
lean_dec_ref(v_toApplicative_154_);
v___f_157_ = lean_alloc_closure((void*)(l_Lean_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_157_, 0, v_toPure_156_);
v___x_158_ = lean_apply_4(v_toBind_155_, lean_box(0), lean_box(0), v_x_153_, v___f_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLOptionM(lean_object* v_00_u03b1_159_, lean_object* v_m_160_, lean_object* v_inst_161_, lean_object* v_x_162_){
_start:
{
lean_object* v_toApplicative_163_; lean_object* v_toBind_164_; lean_object* v_toPure_165_; lean_object* v___f_166_; lean_object* v___x_167_; 
v_toApplicative_163_ = lean_ctor_get(v_inst_161_, 0);
lean_inc_ref(v_toApplicative_163_);
v_toBind_164_ = lean_ctor_get(v_inst_161_, 1);
lean_inc(v_toBind_164_);
lean_dec_ref(v_inst_161_);
v_toPure_165_ = lean_ctor_get(v_toApplicative_163_, 1);
lean_inc(v_toPure_165_);
lean_dec_ref(v_toApplicative_163_);
v___f_166_ = lean_alloc_closure((void*)(l_Lean_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_166_, 0, v_toPure_165_);
v___x_167_ = lean_apply_4(v_toBind_164_, lean_box(0), lean_box(0), v_x_162_, v___f_166_);
return v___x_167_;
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
