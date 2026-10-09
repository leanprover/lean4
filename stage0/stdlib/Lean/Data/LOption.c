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
lean_object* l_Lean_instInhabitedLOption_default___redArg(){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedLOption_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l_Lean_instInhabitedLOption_default___redArg();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default___redArg___boxed(lean_object* v___dummy_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_instInhabitedLOption_default___redArg();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedLOption_default(lean_object* v_00_u03b1_61_){
_start:
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
return v___x_62_;
}
}
lean_object* l_Lean_instInhabitedLOption___redArg(){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(0);
return v___x_64_;
}
}
LEAN_EXPORT void l_Lean_instInhabitedLOption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_65_;
v_res_65_ = l_Lean_instInhabitedLOption___redArg();
stack->m_obj
 = v_res_65_;
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
uint8_t l_Lean_instBEqLOption_beq___redArg(lean_object* v_inst_70_, lean_object* v_x_71_, lean_object* v_x_72_){
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
LEAN_EXPORT void l_Lean_instBEqLOption_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_70_ = stack[0].m_obj;
lean_object* v_x_71_ = stack[1].m_obj;
lean_object* v_x_72_ = stack[2].m_obj;
uint8_t v_res_82_;
v_res_82_ = l_Lean_instBEqLOption_beq___redArg(v_inst_70_, v_x_71_, v_x_72_);
stack->m_num = v_res_82_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___redArg___boxed(lean_object* v_inst_83_, lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
uint8_t v_res_86_; lean_object* v_r_87_; 
v_res_86_ = l_Lean_instBEqLOption_beq___redArg(v_inst_83_, v_x_84_, v_x_85_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
uint8_t l_Lean_instBEqLOption_beq(lean_object* v_00_u03b1_88_, lean_object* v_inst_89_, lean_object* v_x_90_, lean_object* v_x_91_){
_start:
{
uint8_t v___x_92_; 
v___x_92_ = l_Lean_instBEqLOption_beq___redArg(v_inst_89_, v_x_90_, v_x_91_);
return v___x_92_;
}
}
LEAN_EXPORT void l_Lean_instBEqLOption_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_89_ = stack[1].m_obj;
lean_object* v_x_90_ = stack[2].m_obj;
lean_object* v_x_91_ = stack[3].m_obj;
uint8_t v_res_93_;
v_res_93_ = l_Lean_instBEqLOption_beq(lean_box(0), v_inst_89_, v_x_90_, v_x_91_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption_beq___boxed(lean_object* v_00_u03b1_94_, lean_object* v_inst_95_, lean_object* v_x_96_, lean_object* v_x_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Lean_instBEqLOption_beq(v_00_u03b1_94_, v_inst_95_, v_x_96_, v_x_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption___redArg(lean_object* v_inst_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_alloc_closure((void*)(l_Lean_instBEqLOption_beq___boxed), 4, 2);
lean_closure_set(v___x_101_, 0, lean_box(0));
lean_closure_set(v___x_101_, 1, v_inst_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_instBEqLOption(lean_object* v_00_u03b1_102_, lean_object* v_inst_103_){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_closure((void*)(l_Lean_instBEqLOption_beq___boxed), 4, 2);
lean_closure_set(v___x_104_, 0, lean_box(0));
lean_closure_set(v___x_104_, 1, v_inst_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg___lam__0(lean_object* v_inst_109_, lean_object* v_x_110_){
_start:
{
switch(lean_obj_tag(v_x_110_))
{
case 0:
{
lean_object* v___x_111_; 
lean_dec_ref(v_inst_109_);
v___x_111_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__0));
return v___x_111_;
}
case 1:
{
lean_object* v_a_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_a_112_ = lean_ctor_get(v_x_110_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v_x_110_, 1);
v___x_113_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__1));
v___x_114_ = lean_apply_1(v_inst_109_, v_a_112_);
v___x_115_ = lean_string_append(v___x_113_, v___x_114_);
lean_dec_ref(v___x_114_);
v___x_116_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__2));
v___x_117_ = lean_string_append(v___x_115_, v___x_116_);
return v___x_117_;
}
default: 
{
lean_object* v___x_118_; 
lean_dec_ref(v_inst_109_);
v___x_118_ = ((lean_object*)(l_Lean_instToStringLOption___redArg___lam__0___closed__3));
return v___x_118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption___redArg(lean_object* v_inst_119_){
_start:
{
lean_object* v___f_120_; 
v___f_120_ = lean_alloc_closure((void*)(l_Lean_instToStringLOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_120_, 0, v_inst_119_);
return v___f_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToStringLOption(lean_object* v_00_u03b1_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___f_123_; 
v___f_123_ = lean_alloc_closure((void*)(l_Lean_instToStringLOption___redArg___lam__0), 2, 1);
lean_closure_set(v___f_123_, 0, v_inst_122_);
return v___f_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption___redArg(lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 1)
{
lean_object* v_a_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_132_; 
v_a_125_ = lean_ctor_get(v_x_124_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_x_124_);
if (v_isSharedCheck_132_ == 0)
{
v___x_127_ = v_x_124_;
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_a_125_);
lean_dec(v_x_124_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_132_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_130_; 
if (v_isShared_128_ == 0)
{
v___x_130_ = v___x_127_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_a_125_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
else
{
lean_object* v___x_133_; 
lean_dec(v_x_124_);
v___x_133_ = lean_box(0);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_LOption_toOption(lean_object* v_00_u03b1_134_, lean_object* v_x_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_LOption_toOption___redArg(v_x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toLOption___redArg(lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v___x_138_; 
v___x_138_ = lean_box(0);
return v___x_138_;
}
else
{
lean_object* v_val_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_146_; 
v_val_139_ = lean_ctor_get(v_x_137_, 0);
v_isSharedCheck_146_ = !lean_is_exclusive(v_x_137_);
if (v_isSharedCheck_146_ == 0)
{
v___x_141_ = v_x_137_;
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_val_139_);
lean_dec(v_x_137_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_146_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_144_; 
if (v_isShared_142_ == 0)
{
v___x_144_ = v___x_141_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v_val_139_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_toLOption(lean_object* v_00_u03b1_147_, lean_object* v_x_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l_Lean_Option_toLOption___redArg(v_x_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLOptionM___redArg___lam__0(lean_object* v_toPure_150_, lean_object* v_b_151_){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = l_Lean_Option_toLOption___redArg(v_b_151_);
v___x_153_ = lean_apply_2(v_toPure_150_, lean_box(0), v___x_152_);
return v___x_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLOptionM___redArg(lean_object* v_inst_154_, lean_object* v_x_155_){
_start:
{
lean_object* v_toApplicative_156_; lean_object* v_toBind_157_; lean_object* v_toPure_158_; lean_object* v___f_159_; lean_object* v___x_160_; 
v_toApplicative_156_ = lean_ctor_get(v_inst_154_, 0);
lean_inc_ref(v_toApplicative_156_);
v_toBind_157_ = lean_ctor_get(v_inst_154_, 1);
lean_inc(v_toBind_157_);
lean_dec_ref(v_inst_154_);
v_toPure_158_ = lean_ctor_get(v_toApplicative_156_, 1);
lean_inc(v_toPure_158_);
lean_dec_ref(v_toApplicative_156_);
v___f_159_ = lean_alloc_closure((void*)(l_Lean_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_159_, 0, v_toPure_158_);
v___x_160_ = lean_apply_4(v_toBind_157_, lean_box(0), lean_box(0), v_x_155_, v___f_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_toLOptionM(lean_object* v_00_u03b1_161_, lean_object* v_m_162_, lean_object* v_inst_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_toApplicative_165_; lean_object* v_toBind_166_; lean_object* v_toPure_167_; lean_object* v___f_168_; lean_object* v___x_169_; 
v_toApplicative_165_ = lean_ctor_get(v_inst_163_, 0);
lean_inc_ref(v_toApplicative_165_);
v_toBind_166_ = lean_ctor_get(v_inst_163_, 1);
lean_inc(v_toBind_166_);
lean_dec_ref(v_inst_163_);
v_toPure_167_ = lean_ctor_get(v_toApplicative_165_, 1);
lean_inc(v_toPure_167_);
lean_dec_ref(v_toApplicative_165_);
v___f_168_ = lean_alloc_closure((void*)(l_Lean_toLOptionM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_168_, 0, v_toPure_167_);
v___x_169_ = lean_apply_4(v_toBind_166_, lean_box(0), lean_box(0), v_x_164_, v___f_168_);
return v___x_169_;
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
