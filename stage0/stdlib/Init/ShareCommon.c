// Lean compiler output
// Module: Init.ShareCommon
// Imports: public import Init.Data.UInt.Basic public import Init.Control.State
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
LEAN_EXPORT uint8_t l_ShareCommon_Object_ptrEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_Object_ptrEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_ShareCommon_Object_ptrHash(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_Object_ptrHash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StateFactoryPointed;
uint8_t lean_sharecommon_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_Object_eq___boxed(lean_object*, lean_object*);
uint64_t lean_sharecommon_hash(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_Object_hash___boxed(lean_object*);
LEAN_EXPORT uint64_t l_ShareCommon_StateFactory_mkImpl___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl___lam__0___boxed(lean_object*);
static const lean_closure_object l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommon_Object_ptrEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0 = (const lean_object*)&l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0_value;
static const lean_closure_object l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommon_Object_eq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1 = (const lean_object*)&l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1_value;
static const lean_closure_object l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommon_Object_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2 = (const lean_object*)&l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_ShareCommon_StateFactory_mkImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommon_StateFactory_mkImpl___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommon_StateFactory_mkImpl___closed__0 = (const lean_object*)&l_ShareCommon_StateFactory_mkImpl___closed__0_value;
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_get(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_get___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_mkStateImpl(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_instInhabitedState(lean_object*);
lean_object* lean_state_sharecommon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_State_shareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withShareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_withShareCommon(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_shareCommonM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_shareCommonM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_ShareCommonT_run___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ShareCommonT_run___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_ShareCommonT_run___redArg___closed__0 = (const lean_object*)&l_ShareCommonT_run___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonT_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonM_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ShareCommonM_run(lean_object*, lean_object*, lean_object*);
lean_object* lean_sharecommon_quick(lean_object*);
LEAN_EXPORT lean_object* l_ShareCommon_shareCommon_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_ShareCommon_Object_ptrEq(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
size_t v___x_3_; size_t v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_ptr_addr(v_a_1_);
v___x_4_ = lean_ptr_addr(v_b_2_);
v___x_5_ = lean_usize_dec_eq(v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_Object_ptrEq___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_ShareCommon_Object_ptrEq(v_a_6_, v_b_7_);
lean_dec(v_b_7_);
lean_dec(v_a_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint64_t l_ShareCommon_Object_ptrHash(lean_object* v_a_10_){
_start:
{
size_t v___x_11_; uint64_t v___x_12_; 
v___x_11_ = lean_ptr_addr(v_a_10_);
v___x_12_ = lean_usize_to_uint64(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_Object_ptrHash___boxed(lean_object* v_a_13_){
_start:
{
uint64_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_ShareCommon_Object_ptrHash(v_a_13_);
lean_dec(v_a_13_);
v_r_15_ = lean_box_uint64(v_res_14_);
return v_r_15_;
}
}
static lean_object* _init_l_ShareCommon_StateFactoryPointed(void){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_Object_eq___boxed(lean_object* v_a_19_, lean_object* v_b_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = lean_sharecommon_eq(v_a_19_, v_b_20_);
lean_dec(v_b_20_);
lean_dec(v_a_19_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_Object_hash___boxed(lean_object* v_a_24_){
_start:
{
uint64_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = lean_sharecommon_hash(v_a_24_);
lean_dec(v_a_24_);
v_r_26_ = lean_box_uint64(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT uint64_t l_ShareCommon_StateFactory_mkImpl___lam__0(lean_object* v___y_27_){
_start:
{
size_t v___x_28_; uint64_t v___x_29_; 
v___x_28_ = lean_ptr_addr(v___y_27_);
v___x_29_ = lean_usize_to_uint64(v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl___lam__0___boxed(lean_object* v___y_30_){
_start:
{
uint64_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_ShareCommon_StateFactory_mkImpl___lam__0(v___y_30_);
lean_dec(v___y_30_);
v_r_32_ = lean_box_uint64(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl___lam__2(lean_object* v_mkMap_36_, lean_object* v___f_37_, lean_object* v_mkSet_38_, lean_object* v_x_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_40_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0));
v___x_41_ = lean_unsigned_to_nat(1024u);
v___x_42_ = lean_apply_5(v_mkMap_36_, lean_box(0), lean_box(0), v___x_40_, v___f_37_, v___x_41_);
v___x_43_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1));
v___x_44_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2));
v___x_45_ = lean_apply_4(v_mkSet_38_, lean_box(0), v___x_43_, v___x_44_, v___x_41_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_42_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_mkImpl(lean_object* v_x_48_){
_start:
{
lean_object* v_mkMap_49_; lean_object* v_mapFind_x3f_50_; lean_object* v_mapInsert_51_; lean_object* v_mkSet_52_; lean_object* v_setFind_x3f_53_; lean_object* v_setInsert_54_; lean_object* v___f_55_; lean_object* v___f_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; 
v_mkMap_49_ = lean_ctor_get(v_x_48_, 0);
lean_inc(v_mkMap_49_);
v_mapFind_x3f_50_ = lean_ctor_get(v_x_48_, 1);
lean_inc_ref(v_mapFind_x3f_50_);
v_mapInsert_51_ = lean_ctor_get(v_x_48_, 2);
lean_inc(v_mapInsert_51_);
v_mkSet_52_ = lean_ctor_get(v_x_48_, 3);
lean_inc(v_mkSet_52_);
v_setFind_x3f_53_ = lean_ctor_get(v_x_48_, 4);
lean_inc_ref(v_setFind_x3f_53_);
v_setInsert_54_ = lean_ctor_get(v_x_48_, 5);
lean_inc(v_setInsert_54_);
lean_dec_ref(v_x_48_);
v___f_55_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___closed__0));
v___f_56_ = lean_alloc_closure((void*)(l_ShareCommon_StateFactory_mkImpl___lam__2), 4, 3);
lean_closure_set(v___f_56_, 0, v_mkMap_49_);
lean_closure_set(v___f_56_, 1, v___f_55_);
lean_closure_set(v___f_56_, 2, v_mkSet_52_);
v___x_57_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__0));
v___x_58_ = lean_apply_4(v_mapFind_x3f_50_, lean_box(0), lean_box(0), v___x_57_, v___f_55_);
v___x_59_ = lean_apply_4(v_mapInsert_51_, lean_box(0), lean_box(0), v___x_57_, v___f_55_);
v___x_60_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__1));
v___x_61_ = ((lean_object*)(l_ShareCommon_StateFactory_mkImpl___lam__2___closed__2));
v___x_62_ = lean_apply_3(v_setFind_x3f_53_, lean_box(0), v___x_60_, v___x_61_);
v___x_63_ = lean_apply_3(v_setInsert_54_, lean_box(0), v___x_60_, v___x_61_);
v___x_64_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_64_, 0, v___f_56_);
lean_ctor_set(v___x_64_, 1, v___x_58_);
lean_ctor_set(v___x_64_, 2, v___x_59_);
lean_ctor_set(v___x_64_, 3, v___x_62_);
lean_ctor_set(v___x_64_, 4, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_get(lean_object* v_a_65_){
_start:
{
lean_inc(v_a_65_);
return v_a_65_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StateFactory_get___boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_ShareCommon_StateFactory_get(v_a_66_);
lean_dec(v_a_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed(lean_object* v_00_u03c3_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___boxed(lean_object* v_00_u03c3_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_ShareCommon_StatePointed(v_00_u03c3_70_);
lean_dec(v_00_u03c3_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_mkStateImpl(lean_object* v_00_u03c3_72_){
_start:
{
lean_object* v_mkState_73_; lean_object* v___x_74_; lean_object* v___x_75_; 
v_mkState_73_ = lean_ctor_get(v_00_u03c3_72_, 0);
lean_inc_ref(v_mkState_73_);
lean_dec(v_00_u03c3_72_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_apply_1(v_mkState_73_, v___x_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_instInhabitedState(lean_object* v_00_u03c3_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_ShareCommon_mkStateImpl(v_00_u03c3_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_State_shareCommon___boxed(lean_object* v_00_u03b1_82_, lean_object* v_00_u03c3_83_, lean_object* v_s_84_, lean_object* v_a_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = lean_state_sharecommon(v_00_u03c3_83_, v_s_84_, v_a_85_);
lean_dec(v_00_u03c3_83_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_withShareCommon___redArg(lean_object* v_self_87_, lean_object* v_a_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lean_apply_2(v_self_87_, lean_box(0), v_a_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_withShareCommon(lean_object* v_m_90_, lean_object* v_self_91_, lean_object* v_00_u03b1_92_, lean_object* v_a_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_apply_2(v_self_91_, lean_box(0), v_a_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_shareCommonM___redArg(lean_object* v_inst_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_apply_2(v_inst_95_, lean_box(0), v_a_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_shareCommonM(lean_object* v_m_98_, lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; 
v___x_102_ = lean_apply_2(v_inst_100_, lean_box(0), v_a_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg(lean_object* v_00_u03c3_103_, lean_object* v_inst_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_toApplicative_107_; lean_object* v_toPure_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_toApplicative_107_ = lean_ctor_get(v_inst_104_, 0);
lean_inc_ref(v_toApplicative_107_);
lean_dec_ref(v_inst_104_);
v_toPure_108_ = lean_ctor_get(v_toApplicative_107_, 1);
lean_inc(v_toPure_108_);
lean_dec_ref(v_toApplicative_107_);
v___x_109_ = lean_state_sharecommon(v_00_u03c3_103_, v_a_106_, v_a_105_);
v___x_110_ = lean_apply_2(v_toPure_108_, lean_box(0), v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg___boxed(lean_object* v_00_u03c3_111_, lean_object* v_inst_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_111_, v_inst_112_, v_a_113_, v_a_114_);
lean_dec(v_00_u03c3_111_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon(lean_object* v_m_116_, lean_object* v_00_u03b1_117_, lean_object* v_00_u03c3_118_, lean_object* v_inst_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_118_, v_inst_119_, v_a_120_, v_a_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___boxed(lean_object* v_m_123_, lean_object* v_00_u03b1_124_, lean_object* v_00_u03c3_125_, lean_object* v_inst_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_ShareCommonT_withShareCommon(v_m_123_, v_00_u03b1_124_, v_00_u03c3_125_, v_inst_126_, v_a_127_, v_a_128_);
lean_dec(v_00_u03c3_125_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_00_u03c3_130_, lean_object* v_inst_131_, lean_object* v_00_u03b1_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_130_, v_inst_131_, v___y_133_, v___y_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed(lean_object* v_00_u03c3_136_, lean_object* v_inst_137_, lean_object* v_00_u03b1_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_ShareCommonT_monadShareCommon___redArg___lam__0(v_00_u03c3_136_, v_inst_137_, v_00_u03b1_138_, v___y_139_, v___y_140_);
lean_dec(v_00_u03c3_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg(lean_object* v_00_u03c3_142_, lean_object* v_inst_143_){
_start:
{
lean_object* v___f_144_; 
v___f_144_ = lean_alloc_closure((void*)(l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_144_, 0, v_00_u03c3_142_);
lean_closure_set(v___f_144_, 1, v_inst_143_);
return v___f_144_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon(lean_object* v_m_145_, lean_object* v_00_u03c3_146_, lean_object* v_inst_147_){
_start:
{
lean_object* v___f_148_; 
v___f_148_ = lean_alloc_closure((void*)(l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_148_, 0, v_00_u03c3_146_);
lean_closure_set(v___f_148_, 1, v_inst_147_);
return v___f_148_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0(lean_object* v_x_149_){
_start:
{
lean_object* v_fst_150_; 
v_fst_150_ = lean_ctor_get(v_x_149_, 0);
lean_inc(v_fst_150_);
return v_fst_150_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0___boxed(lean_object* v_x_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_ShareCommonT_run___redArg___lam__0(v_x_151_);
lean_dec_ref(v_x_151_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg(lean_object* v_00_u03c3_154_, lean_object* v_inst_155_, lean_object* v_x_156_){
_start:
{
lean_object* v_toApplicative_157_; lean_object* v_toFunctor_158_; lean_object* v_map_159_; lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v_toApplicative_157_ = lean_ctor_get(v_inst_155_, 0);
lean_inc_ref(v_toApplicative_157_);
lean_dec_ref(v_inst_155_);
v_toFunctor_158_ = lean_ctor_get(v_toApplicative_157_, 0);
lean_inc_ref(v_toFunctor_158_);
lean_dec_ref(v_toApplicative_157_);
v_map_159_ = lean_ctor_get(v_toFunctor_158_, 0);
lean_inc(v_map_159_);
lean_dec_ref(v_toFunctor_158_);
v___f_160_ = ((lean_object*)(l_ShareCommonT_run___redArg___closed__0));
v___x_161_ = l_ShareCommon_mkStateImpl(v_00_u03c3_154_);
v___x_162_ = lean_apply_1(v_x_156_, v___x_161_);
v___x_163_ = lean_apply_4(v_map_159_, lean_box(0), lean_box(0), v___f_160_, v___x_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run(lean_object* v_m_164_, lean_object* v_00_u03c3_165_, lean_object* v_00_u03b1_166_, lean_object* v_inst_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_toApplicative_169_; lean_object* v_toFunctor_170_; lean_object* v_map_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v_toApplicative_169_ = lean_ctor_get(v_inst_167_, 0);
lean_inc_ref(v_toApplicative_169_);
lean_dec_ref(v_inst_167_);
v_toFunctor_170_ = lean_ctor_get(v_toApplicative_169_, 0);
lean_inc_ref(v_toFunctor_170_);
lean_dec_ref(v_toApplicative_169_);
v_map_171_ = lean_ctor_get(v_toFunctor_170_, 0);
lean_inc(v_map_171_);
lean_dec_ref(v_toFunctor_170_);
v___f_172_ = ((lean_object*)(l_ShareCommonT_run___redArg___closed__0));
v___x_173_ = l_ShareCommon_mkStateImpl(v_00_u03c3_165_);
v___x_174_ = lean_apply_1(v_x_168_, v___x_173_);
v___x_175_ = lean_apply_4(v_map_171_, lean_box(0), lean_box(0), v___f_172_, v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonM_run___redArg(lean_object* v_00_u03c3_176_, lean_object* v_x_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v_fst_180_; 
v___x_178_ = l_ShareCommon_mkStateImpl(v_00_u03c3_176_);
v___x_179_ = lean_apply_1(v_x_177_, v___x_178_);
v_fst_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_fst_180_);
lean_dec_ref(v___x_179_);
return v_fst_180_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonM_run(lean_object* v_00_u03c3_181_, lean_object* v_00_u03b1_182_, lean_object* v_x_183_){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v_fst_186_; 
v___x_184_ = l_ShareCommon_mkStateImpl(v_00_u03c3_181_);
v___x_185_ = lean_apply_1(v_x_183_, v___x_184_);
v_fst_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_fst_186_);
lean_dec_ref(v___x_185_);
return v_fst_186_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_shareCommon_x27___boxed(lean_object* v_00_u03b1_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = lean_sharecommon_quick(v_a_190_);
lean_dec(v_a_190_);
return v_res_191_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ShareCommon_StateFactoryPointed = _init_l_ShareCommon_StateFactoryPointed();
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Control_State(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_State(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_ShareCommon(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_ShareCommon(builtin);
}
#ifdef __cplusplus
}
#endif
