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
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___redArg();
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___redArg(){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_box(0);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___redArg___boxed(lean_object* v___dummy_70_){
_start:
{
lean_object* v_res_71_; 
v_res_71_ = l_ShareCommon_StatePointed___redArg();
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed(lean_object* v_00_u03c3_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lean_box(0);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_StatePointed___boxed(lean_object* v_00_u03c3_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_ShareCommon_StatePointed(v_00_u03c3_74_);
lean_dec(v_00_u03c3_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_mkStateImpl(lean_object* v_00_u03c3_76_){
_start:
{
lean_object* v_mkState_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_mkState_77_ = lean_ctor_get(v_00_u03c3_76_, 0);
lean_inc_ref(v_mkState_77_);
lean_dec(v_00_u03c3_76_);
v___x_78_ = lean_box(0);
v___x_79_ = lean_apply_1(v_mkState_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_instInhabitedState(lean_object* v_00_u03c3_80_){
_start:
{
lean_object* v___x_81_; 
v___x_81_ = l_ShareCommon_mkStateImpl(v_00_u03c3_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_State_shareCommon___boxed(lean_object* v_00_u03b1_86_, lean_object* v_00_u03c3_87_, lean_object* v_s_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = lean_state_sharecommon(v_00_u03c3_87_, v_s_88_, v_a_89_);
lean_dec(v_00_u03c3_87_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_withShareCommon___redArg(lean_object* v_self_91_, lean_object* v_a_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = lean_apply_2(v_self_91_, lean_box(0), v_a_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_withShareCommon(lean_object* v_m_94_, lean_object* v_self_95_, lean_object* v_00_u03b1_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_apply_2(v_self_95_, lean_box(0), v_a_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_shareCommonM___redArg(lean_object* v_inst_99_, lean_object* v_a_100_){
_start:
{
lean_object* v___x_101_; 
v___x_101_ = lean_apply_2(v_inst_99_, lean_box(0), v_a_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_shareCommonM(lean_object* v_m_102_, lean_object* v_00_u03b1_103_, lean_object* v_inst_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_apply_2(v_inst_104_, lean_box(0), v_a_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg(lean_object* v_00_u03c3_107_, lean_object* v_inst_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v_toApplicative_111_; lean_object* v_toPure_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_toApplicative_111_ = lean_ctor_get(v_inst_108_, 0);
lean_inc_ref(v_toApplicative_111_);
lean_dec_ref(v_inst_108_);
v_toPure_112_ = lean_ctor_get(v_toApplicative_111_, 1);
lean_inc(v_toPure_112_);
lean_dec_ref(v_toApplicative_111_);
v___x_113_ = lean_state_sharecommon(v_00_u03c3_107_, v_a_110_, v_a_109_);
v___x_114_ = lean_apply_2(v_toPure_112_, lean_box(0), v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___redArg___boxed(lean_object* v_00_u03c3_115_, lean_object* v_inst_116_, lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_115_, v_inst_116_, v_a_117_, v_a_118_);
lean_dec(v_00_u03c3_115_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon(lean_object* v_m_120_, lean_object* v_00_u03b1_121_, lean_object* v_00_u03c3_122_, lean_object* v_inst_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_122_, v_inst_123_, v_a_124_, v_a_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_withShareCommon___boxed(lean_object* v_m_127_, lean_object* v_00_u03b1_128_, lean_object* v_00_u03c3_129_, lean_object* v_inst_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_ShareCommonT_withShareCommon(v_m_127_, v_00_u03b1_128_, v_00_u03c3_129_, v_inst_130_, v_a_131_, v_a_132_);
lean_dec(v_00_u03c3_129_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0(lean_object* v_00_u03c3_134_, lean_object* v_inst_135_, lean_object* v_00_u03b1_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = l_ShareCommonT_withShareCommon___redArg(v_00_u03c3_134_, v_inst_135_, v___y_137_, v___y_138_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed(lean_object* v_00_u03c3_140_, lean_object* v_inst_141_, lean_object* v_00_u03b1_142_, lean_object* v___y_143_, lean_object* v___y_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_ShareCommonT_monadShareCommon___redArg___lam__0(v_00_u03c3_140_, v_inst_141_, v_00_u03b1_142_, v___y_143_, v___y_144_);
lean_dec(v_00_u03c3_140_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon___redArg(lean_object* v_00_u03c3_146_, lean_object* v_inst_147_){
_start:
{
lean_object* v___f_148_; 
v___f_148_ = lean_alloc_closure((void*)(l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_148_, 0, v_00_u03c3_146_);
lean_closure_set(v___f_148_, 1, v_inst_147_);
return v___f_148_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_monadShareCommon(lean_object* v_m_149_, lean_object* v_00_u03c3_150_, lean_object* v_inst_151_){
_start:
{
lean_object* v___f_152_; 
v___f_152_ = lean_alloc_closure((void*)(l_ShareCommonT_monadShareCommon___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_152_, 0, v_00_u03c3_150_);
lean_closure_set(v___f_152_, 1, v_inst_151_);
return v___f_152_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0(lean_object* v_x_153_){
_start:
{
lean_object* v_fst_154_; 
v_fst_154_ = lean_ctor_get(v_x_153_, 0);
lean_inc(v_fst_154_);
return v_fst_154_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg___lam__0___boxed(lean_object* v_x_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_ShareCommonT_run___redArg___lam__0(v_x_155_);
lean_dec_ref(v_x_155_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run___redArg(lean_object* v_00_u03c3_158_, lean_object* v_inst_159_, lean_object* v_x_160_){
_start:
{
lean_object* v_toApplicative_161_; lean_object* v_toFunctor_162_; lean_object* v_map_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_toApplicative_161_ = lean_ctor_get(v_inst_159_, 0);
lean_inc_ref(v_toApplicative_161_);
lean_dec_ref(v_inst_159_);
v_toFunctor_162_ = lean_ctor_get(v_toApplicative_161_, 0);
lean_inc_ref(v_toFunctor_162_);
lean_dec_ref(v_toApplicative_161_);
v_map_163_ = lean_ctor_get(v_toFunctor_162_, 0);
lean_inc(v_map_163_);
lean_dec_ref(v_toFunctor_162_);
v___f_164_ = ((lean_object*)(l_ShareCommonT_run___redArg___closed__0));
v___x_165_ = l_ShareCommon_mkStateImpl(v_00_u03c3_158_);
v___x_166_ = lean_apply_1(v_x_160_, v___x_165_);
v___x_167_ = lean_apply_4(v_map_163_, lean_box(0), lean_box(0), v___f_164_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonT_run(lean_object* v_m_168_, lean_object* v_00_u03c3_169_, lean_object* v_00_u03b1_170_, lean_object* v_inst_171_, lean_object* v_x_172_){
_start:
{
lean_object* v_toApplicative_173_; lean_object* v_toFunctor_174_; lean_object* v_map_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v_toApplicative_173_ = lean_ctor_get(v_inst_171_, 0);
lean_inc_ref(v_toApplicative_173_);
lean_dec_ref(v_inst_171_);
v_toFunctor_174_ = lean_ctor_get(v_toApplicative_173_, 0);
lean_inc_ref(v_toFunctor_174_);
lean_dec_ref(v_toApplicative_173_);
v_map_175_ = lean_ctor_get(v_toFunctor_174_, 0);
lean_inc(v_map_175_);
lean_dec_ref(v_toFunctor_174_);
v___f_176_ = ((lean_object*)(l_ShareCommonT_run___redArg___closed__0));
v___x_177_ = l_ShareCommon_mkStateImpl(v_00_u03c3_169_);
v___x_178_ = lean_apply_1(v_x_172_, v___x_177_);
v___x_179_ = lean_apply_4(v_map_175_, lean_box(0), lean_box(0), v___f_176_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonM_run___redArg(lean_object* v_00_u03c3_180_, lean_object* v_x_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v_fst_184_; 
v___x_182_ = l_ShareCommon_mkStateImpl(v_00_u03c3_180_);
v___x_183_ = lean_apply_1(v_x_181_, v___x_182_);
v_fst_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_fst_184_);
lean_dec_ref(v___x_183_);
return v_fst_184_;
}
}
LEAN_EXPORT lean_object* l_ShareCommonM_run(lean_object* v_00_u03c3_185_, lean_object* v_00_u03b1_186_, lean_object* v_x_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v_fst_190_; 
v___x_188_ = l_ShareCommon_mkStateImpl(v_00_u03c3_185_);
v___x_189_ = lean_apply_1(v_x_187_, v___x_188_);
v_fst_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_fst_190_);
lean_dec_ref(v___x_189_);
return v_fst_190_;
}
}
LEAN_EXPORT lean_object* l_ShareCommon_shareCommon_x27___boxed(lean_object* v_00_u03b1_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = lean_sharecommon_quick(v_a_194_);
lean_dec(v_a_194_);
return v_res_195_;
}
}
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Control_State(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_ShareCommon(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
