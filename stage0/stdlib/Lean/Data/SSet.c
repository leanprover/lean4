// Lean compiler output
// Module: Lean.Data.SSet
// Imports: public import Lean.Data.SMap
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
lean_object* l_Lean_SMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_SMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SSet_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_SSet_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_switch___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_switch(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_switch___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_SSet_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_SSet_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_SSet_toList___redArg___closed__0 = (const lean_object*)&l_Lean_SSet_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toSSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_toSSet___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_toSSet___redArg___closed__0;
static lean_once_cell_t l_List_toSSet___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_toSSet___redArg___closed__1;
static lean_once_cell_t l_List_toSSet___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_toSSet___redArg___closed__2;
static lean_once_cell_t l_List_toSSet___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_toSSet___redArg___closed__3;
static lean_once_cell_t l_List_toSSet___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_toSSet___redArg___closed__4;
LEAN_EXPORT lean_object* l_List_toSSet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_toSSet(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_instReprSSet___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".toSSet"};
static const lean_object* l_instReprSSet___redArg___lam__0___closed__0 = (const lean_object*)&l_instReprSSet___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_instReprSSet___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_instReprSSet___redArg___lam__0___closed__0_value)}};
static const lean_object* l_instReprSSet___redArg___lam__0___closed__1 = (const lean_object*)&l_instReprSSet___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_instReprSSet___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSSet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSSet___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instReprSSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instReprSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v_inst_1_, v_inst_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___redArg___boxed(lean_object* v_inst_4_, lean_object* v_inst_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_SSet_instInhabited___redArg(v_inst_4_, v_inst_5_);
lean_dec_ref(v_inst_5_);
lean_dec_ref(v_inst_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited(lean_object* v_00_u03b1_7_, lean_object* v_inst_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v_inst_8_, v_inst_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___boxed(lean_object* v_00_u03b1_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_SSet_instInhabited(v_00_u03b1_11_, v_inst_12_, v_inst_13_);
lean_dec_ref(v_inst_13_);
lean_dec_ref(v_inst_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg(lean_object* v_inst_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v_inst_15_, v_inst_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg___boxed(lean_object* v_inst_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_SSet_empty___redArg(v_inst_18_, v_inst_19_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty(lean_object* v_00_u03b1_21_, lean_object* v_inst_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v_inst_22_, v_inst_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___boxed(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_inst_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_SSet_empty(v_00_u03b1_25_, v_inst_26_, v_inst_27_);
lean_dec_ref(v_inst_27_);
lean_dec_ref(v_inst_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert___redArg(lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_s_31_, lean_object* v_a_32_){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_box(0);
v___x_34_ = l_Lean_SMap_insert___redArg(v_inst_29_, v_inst_30_, v_s_31_, v_a_32_, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert(lean_object* v_00_u03b1_35_, lean_object* v_inst_36_, lean_object* v_inst_37_, lean_object* v_s_38_, lean_object* v_a_39_){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = lean_box(0);
v___x_41_ = l_Lean_SMap_insert___redArg(v_inst_36_, v_inst_37_, v_s_38_, v_a_39_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT uint8_t l_Lean_SSet_contains___redArg(lean_object* v_inst_42_, lean_object* v_inst_43_, lean_object* v_s_44_, lean_object* v_a_45_){
_start:
{
uint8_t v___x_46_; 
v___x_46_ = l_Lean_SMap_contains___redArg(v_inst_42_, v_inst_43_, v_s_44_, v_a_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___redArg___boxed(lean_object* v_inst_47_, lean_object* v_inst_48_, lean_object* v_s_49_, lean_object* v_a_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = l_Lean_SSet_contains___redArg(v_inst_47_, v_inst_48_, v_s_49_, v_a_50_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l_Lean_SSet_contains(lean_object* v_00_u03b1_53_, lean_object* v_inst_54_, lean_object* v_inst_55_, lean_object* v_s_56_, lean_object* v_a_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = l_Lean_SMap_contains___redArg(v_inst_54_, v_inst_55_, v_s_56_, v_a_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___boxed(lean_object* v_00_u03b1_59_, lean_object* v_inst_60_, lean_object* v_inst_61_, lean_object* v_s_62_, lean_object* v_a_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Lean_SSet_contains(v_00_u03b1_59_, v_inst_60_, v_inst_61_, v_s_62_, v_a_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg___lam__0(lean_object* v_f_66_, lean_object* v_a_67_, lean_object* v_x_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_apply_1(v_f_66_, v_a_67_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg(lean_object* v_inst_70_, lean_object* v_s_71_, lean_object* v_f_72_){
_start:
{
lean_object* v___f_73_; lean_object* v___x_74_; 
v___f_73_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_73_, 0, v_f_72_);
v___x_74_ = l_Lean_SMap_forM___redArg(v_inst_70_, v_s_71_, v___f_73_);
return v___x_74_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM(lean_object* v_00_u03b1_75_, lean_object* v_inst_76_, lean_object* v_inst_77_, lean_object* v_m_78_, lean_object* v_inst_79_, lean_object* v_s_80_, lean_object* v_f_81_){
_start:
{
lean_object* v___f_82_; lean_object* v___x_83_; 
v___f_82_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_82_, 0, v_f_81_);
v___x_83_ = l_Lean_SMap_forM___redArg(v_inst_79_, v_s_80_, v___f_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___boxed(lean_object* v_00_u03b1_84_, lean_object* v_inst_85_, lean_object* v_inst_86_, lean_object* v_m_87_, lean_object* v_inst_88_, lean_object* v_s_89_, lean_object* v_f_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = l_Lean_SSet_forM(v_00_u03b1_84_, v_inst_85_, v_inst_86_, v_m_87_, v_inst_88_, v_s_89_, v_f_90_);
lean_dec_ref(v_inst_86_);
lean_dec_ref(v_inst_85_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___redArg(lean_object* v_s_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_Lean_SMap_switch___redArg(v_s_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch(lean_object* v_00_u03b1_94_, lean_object* v_inst_95_, lean_object* v_inst_96_, lean_object* v_s_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l_Lean_SMap_switch___redArg(v_s_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___boxed(lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_s_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Lean_SSet_switch(v_00_u03b1_99_, v_inst_100_, v_inst_101_, v_s_102_);
lean_dec_ref(v_inst_101_);
lean_dec_ref(v_inst_100_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg___lam__0(lean_object* v_f_104_, lean_object* v_d_105_, lean_object* v_a_106_, lean_object* v_x_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_apply_2(v_f_104_, v_d_105_, v_a_106_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg(lean_object* v_f_109_, lean_object* v_init_110_, lean_object* v_s_111_){
_start:
{
lean_object* v___f_112_; lean_object* v___x_113_; 
v___f_112_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_112_, 0, v_f_109_);
v___x_113_ = l_Lean_SMap_fold___redArg(v___f_112_, v_init_110_, v_s_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold(lean_object* v_00_u03b1_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_00_u03c3_117_, lean_object* v_f_118_, lean_object* v_init_119_, lean_object* v_s_120_){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; 
v___f_121_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_121_, 0, v_f_118_);
v___x_122_ = l_Lean_SMap_fold___redArg(v___f_121_, v_init_119_, v_s_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___boxed(lean_object* v_00_u03b1_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_00_u03c3_126_, lean_object* v_f_127_, lean_object* v_init_128_, lean_object* v_s_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_SSet_fold(v_00_u03b1_123_, v_inst_124_, v_inst_125_, v_00_u03c3_126_, v_f_127_, v_init_128_, v_s_129_);
lean_dec_ref(v_inst_125_);
lean_dec_ref(v_inst_124_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg___lam__0(lean_object* v_d_131_, lean_object* v_a_132_, lean_object* v_x_133_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v_a_132_);
lean_ctor_set(v___x_134_, 1, v_d_131_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg(lean_object* v_m_136_){
_start:
{
lean_object* v___f_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___f_137_ = ((lean_object*)(l_Lean_SSet_toList___redArg___closed__0));
v___x_138_ = lean_box(0);
v___x_139_ = l_Lean_SMap_fold___redArg(v___f_137_, v___x_138_, v_m_136_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList(lean_object* v_00_u03b1_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_m_143_){
_start:
{
lean_object* v___x_144_; 
v___x_144_ = l_Lean_SSet_toList___redArg(v_m_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___boxed(lean_object* v_00_u03b1_145_, lean_object* v_inst_146_, lean_object* v_inst_147_, lean_object* v_m_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_SSet_toList(v_00_u03b1_145_, v_inst_146_, v_inst_147_, v_m_148_);
lean_dec_ref(v_inst_147_);
lean_dec_ref(v_inst_146_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_List_toSSet___redArg___lam__0(lean_object* v_inst_150_, lean_object* v_inst_151_, lean_object* v_s_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = lean_box(0);
v___x_155_ = l_Lean_SMap_insert___redArg(v_inst_150_, v_inst_151_, v_s_152_, v_a_153_, v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_List_toSSet___redArg___closed__0(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_156_ = lean_box(0);
v___x_157_ = lean_unsigned_to_nat(16u);
v___x_158_ = lean_mk_array(v___x_157_, v___x_156_);
return v___x_158_;
}
}
static lean_object* _init_l_List_toSSet___redArg___closed__1(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = lean_obj_once(&l_List_toSSet___redArg___closed__0, &l_List_toSSet___redArg___closed__0_once, _init_l_List_toSSet___redArg___closed__0);
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v___x_159_);
return v___x_161_;
}
}
static lean_object* _init_l_List_toSSet___redArg___closed__2(void){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_162_;
}
}
static lean_object* _init_l_List_toSSet___redArg___closed__3(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = lean_obj_once(&l_List_toSSet___redArg___closed__2, &l_List_toSSet___redArg___closed__2_once, _init_l_List_toSSet___redArg___closed__2);
v___x_164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_List_toSSet___redArg___closed__4(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; uint8_t v___x_167_; lean_object* v___x_168_; 
v___x_165_ = lean_obj_once(&l_List_toSSet___redArg___closed__3, &l_List_toSSet___redArg___closed__3_once, _init_l_List_toSSet___redArg___closed__3);
v___x_166_ = lean_obj_once(&l_List_toSSet___redArg___closed__1, &l_List_toSSet___redArg___closed__1_once, _init_l_List_toSSet___redArg___closed__1);
v___x_167_ = 1;
v___x_168_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_165_);
lean_ctor_set_uint8(v___x_168_, sizeof(void*)*2, v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_List_toSSet___redArg(lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_es_171_){
_start:
{
lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___f_172_ = lean_alloc_closure((void*)(l_List_toSSet___redArg___lam__0), 4, 2);
lean_closure_set(v___f_172_, 0, v_inst_169_);
lean_closure_set(v___f_172_, 1, v_inst_170_);
v___x_173_ = lean_obj_once(&l_List_toSSet___redArg___closed__4, &l_List_toSSet___redArg___closed__4_once, _init_l_List_toSSet___redArg___closed__4);
v___x_174_ = l_List_foldl___redArg(v___f_172_, v___x_173_, v_es_171_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_List_toSSet(lean_object* v_00_u03b1_175_, lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_es_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_List_toSSet___redArg(v_inst_176_, v_inst_177_, v_es_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet___redArg___lam__0(lean_object* v_inst_183_, lean_object* v_v_184_, lean_object* v_prec_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_186_ = l_Lean_SSet_toList___redArg(v_v_184_);
v___x_187_ = l_List_repr___redArg(v_inst_183_, v___x_186_);
v___x_188_ = ((lean_object*)(l_instReprSSet___redArg___lam__0___closed__1));
v___x_189_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = l_Repr_addAppParen(v___x_189_, v_prec_185_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet___redArg___lam__0___boxed(lean_object* v_inst_191_, lean_object* v_v_192_, lean_object* v_prec_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_instReprSSet___redArg___lam__0(v_inst_191_, v_v_192_, v_prec_193_);
lean_dec(v_prec_193_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet___redArg(lean_object* v_inst_195_){
_start:
{
lean_object* v___f_196_; 
v___f_196_ = lean_alloc_closure((void*)(l_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_196_, 0, v_inst_195_);
return v___f_196_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet(lean_object* v_00_u03b1_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_inst_200_){
_start:
{
lean_object* v___f_201_; 
v___f_201_ = lean_alloc_closure((void*)(l_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_201_, 0, v_inst_200_);
return v___f_201_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet___boxed(lean_object* v_00_u03b1_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_inst_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_instReprSSet(v_00_u03b1_202_, v_x_203_, v_x_204_, v_inst_205_);
lean_dec_ref(v_x_204_);
lean_dec_ref(v_x_203_);
return v_res_206_;
}
}
lean_object* runtime_initialize_Lean_Data_SMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_SSet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_SMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_SSet(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_SMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_SSet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_SMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_SSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_SSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_SSet(builtin);
}
#ifdef __cplusplus
}
#endif
