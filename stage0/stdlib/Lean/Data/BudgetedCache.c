// Lean compiler output
// Module: Lean.Data.BudgetedCache
// Imports: public import Init.System.IO public import Lean.Data.LBool public import Lean.Data.PersistentHashMap
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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_instEmptyCollection___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_BudgetedCache_insert___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_insert___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___redArg(){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0, &l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0_once, _init_l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_instInhabitedBudgetedCache_default___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default(lean_object* v_00_u03b1_6_, lean_object* v_00_u03b2_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0, &l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0_once, _init_l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___boxed(lean_object* v_00_u03b1_10_, lean_object* v_00_u03b2_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_instInhabitedBudgetedCache_default(v_00_u03b1_10_, v_00_u03b2_11_, v_inst_12_);
lean_dec_ref(v_inst_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache___redArg(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0, &l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0_once, _init_l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache___redArg___boxed(lean_object* v___dummy_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_instInhabitedBudgetedCache___redArg();
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache(lean_object* v_a_18_, lean_object* v_a_19_, lean_object* v_a_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0, &l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0_once, _init_l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache___boxed(lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_instInhabitedBudgetedCache(v_a_22_, v_a_23_, v_a_24_);
lean_dec_ref(v_a_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0, &l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0_once, _init_l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_instEmptyCollection___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_BudgetedCache_instEmptyCollection___redArg();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_instEmptyCollection(lean_object* v_00_u03b1_30_, lean_object* v_00_u03b2_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_obj_once(&l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0, &l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0_once, _init_l_Lean_instInhabitedBudgetedCache_default___redArg___closed__0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_instEmptyCollection___boxed(lean_object* v_00_u03b1_34_, lean_object* v_00_u03b2_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_BudgetedCache_instEmptyCollection(v_00_u03b1_34_, v_00_u03b2_35_, v_inst_36_);
lean_dec_ref(v_inst_36_);
return v_res_37_;
}
}
LEAN_EXPORT uint8_t l_Lean_BudgetedCache_insert___redArg___lam__0(lean_object* v_inst_38_, lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; uint64_t v___x_43_; uint64_t v___x_44_; uint8_t v___x_45_; 
lean_inc_ref(v_inst_38_);
v___x_41_ = lean_apply_1(v_inst_38_, v_a_39_);
v___x_42_ = lean_apply_1(v_inst_38_, v_b_40_);
v___x_43_ = lean_unbox_uint64(v___x_41_);
lean_dec_ref(v___x_41_);
v___x_44_ = lean_unbox_uint64(v___x_42_);
lean_dec_ref(v___x_42_);
v___x_45_ = lean_uint64_dec_eq(v___x_43_, v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_insert___redArg___lam__0___boxed(lean_object* v_inst_46_, lean_object* v_a_47_, lean_object* v_b_48_){
_start:
{
uint8_t v_res_49_; lean_object* v_r_50_; 
v_res_49_ = l_Lean_BudgetedCache_insert___redArg___lam__0(v_inst_46_, v_a_47_, v_b_48_);
v_r_50_ = lean_box(v_res_49_);
return v_r_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_insert___redArg(lean_object* v_inst_51_, lean_object* v_c_52_, lean_object* v_key_53_, lean_object* v_value_54_){
_start:
{
lean_object* v___f_55_; lean_object* v___x_56_; 
lean_inc_ref(v_inst_51_);
v___f_55_ = lean_alloc_closure((void*)(l_Lean_BudgetedCache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_55_, 0, v_inst_51_);
v___x_56_ = l_Lean_PersistentHashMap_insert___redArg(v___f_55_, v_inst_51_, v_c_52_, v_key_53_, v_value_54_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_insert(lean_object* v_00_u03b1_57_, lean_object* v_00_u03b2_58_, lean_object* v_inst_59_, lean_object* v_c_60_, lean_object* v_key_61_, lean_object* v_value_62_){
_start:
{
lean_object* v___f_63_; lean_object* v___x_64_; 
lean_inc_ref(v_inst_59_);
v___f_63_ = lean_alloc_closure((void*)(l_Lean_BudgetedCache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_63_, 0, v_inst_59_);
v___x_64_ = l_Lean_PersistentHashMap_insert___redArg(v___f_63_, v_inst_59_, v_c_60_, v_key_61_, v_value_62_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg___lam__2(lean_object* v_toPure_65_, lean_object* v_____r_66_){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_67_ = lean_box(0);
v___x_68_ = lean_apply_2(v_toPure_65_, lean_box(0), v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg___lam__0(lean_object* v_toPure_69_, lean_object* v_snd_70_, lean_object* v___f_71_, lean_object* v_inst_72_, lean_object* v_c_73_, lean_object* v_key_74_, lean_object* v_onEvict_75_, lean_object* v_toBind_76_, lean_object* v___f_77_, uint8_t v_____do__lift_78_){
_start:
{
switch(v_____do__lift_78_)
{
case 0:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec(v___f_77_);
lean_dec(v_toBind_76_);
lean_dec(v_onEvict_75_);
lean_dec(v_key_74_);
lean_dec_ref(v_c_73_);
lean_dec_ref(v_inst_72_);
lean_dec_ref(v___f_71_);
lean_dec(v_snd_70_);
v___x_79_ = lean_box(0);
v___x_80_ = lean_apply_2(v_toPure_69_, lean_box(0), v___x_79_);
return v___x_80_;
}
case 1:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_dec(v___f_77_);
lean_dec(v_toBind_76_);
lean_dec(v_onEvict_75_);
lean_dec(v_key_74_);
lean_dec_ref(v_c_73_);
lean_dec_ref(v_inst_72_);
lean_dec_ref(v___f_71_);
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v_snd_70_);
v___x_82_ = lean_apply_2(v_toPure_69_, lean_box(0), v___x_81_);
return v___x_82_;
}
default: 
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v_snd_70_);
lean_dec(v_toPure_69_);
v___x_83_ = l_Lean_PersistentHashMap_erase___redArg(v___f_71_, v_inst_72_, v_c_73_, v_key_74_);
v___x_84_ = lean_apply_1(v_onEvict_75_, v___x_83_);
v___x_85_ = lean_apply_4(v_toBind_76_, lean_box(0), lean_box(0), v___x_84_, v___f_77_);
return v___x_85_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg___lam__0___boxed(lean_object* v_toPure_86_, lean_object* v_snd_87_, lean_object* v___f_88_, lean_object* v_inst_89_, lean_object* v_c_90_, lean_object* v_key_91_, lean_object* v_onEvict_92_, lean_object* v_toBind_93_, lean_object* v___f_94_, lean_object* v_____do__lift_95_){
_start:
{
uint8_t v_____do__lift_274__boxed_96_; lean_object* v_res_97_; 
v_____do__lift_274__boxed_96_ = lean_unbox(v_____do__lift_95_);
v_res_97_ = l_Lean_BudgetedCache_find_x3f___redArg___lam__0(v_toPure_86_, v_snd_87_, v___f_88_, v_inst_89_, v_c_90_, v_key_91_, v_onEvict_92_, v_toBind_93_, v___f_94_, v_____do__lift_274__boxed_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg(lean_object* v_inst_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_c_102_, lean_object* v_key_103_, lean_object* v_onEvict_104_, size_t v_budget_105_){
_start:
{
lean_object* v_toApplicative_106_; lean_object* v_toBind_107_; lean_object* v_toPure_108_; lean_object* v___f_109_; lean_object* v___x_110_; 
v_toApplicative_106_ = lean_ctor_get(v_inst_100_, 0);
lean_inc_ref(v_toApplicative_106_);
v_toBind_107_ = lean_ctor_get(v_inst_100_, 1);
lean_inc(v_toBind_107_);
lean_dec_ref(v_inst_100_);
v_toPure_108_ = lean_ctor_get(v_toApplicative_106_, 1);
lean_inc(v_toPure_108_);
lean_dec_ref(v_toApplicative_106_);
lean_inc_ref_n(v_inst_98_, 2);
v___f_109_ = lean_alloc_closure((void*)(l_Lean_BudgetedCache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_109_, 0, v_inst_98_);
lean_inc(v_key_103_);
lean_inc_ref(v___f_109_);
v___x_110_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_109_, v_inst_98_, v_c_102_, v_key_103_);
if (lean_obj_tag(v___x_110_) == 1)
{
lean_object* v_val_111_; lean_object* v_fst_112_; lean_object* v_snd_113_; lean_object* v___f_114_; lean_object* v___f_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_val_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_val_111_);
lean_dec_ref_known(v___x_110_, 1);
v_fst_112_ = lean_ctor_get(v_val_111_, 0);
lean_inc(v_fst_112_);
v_snd_113_ = lean_ctor_get(v_val_111_, 1);
lean_inc(v_snd_113_);
lean_dec(v_val_111_);
lean_inc(v_toPure_108_);
v___f_114_ = lean_alloc_closure((void*)(l_Lean_BudgetedCache_find_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_114_, 0, v_toPure_108_);
lean_inc(v_toBind_107_);
lean_inc(v_key_103_);
v___f_115_ = lean_alloc_closure((void*)(l_Lean_BudgetedCache_find_x3f___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_115_, 0, v_toPure_108_);
lean_closure_set(v___f_115_, 1, v_snd_113_);
lean_closure_set(v___f_115_, 2, v___f_109_);
lean_closure_set(v___f_115_, 3, v_inst_98_);
lean_closure_set(v___f_115_, 4, v_c_102_);
lean_closure_set(v___f_115_, 5, v_key_103_);
lean_closure_set(v___f_115_, 6, v_onEvict_104_);
lean_closure_set(v___f_115_, 7, v_toBind_107_);
lean_closure_set(v___f_115_, 8, v___f_114_);
v___x_116_ = lean_box_usize(v_budget_105_);
v___x_117_ = lean_apply_3(v_inst_99_, v_key_103_, v_fst_112_, v___x_116_);
v___x_118_ = lean_apply_2(v_inst_101_, lean_box(0), v___x_117_);
v___x_119_ = lean_apply_4(v_toBind_107_, lean_box(0), lean_box(0), v___x_118_, v___f_115_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v___x_110_);
lean_dec_ref(v___f_109_);
lean_dec(v_toBind_107_);
lean_dec(v_onEvict_104_);
lean_dec(v_key_103_);
lean_dec_ref(v_c_102_);
lean_dec(v_inst_101_);
lean_dec_ref(v_inst_99_);
lean_dec_ref(v_inst_98_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_2(v_toPure_108_, lean_box(0), v___x_120_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___redArg___boxed(lean_object* v_inst_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_c_126_, lean_object* v_key_127_, lean_object* v_onEvict_128_, lean_object* v_budget_129_){
_start:
{
size_t v_budget_boxed_130_; lean_object* v_res_131_; 
v_budget_boxed_130_ = lean_unbox_usize(v_budget_129_);
lean_dec(v_budget_129_);
v_res_131_ = l_Lean_BudgetedCache_find_x3f___redArg(v_inst_122_, v_inst_123_, v_inst_124_, v_inst_125_, v_c_126_, v_key_127_, v_onEvict_128_, v_budget_boxed_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f(lean_object* v_00_u03b1_132_, lean_object* v_inst_133_, lean_object* v_00_u03b2_134_, lean_object* v_inst_135_, lean_object* v_m_136_, lean_object* v_inst_137_, lean_object* v_inst_138_, lean_object* v_c_139_, lean_object* v_key_140_, lean_object* v_onEvict_141_, size_t v_budget_142_){
_start:
{
lean_object* v_toApplicative_143_; lean_object* v_toBind_144_; lean_object* v_toPure_145_; lean_object* v___f_146_; lean_object* v___x_147_; 
v_toApplicative_143_ = lean_ctor_get(v_inst_137_, 0);
lean_inc_ref(v_toApplicative_143_);
v_toBind_144_ = lean_ctor_get(v_inst_137_, 1);
lean_inc(v_toBind_144_);
lean_dec_ref(v_inst_137_);
v_toPure_145_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc(v_toPure_145_);
lean_dec_ref(v_toApplicative_143_);
lean_inc_ref_n(v_inst_133_, 2);
v___f_146_ = lean_alloc_closure((void*)(l_Lean_BudgetedCache_insert___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_146_, 0, v_inst_133_);
lean_inc(v_key_140_);
lean_inc_ref(v___f_146_);
v___x_147_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v___f_146_, v_inst_133_, v_c_139_, v_key_140_);
if (lean_obj_tag(v___x_147_) == 1)
{
lean_object* v_val_148_; lean_object* v_fst_149_; lean_object* v_snd_150_; lean_object* v___f_151_; lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v_val_148_ = lean_ctor_get(v___x_147_, 0);
lean_inc(v_val_148_);
lean_dec_ref_known(v___x_147_, 1);
v_fst_149_ = lean_ctor_get(v_val_148_, 0);
lean_inc(v_fst_149_);
v_snd_150_ = lean_ctor_get(v_val_148_, 1);
lean_inc(v_snd_150_);
lean_dec(v_val_148_);
lean_inc(v_toPure_145_);
v___f_151_ = lean_alloc_closure((void*)(l_Lean_BudgetedCache_find_x3f___redArg___lam__2), 2, 1);
lean_closure_set(v___f_151_, 0, v_toPure_145_);
lean_inc(v_toBind_144_);
lean_inc(v_key_140_);
v___f_152_ = lean_alloc_closure((void*)(l_Lean_BudgetedCache_find_x3f___redArg___lam__0___boxed), 10, 9);
lean_closure_set(v___f_152_, 0, v_toPure_145_);
lean_closure_set(v___f_152_, 1, v_snd_150_);
lean_closure_set(v___f_152_, 2, v___f_146_);
lean_closure_set(v___f_152_, 3, v_inst_133_);
lean_closure_set(v___f_152_, 4, v_c_139_);
lean_closure_set(v___f_152_, 5, v_key_140_);
lean_closure_set(v___f_152_, 6, v_onEvict_141_);
lean_closure_set(v___f_152_, 7, v_toBind_144_);
lean_closure_set(v___f_152_, 8, v___f_151_);
v___x_153_ = lean_box_usize(v_budget_142_);
v___x_154_ = lean_apply_3(v_inst_135_, v_key_140_, v_fst_149_, v___x_153_);
v___x_155_ = lean_apply_2(v_inst_138_, lean_box(0), v___x_154_);
v___x_156_ = lean_apply_4(v_toBind_144_, lean_box(0), lean_box(0), v___x_155_, v___f_152_);
return v___x_156_;
}
else
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v___x_147_);
lean_dec_ref(v___f_146_);
lean_dec(v_toBind_144_);
lean_dec(v_onEvict_141_);
lean_dec(v_key_140_);
lean_dec_ref(v_c_139_);
lean_dec(v_inst_138_);
lean_dec_ref(v_inst_135_);
lean_dec_ref(v_inst_133_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_apply_2(v_toPure_145_, lean_box(0), v___x_157_);
return v___x_158_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_BudgetedCache_find_x3f___boxed(lean_object* v_00_u03b1_159_, lean_object* v_inst_160_, lean_object* v_00_u03b2_161_, lean_object* v_inst_162_, lean_object* v_m_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_c_166_, lean_object* v_key_167_, lean_object* v_onEvict_168_, lean_object* v_budget_169_){
_start:
{
size_t v_budget_boxed_170_; lean_object* v_res_171_; 
v_budget_boxed_170_ = lean_unbox_usize(v_budget_169_);
lean_dec(v_budget_169_);
v_res_171_ = l_Lean_BudgetedCache_find_x3f(v_00_u03b1_159_, v_inst_160_, v_00_u03b2_161_, v_inst_162_, v_m_163_, v_inst_164_, v_inst_165_, v_c_166_, v_key_167_, v_onEvict_168_, v_budget_boxed_170_);
return v_res_171_;
}
}
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_BudgetedCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_BudgetedCache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Lean_Data_LBool(uint8_t builtin);
lean_object* initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_BudgetedCache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LBool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_BudgetedCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_BudgetedCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_BudgetedCache(builtin);
}
#ifdef __cplusplus
}
#endif
