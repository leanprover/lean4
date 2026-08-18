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
uint8_t l_Lean_SMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___redArg(lean_object*);
lean_object* l_Lean_SMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_SMap_forM___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___closed__0;
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___closed__1;
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___closed__2;
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___closed__3;
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___closed__4;
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_List_toSSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toSSet___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_List_toSSet(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instReprSSet___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ".toSSet"};
static const lean_object* l_Lean_instReprSSet___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instReprSSet___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instReprSSet___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprSSet___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean_instReprSSet___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instReprSSet___redArg___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprSSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__0(void){
_start:
{
lean_object* v_cellCount_1_; lean_object* v___x_2_; 
v_cellCount_1_ = lean_unsigned_to_nat(16u);
v___x_2_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__1(void){
_start:
{
lean_object* v_cellCount_3_; lean_object* v___x_4_; 
v_cellCount_3_ = lean_unsigned_to_nat(16u);
v___x_4_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_5_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__1, &l_Lean_SSet_instInhabited___aux__1___closed__1_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__1);
v___x_6_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__0, &l_Lean_SSet_instInhabited___aux__1___closed__0_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__0);
v___x_7_ = lean_unsigned_to_nat(0u);
v___x_8_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__3(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_9_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_10_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__3, &l_Lean_SSet_instInhabited___aux__1___closed__3_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__3);
v___x_11_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__5(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__4, &l_Lean_SSet_instInhabited___aux__1___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__4);
v___x_13_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__2, &l_Lean_SSet_instInhabited___aux__1___closed__2_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__2);
v___x_14_ = 1;
v___x_15_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_15_, 0, v___x_13_);
lean_ctor_set(v___x_15_, 1, v___x_12_);
lean_ctor_set_uint8(v___x_15_, sizeof(void*)*2, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1(lean_object* v_00_u03b1_16_, lean_object* v_inst_17_, lean_object* v_inst_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__5, &l_Lean_SSet_instInhabited___aux__1___closed__5_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__5);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___boxed(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_SSet_instInhabited___aux__1(v_00_u03b1_20_, v_inst_21_, v_inst_22_);
lean_dec_ref(v_inst_22_);
lean_dec_ref(v_inst_21_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited(lean_object* v_00_u03b1_24_, lean_object* v_inst_25_, lean_object* v_inst_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__5, &l_Lean_SSet_instInhabited___aux__1___closed__5_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__5);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___boxed(lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_SSet_instInhabited(v_00_u03b1_28_, v_inst_29_, v_inst_30_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg(lean_object* v_inst_32_, lean_object* v_inst_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v_inst_32_, v_inst_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg___boxed(lean_object* v_inst_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_SSet_empty___redArg(v_inst_35_, v_inst_36_);
lean_dec_ref(v_inst_36_);
lean_dec_ref(v_inst_35_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty(lean_object* v_00_u03b1_38_, lean_object* v_inst_39_, lean_object* v_inst_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v_inst_39_, v_inst_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___boxed(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_SSet_empty(v_00_u03b1_42_, v_inst_43_, v_inst_44_);
lean_dec_ref(v_inst_44_);
lean_dec_ref(v_inst_43_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert___redArg(lean_object* v_inst_46_, lean_object* v_inst_47_, lean_object* v_s_48_, lean_object* v_a_49_){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_box(0);
v___x_51_ = l_Lean_SMap_insert___redArg(v_inst_46_, v_inst_47_, v_s_48_, v_a_49_, v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert(lean_object* v_00_u03b1_52_, lean_object* v_inst_53_, lean_object* v_inst_54_, lean_object* v_s_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_57_ = lean_box(0);
v___x_58_ = l_Lean_SMap_insert___redArg(v_inst_53_, v_inst_54_, v_s_55_, v_a_56_, v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT uint8_t l_Lean_SSet_contains___redArg(lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_s_61_, lean_object* v_a_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = l_Lean_SMap_contains___redArg(v_inst_59_, v_inst_60_, v_s_61_, v_a_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___redArg___boxed(lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_s_66_, lean_object* v_a_67_){
_start:
{
uint8_t v_res_68_; lean_object* v_r_69_; 
v_res_68_ = l_Lean_SSet_contains___redArg(v_inst_64_, v_inst_65_, v_s_66_, v_a_67_);
v_r_69_ = lean_box(v_res_68_);
return v_r_69_;
}
}
LEAN_EXPORT uint8_t l_Lean_SSet_contains(lean_object* v_00_u03b1_70_, lean_object* v_inst_71_, lean_object* v_inst_72_, lean_object* v_s_73_, lean_object* v_a_74_){
_start:
{
uint8_t v___x_75_; 
v___x_75_ = l_Lean_SMap_contains___redArg(v_inst_71_, v_inst_72_, v_s_73_, v_a_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___boxed(lean_object* v_00_u03b1_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_s_79_, lean_object* v_a_80_){
_start:
{
uint8_t v_res_81_; lean_object* v_r_82_; 
v_res_81_ = l_Lean_SSet_contains(v_00_u03b1_76_, v_inst_77_, v_inst_78_, v_s_79_, v_a_80_);
v_r_82_ = lean_box(v_res_81_);
return v_r_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg___lam__0(lean_object* v_f_83_, lean_object* v_a_84_, lean_object* v_x_85_){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = lean_apply_1(v_f_83_, v_a_84_);
return v___x_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg(lean_object* v_inst_87_, lean_object* v_s_88_, lean_object* v_f_89_){
_start:
{
lean_object* v___f_90_; lean_object* v___x_91_; 
v___f_90_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_90_, 0, v_f_89_);
v___x_91_ = l_Lean_SMap_forM___redArg(v_inst_87_, v_s_88_, v___f_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM(lean_object* v_00_u03b1_92_, lean_object* v_inst_93_, lean_object* v_inst_94_, lean_object* v_m_95_, lean_object* v_inst_96_, lean_object* v_s_97_, lean_object* v_f_98_){
_start:
{
lean_object* v___f_99_; lean_object* v___x_100_; 
v___f_99_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_99_, 0, v_f_98_);
v___x_100_ = l_Lean_SMap_forM___redArg(v_inst_96_, v_s_97_, v___f_99_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___boxed(lean_object* v_00_u03b1_101_, lean_object* v_inst_102_, lean_object* v_inst_103_, lean_object* v_m_104_, lean_object* v_inst_105_, lean_object* v_s_106_, lean_object* v_f_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_SSet_forM(v_00_u03b1_101_, v_inst_102_, v_inst_103_, v_m_104_, v_inst_105_, v_s_106_, v_f_107_);
lean_dec_ref(v_inst_103_);
lean_dec_ref(v_inst_102_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___redArg(lean_object* v_s_109_){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_SMap_switch___redArg(v_s_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch(lean_object* v_00_u03b1_111_, lean_object* v_inst_112_, lean_object* v_inst_113_, lean_object* v_s_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_SMap_switch___redArg(v_s_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___boxed(lean_object* v_00_u03b1_116_, lean_object* v_inst_117_, lean_object* v_inst_118_, lean_object* v_s_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_SSet_switch(v_00_u03b1_116_, v_inst_117_, v_inst_118_, v_s_119_);
lean_dec_ref(v_inst_118_);
lean_dec_ref(v_inst_117_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg___lam__0(lean_object* v_f_121_, lean_object* v_d_122_, lean_object* v_a_123_, lean_object* v_x_124_){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_apply_2(v_f_121_, v_d_122_, v_a_123_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg(lean_object* v_f_126_, lean_object* v_init_127_, lean_object* v_s_128_){
_start:
{
lean_object* v___f_129_; lean_object* v___x_130_; 
v___f_129_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_129_, 0, v_f_126_);
v___x_130_ = l_Lean_SMap_fold___redArg(v___f_129_, v_init_127_, v_s_128_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold(lean_object* v_00_u03b1_131_, lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_00_u03c3_134_, lean_object* v_f_135_, lean_object* v_init_136_, lean_object* v_s_137_){
_start:
{
lean_object* v___f_138_; lean_object* v___x_139_; 
v___f_138_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_138_, 0, v_f_135_);
v___x_139_ = l_Lean_SMap_fold___redArg(v___f_138_, v_init_136_, v_s_137_);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___boxed(lean_object* v_00_u03b1_140_, lean_object* v_inst_141_, lean_object* v_inst_142_, lean_object* v_00_u03c3_143_, lean_object* v_f_144_, lean_object* v_init_145_, lean_object* v_s_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l_Lean_SSet_fold(v_00_u03b1_140_, v_inst_141_, v_inst_142_, v_00_u03c3_143_, v_f_144_, v_init_145_, v_s_146_);
lean_dec_ref(v_inst_142_);
lean_dec_ref(v_inst_141_);
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg___lam__0(lean_object* v_d_148_, lean_object* v_a_149_, lean_object* v_x_150_){
_start:
{
lean_object* v___x_151_; 
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v_a_149_);
lean_ctor_set(v___x_151_, 1, v_d_148_);
return v___x_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg(lean_object* v_m_153_){
_start:
{
lean_object* v___f_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
v___f_154_ = ((lean_object*)(l_Lean_SSet_toList___redArg___closed__0));
v___x_155_ = lean_box(0);
v___x_156_ = l_Lean_SMap_fold___redArg(v___f_154_, v___x_155_, v_m_153_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList(lean_object* v_00_u03b1_157_, lean_object* v_inst_158_, lean_object* v_inst_159_, lean_object* v_m_160_){
_start:
{
lean_object* v___x_161_; 
v___x_161_ = l_Lean_SSet_toList___redArg(v_m_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___boxed(lean_object* v_00_u03b1_162_, lean_object* v_inst_163_, lean_object* v_inst_164_, lean_object* v_m_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Lean_SSet_toList(v_00_u03b1_162_, v_inst_163_, v_inst_164_, v_m_165_);
lean_dec_ref(v_inst_164_);
lean_dec_ref(v_inst_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSSet___redArg___lam__0(lean_object* v_inst_167_, lean_object* v_inst_168_, lean_object* v_s_169_, lean_object* v_a_170_){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = lean_box(0);
v___x_172_ = l_Lean_SMap_insert___redArg(v_inst_167_, v_inst_168_, v_s_169_, v_a_170_, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSSet___redArg(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_es_175_){
_start:
{
lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___f_176_ = lean_alloc_closure((void*)(l_Lean_List_toSSet___redArg___lam__0), 4, 2);
lean_closure_set(v___f_176_, 0, v_inst_173_);
lean_closure_set(v___f_176_, 1, v_inst_174_);
v___x_177_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__5, &l_Lean_SSet_instInhabited___aux__1___closed__5_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__5);
v___x_178_ = l_List_foldl___redArg(v___f_176_, v___x_177_, v_es_175_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSSet(lean_object* v_00_u03b1_179_, lean_object* v_inst_180_, lean_object* v_inst_181_, lean_object* v_es_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_List_toSSet___redArg(v_inst_180_, v_inst_181_, v_es_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg___lam__0(lean_object* v_inst_187_, lean_object* v_v_188_, lean_object* v_prec_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_190_ = l_Lean_SSet_toList___redArg(v_v_188_);
v___x_191_ = l_List_repr___redArg(v_inst_187_, v___x_190_);
v___x_192_ = ((lean_object*)(l_Lean_instReprSSet___redArg___lam__0___closed__1));
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = l_Repr_addAppParen(v___x_193_, v_prec_189_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg___lam__0___boxed(lean_object* v_inst_195_, lean_object* v_v_196_, lean_object* v_prec_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_instReprSSet___redArg___lam__0(v_inst_195_, v_v_196_, v_prec_197_);
lean_dec(v_prec_197_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg(lean_object* v_inst_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Lean_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_200_, 0, v_inst_199_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet(lean_object* v_00_u03b1_201_, lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v___f_205_; 
v___f_205_ = lean_alloc_closure((void*)(l_Lean_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_205_, 0, v_inst_204_);
return v___f_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___boxed(lean_object* v_00_u03b1_206_, lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_instReprSSet(v_00_u03b1_206_, v_x_207_, v_x_208_, v_inst_209_);
lean_dec_ref(v_x_208_);
lean_dec_ref(v_x_207_);
return v_res_210_;
}
}
lean_object* runtime_initialize_Lean_Data_SMap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_SSet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
