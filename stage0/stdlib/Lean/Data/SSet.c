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
LEAN_EXPORT lean_object* l_List_toSSet___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__0, &l_Lean_SSet_instInhabited___aux__1___closed__0_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__2(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_7_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__2, &l_Lean_SSet_instInhabited___aux__1___closed__2_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__2);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___closed__4(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__3, &l_Lean_SSet_instInhabited___aux__1___closed__3_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__3);
v___x_11_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__1, &l_Lean_SSet_instInhabited___aux__1___closed__1_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__1);
v___x_12_ = 1;
v___x_13_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_13_, 0, v___x_11_);
lean_ctor_set(v___x_13_, 1, v___x_10_);
lean_ctor_set_uint8(v___x_13_, sizeof(void*)*2, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__4, &l_Lean_SSet_instInhabited___aux__1___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__4);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___boxed(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_inst_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_SSet_instInhabited___aux__1(v_00_u03b1_18_, v_inst_19_, v_inst_20_);
lean_dec_ref(v_inst_20_);
lean_dec_ref(v_inst_19_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__4, &l_Lean_SSet_instInhabited___aux__1___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__4);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___boxed(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_SSet_instInhabited(v_00_u03b1_26_, v_inst_27_, v_inst_28_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg(lean_object* v_inst_30_, lean_object* v_inst_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v_inst_30_, v_inst_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg___boxed(lean_object* v_inst_33_, lean_object* v_inst_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_SSet_empty___redArg(v_inst_33_, v_inst_34_);
lean_dec_ref(v_inst_34_);
lean_dec_ref(v_inst_33_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty(lean_object* v_00_u03b1_36_, lean_object* v_inst_37_, lean_object* v_inst_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_SMap_empty(lean_box(0), lean_box(0), v_inst_37_, v_inst_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___boxed(lean_object* v_00_u03b1_40_, lean_object* v_inst_41_, lean_object* v_inst_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_SSet_empty(v_00_u03b1_40_, v_inst_41_, v_inst_42_);
lean_dec_ref(v_inst_42_);
lean_dec_ref(v_inst_41_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert___redArg(lean_object* v_inst_44_, lean_object* v_inst_45_, lean_object* v_s_46_, lean_object* v_a_47_){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_box(0);
v___x_49_ = l_Lean_SMap_insert___redArg(v_inst_44_, v_inst_45_, v_s_46_, v_a_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert(lean_object* v_00_u03b1_50_, lean_object* v_inst_51_, lean_object* v_inst_52_, lean_object* v_s_53_, lean_object* v_a_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_box(0);
v___x_56_ = l_Lean_SMap_insert___redArg(v_inst_51_, v_inst_52_, v_s_53_, v_a_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT uint8_t l_Lean_SSet_contains___redArg(lean_object* v_inst_57_, lean_object* v_inst_58_, lean_object* v_s_59_, lean_object* v_a_60_){
_start:
{
uint8_t v___x_61_; 
v___x_61_ = l_Lean_SMap_contains___redArg(v_inst_57_, v_inst_58_, v_s_59_, v_a_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___redArg___boxed(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_s_64_, lean_object* v_a_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_Lean_SSet_contains___redArg(v_inst_62_, v_inst_63_, v_s_64_, v_a_65_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
LEAN_EXPORT uint8_t l_Lean_SSet_contains(lean_object* v_00_u03b1_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_s_71_, lean_object* v_a_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = l_Lean_SMap_contains___redArg(v_inst_69_, v_inst_70_, v_s_71_, v_a_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___boxed(lean_object* v_00_u03b1_74_, lean_object* v_inst_75_, lean_object* v_inst_76_, lean_object* v_s_77_, lean_object* v_a_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_Lean_SSet_contains(v_00_u03b1_74_, v_inst_75_, v_inst_76_, v_s_77_, v_a_78_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg___lam__0(lean_object* v_f_81_, lean_object* v_a_82_, lean_object* v_x_83_){
_start:
{
lean_object* v___x_84_; 
v___x_84_ = lean_apply_1(v_f_81_, v_a_82_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg(lean_object* v_inst_85_, lean_object* v_s_86_, lean_object* v_f_87_){
_start:
{
lean_object* v___f_88_; lean_object* v___x_89_; 
v___f_88_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_88_, 0, v_f_87_);
v___x_89_ = l_Lean_SMap_forM___redArg(v_inst_85_, v_s_86_, v___f_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM(lean_object* v_00_u03b1_90_, lean_object* v_inst_91_, lean_object* v_inst_92_, lean_object* v_m_93_, lean_object* v_inst_94_, lean_object* v_s_95_, lean_object* v_f_96_){
_start:
{
lean_object* v___f_97_; lean_object* v___x_98_; 
v___f_97_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_97_, 0, v_f_96_);
v___x_98_ = l_Lean_SMap_forM___redArg(v_inst_94_, v_s_95_, v___f_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___boxed(lean_object* v_00_u03b1_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_m_102_, lean_object* v_inst_103_, lean_object* v_s_104_, lean_object* v_f_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_SSet_forM(v_00_u03b1_99_, v_inst_100_, v_inst_101_, v_m_102_, v_inst_103_, v_s_104_, v_f_105_);
lean_dec_ref(v_inst_101_);
lean_dec_ref(v_inst_100_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___redArg(lean_object* v_s_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_SMap_switch___redArg(v_s_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch(lean_object* v_00_u03b1_109_, lean_object* v_inst_110_, lean_object* v_inst_111_, lean_object* v_s_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_SMap_switch___redArg(v_s_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___boxed(lean_object* v_00_u03b1_114_, lean_object* v_inst_115_, lean_object* v_inst_116_, lean_object* v_s_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_SSet_switch(v_00_u03b1_114_, v_inst_115_, v_inst_116_, v_s_117_);
lean_dec_ref(v_inst_116_);
lean_dec_ref(v_inst_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg___lam__0(lean_object* v_f_119_, lean_object* v_d_120_, lean_object* v_a_121_, lean_object* v_x_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_apply_2(v_f_119_, v_d_120_, v_a_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg(lean_object* v_f_124_, lean_object* v_init_125_, lean_object* v_s_126_){
_start:
{
lean_object* v___f_127_; lean_object* v___x_128_; 
v___f_127_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_127_, 0, v_f_124_);
v___x_128_ = l_Lean_SMap_fold___redArg(v___f_127_, v_init_125_, v_s_126_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold(lean_object* v_00_u03b1_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_00_u03c3_132_, lean_object* v_f_133_, lean_object* v_init_134_, lean_object* v_s_135_){
_start:
{
lean_object* v___f_136_; lean_object* v___x_137_; 
v___f_136_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_136_, 0, v_f_133_);
v___x_137_ = l_Lean_SMap_fold___redArg(v___f_136_, v_init_134_, v_s_135_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___boxed(lean_object* v_00_u03b1_138_, lean_object* v_inst_139_, lean_object* v_inst_140_, lean_object* v_00_u03c3_141_, lean_object* v_f_142_, lean_object* v_init_143_, lean_object* v_s_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_SSet_fold(v_00_u03b1_138_, v_inst_139_, v_inst_140_, v_00_u03c3_141_, v_f_142_, v_init_143_, v_s_144_);
lean_dec_ref(v_inst_140_);
lean_dec_ref(v_inst_139_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg___lam__0(lean_object* v_d_146_, lean_object* v_a_147_, lean_object* v_x_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v_a_147_);
lean_ctor_set(v___x_149_, 1, v_d_146_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg(lean_object* v_m_151_){
_start:
{
lean_object* v___f_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___f_152_ = ((lean_object*)(l_Lean_SSet_toList___redArg___closed__0));
v___x_153_ = lean_box(0);
v___x_154_ = l_Lean_SMap_fold___redArg(v___f_152_, v___x_153_, v_m_151_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList(lean_object* v_00_u03b1_155_, lean_object* v_inst_156_, lean_object* v_inst_157_, lean_object* v_m_158_){
_start:
{
lean_object* v___x_159_; 
v___x_159_ = l_Lean_SSet_toList___redArg(v_m_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___boxed(lean_object* v_00_u03b1_160_, lean_object* v_inst_161_, lean_object* v_inst_162_, lean_object* v_m_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = l_Lean_SSet_toList(v_00_u03b1_160_, v_inst_161_, v_inst_162_, v_m_163_);
lean_dec_ref(v_inst_162_);
lean_dec_ref(v_inst_161_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* l_List_toSSet___redArg___lam__0(lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_s_167_, lean_object* v_a_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_box(0);
v___x_170_ = l_Lean_SMap_insert___redArg(v_inst_165_, v_inst_166_, v_s_167_, v_a_168_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_List_toSSet___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_es_173_){
_start:
{
lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___f_174_ = lean_alloc_closure((void*)(l_List_toSSet___redArg___lam__0), 4, 2);
lean_closure_set(v___f_174_, 0, v_inst_171_);
lean_closure_set(v___f_174_, 1, v_inst_172_);
v___x_175_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___closed__4, &l_Lean_SSet_instInhabited___aux__1___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___closed__4);
v___x_176_ = l_List_foldl___redArg(v___f_174_, v___x_175_, v_es_173_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_List_toSSet(lean_object* v_00_u03b1_177_, lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_es_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l_List_toSSet___redArg(v_inst_178_, v_inst_179_, v_es_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet___redArg___lam__0(lean_object* v_inst_185_, lean_object* v_v_186_, lean_object* v_prec_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_188_ = l_Lean_SSet_toList___redArg(v_v_186_);
v___x_189_ = l_List_repr___redArg(v_inst_185_, v___x_188_);
v___x_190_ = ((lean_object*)(l_instReprSSet___redArg___lam__0___closed__1));
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = l_Repr_addAppParen(v___x_191_, v_prec_187_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet___redArg___lam__0___boxed(lean_object* v_inst_193_, lean_object* v_v_194_, lean_object* v_prec_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_instReprSSet___redArg___lam__0(v_inst_193_, v_v_194_, v_prec_195_);
lean_dec(v_prec_195_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet___redArg(lean_object* v_inst_197_){
_start:
{
lean_object* v___f_198_; 
v___f_198_ = lean_alloc_closure((void*)(l_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_198_, 0, v_inst_197_);
return v___f_198_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet(lean_object* v_00_u03b1_199_, lean_object* v_x_200_, lean_object* v_x_201_, lean_object* v_inst_202_){
_start:
{
lean_object* v___f_203_; 
v___f_203_ = lean_alloc_closure((void*)(l_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_203_, 0, v_inst_202_);
return v___f_203_;
}
}
LEAN_EXPORT lean_object* l_instReprSSet___boxed(lean_object* v_00_u03b1_204_, lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_instReprSSet(v_00_u03b1_204_, v_x_205_, v_x_206_, v_inst_207_);
lean_dec_ref(v_x_206_);
lean_dec_ref(v_x_205_);
return v_res_208_;
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
