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
lean_object* l_Lean_SMap_empty___redArg();
lean_object* l_Lean_SMap_switch___redArg(lean_object*);
lean_object* l_Lean_SMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_fold___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_SMap_forM___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___redArg___closed__0;
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___redArg___closed__1;
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___redArg___closed__2;
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___redArg___closed__3;
static lean_once_cell_t l_Lean_SSet_instInhabited___aux__1___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___aux__1___redArg___closed__4;
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___redArg();
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_SSet_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_instInhabited___closed__0;
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_SSet_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_SSet_empty___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = lean_unsigned_to_nat(16u);
v___x_3_ = lean_mk_array(v___x_2_, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__0, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__0_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__0);
v___x_5_ = lean_unsigned_to_nat(0u);
v___x_6_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set(v___x_6_, 1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_7_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_8_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__2, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__2_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__2);
v___x_9_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_9_, 0, v___x_8_);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__4(void){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; uint8_t v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__3, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__3_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__3);
v___x_11_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__1, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__1_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__1);
v___x_12_ = 1;
v___x_13_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_13_, 0, v___x_11_);
lean_ctor_set(v___x_13_, 1, v___x_10_);
lean_ctor_set_uint8(v___x_13_, sizeof(void*)*2, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___redArg(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__4, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__4);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___redArg___boxed(lean_object* v___dummy_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_SSet_instInhabited___aux__1___redArg();
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_inst_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__4, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__4);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___boxed(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_SSet_instInhabited___aux__1(v_00_u03b1_22_, v_inst_23_, v_inst_24_);
lean_dec_ref(v_inst_24_);
lean_dec_ref(v_inst_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__4, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__4);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_SSet_instInhabited___redArg();
return v_res_29_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Lean_SSet_instInhabited___redArg();
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited(lean_object* v_00_u03b1_31_, lean_object* v_inst_32_, lean_object* v_inst_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l_Lean_SSet_instInhabited___closed__0, &l_Lean_SSet_instInhabited___closed__0_once, _init_l_Lean_SSet_instInhabited___closed__0);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___boxed(lean_object* v_00_u03b1_35_, lean_object* v_inst_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_SSet_instInhabited(v_00_u03b1_35_, v_inst_36_, v_inst_37_);
lean_dec_ref(v_inst_37_);
lean_dec_ref(v_inst_36_);
return v_res_38_;
}
}
static lean_object* _init_l_Lean_SSet_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_SMap_empty___redArg();
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg(){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_once(&l_Lean_SSet_empty___redArg___closed__0, &l_Lean_SSet_empty___redArg___closed__0_once, _init_l_Lean_SSet_empty___redArg___closed__0);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg___boxed(lean_object* v___dummy_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_SSet_empty___redArg();
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty(lean_object* v_00_u03b1_44_, lean_object* v_inst_45_, lean_object* v_inst_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_obj_once(&l_Lean_SSet_empty___redArg___closed__0, &l_Lean_SSet_empty___redArg___closed__0_once, _init_l_Lean_SSet_empty___redArg___closed__0);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___boxed(lean_object* v_00_u03b1_48_, lean_object* v_inst_49_, lean_object* v_inst_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_SSet_empty(v_00_u03b1_48_, v_inst_49_, v_inst_50_);
lean_dec_ref(v_inst_50_);
lean_dec_ref(v_inst_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert___redArg(lean_object* v_inst_52_, lean_object* v_inst_53_, lean_object* v_s_54_, lean_object* v_a_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_box(0);
v___x_57_ = l_Lean_SMap_insert___redArg(v_inst_52_, v_inst_53_, v_s_54_, v_a_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert(lean_object* v_00_u03b1_58_, lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_s_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_box(0);
v___x_64_ = l_Lean_SMap_insert___redArg(v_inst_59_, v_inst_60_, v_s_61_, v_a_62_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT uint8_t l_Lean_SSet_contains___redArg(lean_object* v_inst_65_, lean_object* v_inst_66_, lean_object* v_s_67_, lean_object* v_a_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = l_Lean_SMap_contains___redArg(v_inst_65_, v_inst_66_, v_s_67_, v_a_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___redArg___boxed(lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_s_72_, lean_object* v_a_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_Lean_SSet_contains___redArg(v_inst_70_, v_inst_71_, v_s_72_, v_a_73_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT uint8_t l_Lean_SSet_contains(lean_object* v_00_u03b1_76_, lean_object* v_inst_77_, lean_object* v_inst_78_, lean_object* v_s_79_, lean_object* v_a_80_){
_start:
{
uint8_t v___x_81_; 
v___x_81_ = l_Lean_SMap_contains___redArg(v_inst_77_, v_inst_78_, v_s_79_, v_a_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___boxed(lean_object* v_00_u03b1_82_, lean_object* v_inst_83_, lean_object* v_inst_84_, lean_object* v_s_85_, lean_object* v_a_86_){
_start:
{
uint8_t v_res_87_; lean_object* v_r_88_; 
v_res_87_ = l_Lean_SSet_contains(v_00_u03b1_82_, v_inst_83_, v_inst_84_, v_s_85_, v_a_86_);
v_r_88_ = lean_box(v_res_87_);
return v_r_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg___lam__0(lean_object* v_f_89_, lean_object* v_a_90_, lean_object* v_x_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lean_apply_1(v_f_89_, v_a_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg(lean_object* v_inst_93_, lean_object* v_s_94_, lean_object* v_f_95_){
_start:
{
lean_object* v___f_96_; lean_object* v___x_97_; 
v___f_96_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_96_, 0, v_f_95_);
v___x_97_ = l_Lean_SMap_forM___redArg(v_inst_93_, v_s_94_, v___f_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM(lean_object* v_00_u03b1_98_, lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_m_101_, lean_object* v_inst_102_, lean_object* v_s_103_, lean_object* v_f_104_){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; 
v___f_105_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_105_, 0, v_f_104_);
v___x_106_ = l_Lean_SMap_forM___redArg(v_inst_102_, v_s_103_, v___f_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___boxed(lean_object* v_00_u03b1_107_, lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_m_110_, lean_object* v_inst_111_, lean_object* v_s_112_, lean_object* v_f_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_SSet_forM(v_00_u03b1_107_, v_inst_108_, v_inst_109_, v_m_110_, v_inst_111_, v_s_112_, v_f_113_);
lean_dec_ref(v_inst_109_);
lean_dec_ref(v_inst_108_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___redArg(lean_object* v_s_115_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_SMap_switch___redArg(v_s_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch(lean_object* v_00_u03b1_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_s_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_SMap_switch___redArg(v_s_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___boxed(lean_object* v_00_u03b1_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_s_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_SSet_switch(v_00_u03b1_122_, v_inst_123_, v_inst_124_, v_s_125_);
lean_dec_ref(v_inst_124_);
lean_dec_ref(v_inst_123_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg___lam__0(lean_object* v_f_127_, lean_object* v_d_128_, lean_object* v_a_129_, lean_object* v_x_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_apply_2(v_f_127_, v_d_128_, v_a_129_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg(lean_object* v_f_132_, lean_object* v_init_133_, lean_object* v_s_134_){
_start:
{
lean_object* v___f_135_; lean_object* v___x_136_; 
v___f_135_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_135_, 0, v_f_132_);
v___x_136_ = l_Lean_SMap_fold___redArg(v___f_135_, v_init_133_, v_s_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold(lean_object* v_00_u03b1_137_, lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_00_u03c3_140_, lean_object* v_f_141_, lean_object* v_init_142_, lean_object* v_s_143_){
_start:
{
lean_object* v___f_144_; lean_object* v___x_145_; 
v___f_144_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_144_, 0, v_f_141_);
v___x_145_ = l_Lean_SMap_fold___redArg(v___f_144_, v_init_142_, v_s_143_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___boxed(lean_object* v_00_u03b1_146_, lean_object* v_inst_147_, lean_object* v_inst_148_, lean_object* v_00_u03c3_149_, lean_object* v_f_150_, lean_object* v_init_151_, lean_object* v_s_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_SSet_fold(v_00_u03b1_146_, v_inst_147_, v_inst_148_, v_00_u03c3_149_, v_f_150_, v_init_151_, v_s_152_);
lean_dec_ref(v_inst_148_);
lean_dec_ref(v_inst_147_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg___lam__0(lean_object* v_d_154_, lean_object* v_a_155_, lean_object* v_x_156_){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v_a_155_);
lean_ctor_set(v___x_157_, 1, v_d_154_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg(lean_object* v_m_159_){
_start:
{
lean_object* v___f_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___f_160_ = ((lean_object*)(l_Lean_SSet_toList___redArg___closed__0));
v___x_161_ = lean_box(0);
v___x_162_ = l_Lean_SMap_fold___redArg(v___f_160_, v___x_161_, v_m_159_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList(lean_object* v_00_u03b1_163_, lean_object* v_inst_164_, lean_object* v_inst_165_, lean_object* v_m_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_SSet_toList___redArg(v_m_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___boxed(lean_object* v_00_u03b1_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_m_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_SSet_toList(v_00_u03b1_168_, v_inst_169_, v_inst_170_, v_m_171_);
lean_dec_ref(v_inst_170_);
lean_dec_ref(v_inst_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSSet___redArg___lam__0(lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_s_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_box(0);
v___x_178_ = l_Lean_SMap_insert___redArg(v_inst_173_, v_inst_174_, v_s_175_, v_a_176_, v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSSet___redArg(lean_object* v_inst_179_, lean_object* v_inst_180_, lean_object* v_es_181_){
_start:
{
lean_object* v___f_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___f_182_ = lean_alloc_closure((void*)(l_Lean_List_toSSet___redArg___lam__0), 4, 2);
lean_closure_set(v___f_182_, 0, v_inst_179_);
lean_closure_set(v___f_182_, 1, v_inst_180_);
v___x_183_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__4, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__4);
v___x_184_ = l_List_foldl___redArg(v___f_182_, v___x_183_, v_es_181_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSSet(lean_object* v_00_u03b1_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_es_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_List_toSSet___redArg(v_inst_186_, v_inst_187_, v_es_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg___lam__0(lean_object* v_inst_193_, lean_object* v_v_194_, lean_object* v_prec_195_){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_196_ = l_Lean_SSet_toList___redArg(v_v_194_);
v___x_197_ = l_List_repr___redArg(v_inst_193_, v___x_196_);
v___x_198_ = ((lean_object*)(l_Lean_instReprSSet___redArg___lam__0___closed__1));
v___x_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = l_Repr_addAppParen(v___x_199_, v_prec_195_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg___lam__0___boxed(lean_object* v_inst_201_, lean_object* v_v_202_, lean_object* v_prec_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_instReprSSet___redArg___lam__0(v_inst_201_, v_v_202_, v_prec_203_);
lean_dec(v_prec_203_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg(lean_object* v_inst_205_){
_start:
{
lean_object* v___f_206_; 
v___f_206_ = lean_alloc_closure((void*)(l_Lean_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_206_, 0, v_inst_205_);
return v___f_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet(lean_object* v_00_u03b1_207_, lean_object* v_x_208_, lean_object* v_x_209_, lean_object* v_inst_210_){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = lean_alloc_closure((void*)(l_Lean_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_211_, 0, v_inst_210_);
return v___f_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___boxed(lean_object* v_00_u03b1_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Lean_instReprSSet(v_00_u03b1_212_, v_x_213_, v_x_214_, v_inst_215_);
lean_dec_ref(v_x_214_);
lean_dec_ref(v_x_213_);
return v_res_216_;
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
