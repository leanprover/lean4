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
lean_object* l_Lean_SSet_instInhabited___aux__1___redArg(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__4, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__4);
return v___x_15_;
}
}
LEAN_EXPORT void l_Lean_SSet_instInhabited___aux__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_16_;
v_res_16_ = l_Lean_SSet_instInhabited___aux__1___redArg();
stack->m_obj
 = v_res_16_;
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___redArg___boxed(lean_object* v___dummy_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_SSet_instInhabited___aux__1___redArg();
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1(lean_object* v_00_u03b1_19_, lean_object* v_inst_20_, lean_object* v_inst_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__4, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__4);
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___aux__1___boxed(lean_object* v_00_u03b1_23_, lean_object* v_inst_24_, lean_object* v_inst_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_SSet_instInhabited___aux__1(v_00_u03b1_23_, v_inst_24_, v_inst_25_);
lean_dec_ref(v_inst_25_);
lean_dec_ref(v_inst_24_);
return v_res_26_;
}
}
lean_object* l_Lean_SSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__4, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__4);
return v___x_28_;
}
}
LEAN_EXPORT void l_Lean_SSet_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_29_;
v_res_29_ = l_Lean_SSet_instInhabited___redArg();
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___redArg___boxed(lean_object* v___dummy_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_SSet_instInhabited___redArg();
return v_res_31_;
}
}
static lean_object* _init_l_Lean_SSet_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_SSet_instInhabited___redArg();
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited(lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Lean_SSet_instInhabited___closed__0, &l_Lean_SSet_instInhabited___closed__0_once, _init_l_Lean_SSet_instInhabited___closed__0);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_instInhabited___boxed(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_SSet_instInhabited(v_00_u03b1_37_, v_inst_38_, v_inst_39_);
lean_dec_ref(v_inst_39_);
lean_dec_ref(v_inst_38_);
return v_res_40_;
}
}
static lean_object* _init_l_Lean_SSet_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_SMap_empty___redArg();
return v___x_41_;
}
}
lean_object* l_Lean_SSet_empty___redArg(){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Lean_SSet_empty___redArg___closed__0, &l_Lean_SSet_empty___redArg___closed__0_once, _init_l_Lean_SSet_empty___redArg___closed__0);
return v___x_43_;
}
}
LEAN_EXPORT void l_Lean_SSet_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_44_;
v_res_44_ = l_Lean_SSet_empty___redArg();
stack->m_obj
 = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___redArg___boxed(lean_object* v___dummy_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_SSet_empty___redArg();
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lean_obj_once(&l_Lean_SSet_empty___redArg___closed__0, &l_Lean_SSet_empty___redArg___closed__0_once, _init_l_Lean_SSet_empty___redArg___closed__0);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_empty___boxed(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_SSet_empty(v_00_u03b1_51_, v_inst_52_, v_inst_53_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_inst_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert___redArg(lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_s_57_, lean_object* v_a_58_){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_box(0);
v___x_60_ = l_Lean_SMap_insert___redArg(v_inst_55_, v_inst_56_, v_s_57_, v_a_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_insert(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_s_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_box(0);
v___x_67_ = l_Lean_SMap_insert___redArg(v_inst_62_, v_inst_63_, v_s_64_, v_a_65_, v___x_66_);
return v___x_67_;
}
}
uint8_t l_Lean_SSet_contains___redArg(lean_object* v_inst_68_, lean_object* v_inst_69_, lean_object* v_s_70_, lean_object* v_a_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = l_Lean_SMap_contains___redArg(v_inst_68_, v_inst_69_, v_s_70_, v_a_71_);
return v___x_72_;
}
}
LEAN_EXPORT void l_Lean_SSet_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_68_ = stack[0].m_obj;
lean_object* v_inst_69_ = stack[1].m_obj;
lean_object* v_s_70_ = stack[2].m_obj;
lean_object* v_a_71_ = stack[3].m_obj;
uint8_t v_res_73_;
v_res_73_ = l_Lean_SSet_contains___redArg(v_inst_68_, v_inst_69_, v_s_70_, v_a_71_);
stack->m_num = v_res_73_;
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___redArg___boxed(lean_object* v_inst_74_, lean_object* v_inst_75_, lean_object* v_s_76_, lean_object* v_a_77_){
_start:
{
uint8_t v_res_78_; lean_object* v_r_79_; 
v_res_78_ = l_Lean_SSet_contains___redArg(v_inst_74_, v_inst_75_, v_s_76_, v_a_77_);
v_r_79_ = lean_box(v_res_78_);
return v_r_79_;
}
}
uint8_t l_Lean_SSet_contains(lean_object* v_00_u03b1_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_s_83_, lean_object* v_a_84_){
_start:
{
uint8_t v___x_85_; 
v___x_85_ = l_Lean_SMap_contains___redArg(v_inst_81_, v_inst_82_, v_s_83_, v_a_84_);
return v___x_85_;
}
}
LEAN_EXPORT void l_Lean_SSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_81_ = stack[1].m_obj;
lean_object* v_inst_82_ = stack[2].m_obj;
lean_object* v_s_83_ = stack[3].m_obj;
lean_object* v_a_84_ = stack[4].m_obj;
uint8_t v_res_86_;
v_res_86_ = l_Lean_SSet_contains(lean_box(0), v_inst_81_, v_inst_82_, v_s_83_, v_a_84_);
stack->m_num = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_SSet_contains___boxed(lean_object* v_00_u03b1_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_s_90_, lean_object* v_a_91_){
_start:
{
uint8_t v_res_92_; lean_object* v_r_93_; 
v_res_92_ = l_Lean_SSet_contains(v_00_u03b1_87_, v_inst_88_, v_inst_89_, v_s_90_, v_a_91_);
v_r_93_ = lean_box(v_res_92_);
return v_r_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg___lam__0(lean_object* v_f_94_, lean_object* v_a_95_, lean_object* v_x_96_){
_start:
{
lean_object* v___x_97_; 
v___x_97_ = lean_apply_1(v_f_94_, v_a_95_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___redArg(lean_object* v_inst_98_, lean_object* v_s_99_, lean_object* v_f_100_){
_start:
{
lean_object* v___f_101_; lean_object* v___x_102_; 
v___f_101_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_101_, 0, v_f_100_);
v___x_102_ = l_Lean_SMap_forM___redArg(v_inst_98_, v_s_99_, v___f_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM(lean_object* v_00_u03b1_103_, lean_object* v_inst_104_, lean_object* v_inst_105_, lean_object* v_m_106_, lean_object* v_inst_107_, lean_object* v_s_108_, lean_object* v_f_109_){
_start:
{
lean_object* v___f_110_; lean_object* v___x_111_; 
v___f_110_ = lean_alloc_closure((void*)(l_Lean_SSet_forM___redArg___lam__0), 3, 1);
lean_closure_set(v___f_110_, 0, v_f_109_);
v___x_111_ = l_Lean_SMap_forM___redArg(v_inst_107_, v_s_108_, v___f_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_forM___boxed(lean_object* v_00_u03b1_112_, lean_object* v_inst_113_, lean_object* v_inst_114_, lean_object* v_m_115_, lean_object* v_inst_116_, lean_object* v_s_117_, lean_object* v_f_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_SSet_forM(v_00_u03b1_112_, v_inst_113_, v_inst_114_, v_m_115_, v_inst_116_, v_s_117_, v_f_118_);
lean_dec_ref(v_inst_114_);
lean_dec_ref(v_inst_113_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___redArg(lean_object* v_s_120_){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_SMap_switch___redArg(v_s_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch(lean_object* v_00_u03b1_122_, lean_object* v_inst_123_, lean_object* v_inst_124_, lean_object* v_s_125_){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_SMap_switch___redArg(v_s_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_switch___boxed(lean_object* v_00_u03b1_127_, lean_object* v_inst_128_, lean_object* v_inst_129_, lean_object* v_s_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Lean_SSet_switch(v_00_u03b1_127_, v_inst_128_, v_inst_129_, v_s_130_);
lean_dec_ref(v_inst_129_);
lean_dec_ref(v_inst_128_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg___lam__0(lean_object* v_f_132_, lean_object* v_d_133_, lean_object* v_a_134_, lean_object* v_x_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_apply_2(v_f_132_, v_d_133_, v_a_134_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___redArg(lean_object* v_f_137_, lean_object* v_init_138_, lean_object* v_s_139_){
_start:
{
lean_object* v___f_140_; lean_object* v___x_141_; 
v___f_140_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_140_, 0, v_f_137_);
v___x_141_ = l_Lean_SMap_fold___redArg(v___f_140_, v_init_138_, v_s_139_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold(lean_object* v_00_u03b1_142_, lean_object* v_inst_143_, lean_object* v_inst_144_, lean_object* v_00_u03c3_145_, lean_object* v_f_146_, lean_object* v_init_147_, lean_object* v_s_148_){
_start:
{
lean_object* v___f_149_; lean_object* v___x_150_; 
v___f_149_ = lean_alloc_closure((void*)(l_Lean_SSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_149_, 0, v_f_146_);
v___x_150_ = l_Lean_SMap_fold___redArg(v___f_149_, v_init_147_, v_s_148_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_fold___boxed(lean_object* v_00_u03b1_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_00_u03c3_154_, lean_object* v_f_155_, lean_object* v_init_156_, lean_object* v_s_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_SSet_fold(v_00_u03b1_151_, v_inst_152_, v_inst_153_, v_00_u03c3_154_, v_f_155_, v_init_156_, v_s_157_);
lean_dec_ref(v_inst_153_);
lean_dec_ref(v_inst_152_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg___lam__0(lean_object* v_d_159_, lean_object* v_a_160_, lean_object* v_x_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v_a_160_);
lean_ctor_set(v___x_162_, 1, v_d_159_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___redArg(lean_object* v_m_164_){
_start:
{
lean_object* v___f_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___f_165_ = ((lean_object*)(l_Lean_SSet_toList___redArg___closed__0));
v___x_166_ = lean_box(0);
v___x_167_ = l_Lean_SMap_fold___redArg(v___f_165_, v___x_166_, v_m_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList(lean_object* v_00_u03b1_168_, lean_object* v_inst_169_, lean_object* v_inst_170_, lean_object* v_m_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_SSet_toList___redArg(v_m_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_SSet_toList___boxed(lean_object* v_00_u03b1_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_m_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_SSet_toList(v_00_u03b1_173_, v_inst_174_, v_inst_175_, v_m_176_);
lean_dec_ref(v_inst_175_);
lean_dec_ref(v_inst_174_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSSet___redArg___lam__0(lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_s_180_, lean_object* v_a_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_box(0);
v___x_183_ = l_Lean_SMap_insert___redArg(v_inst_178_, v_inst_179_, v_s_180_, v_a_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSSet___redArg(lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_es_186_){
_start:
{
lean_object* v___f_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___f_187_ = lean_alloc_closure((void*)(l_Lean_List_toSSet___redArg___lam__0), 4, 2);
lean_closure_set(v___f_187_, 0, v_inst_184_);
lean_closure_set(v___f_187_, 1, v_inst_185_);
v___x_188_ = lean_obj_once(&l_Lean_SSet_instInhabited___aux__1___redArg___closed__4, &l_Lean_SSet_instInhabited___aux__1___redArg___closed__4_once, _init_l_Lean_SSet_instInhabited___aux__1___redArg___closed__4);
v___x_189_ = l_List_foldl___redArg(v___f_187_, v___x_188_, v_es_186_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_List_toSSet(lean_object* v_00_u03b1_190_, lean_object* v_inst_191_, lean_object* v_inst_192_, lean_object* v_es_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_List_toSSet___redArg(v_inst_191_, v_inst_192_, v_es_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg___lam__0(lean_object* v_inst_198_, lean_object* v_v_199_, lean_object* v_prec_200_){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_201_ = l_Lean_SSet_toList___redArg(v_v_199_);
v___x_202_ = l_List_repr___redArg(v_inst_198_, v___x_201_);
v___x_203_ = ((lean_object*)(l_Lean_instReprSSet___redArg___lam__0___closed__1));
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_202_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = l_Repr_addAppParen(v___x_204_, v_prec_200_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg___lam__0___boxed(lean_object* v_inst_206_, lean_object* v_v_207_, lean_object* v_prec_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_instReprSSet___redArg___lam__0(v_inst_206_, v_v_207_, v_prec_208_);
lean_dec(v_prec_208_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___redArg(lean_object* v_inst_210_){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = lean_alloc_closure((void*)(l_Lean_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_211_, 0, v_inst_210_);
return v___f_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet(lean_object* v_00_u03b1_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_inst_215_){
_start:
{
lean_object* v___f_216_; 
v___f_216_ = lean_alloc_closure((void*)(l_Lean_instReprSSet___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_216_, 0, v_inst_215_);
return v___f_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprSSet___boxed(lean_object* v_00_u03b1_217_, lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_instReprSSet(v_00_u03b1_217_, v_x_218_, v_x_219_, v_inst_220_);
lean_dec_ref(v_x_219_);
lean_dec_ref(v_x_218_);
return v_res_221_;
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
