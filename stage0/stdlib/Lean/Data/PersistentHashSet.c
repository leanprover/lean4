// Lean compiler output
// Module: Lean.Data.PersistentHashSet
// Imports: public import Lean.Data.PersistentHashMap
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
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlMAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_Node_isEmpty___redArg(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_PersistentHashMap_findKeyDAux___redArg(lean_object*, lean_object*, size_t, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_toList___redArg(lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_PersistentHashSet_fold___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__0_value;
static const lean_closure_object l_Lean_PersistentHashSet_fold___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__1 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__1_value;
static const lean_closure_object l_Lean_PersistentHashSet_fold___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__2 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__2_value;
static const lean_closure_object l_Lean_PersistentHashSet_fold___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__3 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__3_value;
static const lean_closure_object l_Lean_PersistentHashSet_fold___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__4 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__4_value;
static const lean_closure_object l_Lean_PersistentHashSet_fold___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__5 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__5_value;
static const lean_closure_object l_Lean_PersistentHashSet_fold___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__6 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__6_value;
static const lean_ctor_object l_Lean_PersistentHashSet_fold___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__0_value),((lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__1_value)}};
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__7 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__7_value;
static const lean_ctor_object l_Lean_PersistentHashSet_fold___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__7_value),((lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__2_value),((lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__3_value),((lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__4_value),((lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__5_value)}};
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__8 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__8_value;
static const lean_ctor_object l_Lean_PersistentHashSet_fold___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__8_value),((lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__6_value)}};
static const lean_object* l_Lean_PersistentHashSet_fold___redArg___closed__9 = (const lean_object*)&l_Lean_PersistentHashSet_fold___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_PersistentHashSet_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_PersistentHashSet_toList___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_PersistentHashSet_toList___redArg___closed__0 = (const lean_object*)&l_Lean_PersistentHashSet_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v_inst_1_, v_inst_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___redArg___boxed(lean_object* v_inst_4_, lean_object* v_inst_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_PersistentHashSet_empty___redArg(v_inst_4_, v_inst_5_);
lean_dec_ref(v_inst_5_);
lean_dec_ref(v_inst_4_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty(lean_object* v_00_u03b1_7_, lean_object* v_inst_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v_inst_8_, v_inst_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___boxed(lean_object* v_00_u03b1_11_, lean_object* v_inst_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Lean_PersistentHashSet_empty(v_00_u03b1_11_, v_inst_12_, v_inst_13_);
lean_dec_ref(v_inst_13_);
lean_dec_ref(v_inst_12_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___redArg(lean_object* v_inst_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v_inst_15_, v_inst_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___redArg___boxed(lean_object* v_inst_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_PersistentHashSet_instInhabited___redArg(v_inst_18_, v_inst_19_);
lean_dec_ref(v_inst_19_);
lean_dec_ref(v_inst_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited(lean_object* v_00_u03b1_21_, lean_object* v_inst_22_, lean_object* v_inst_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v_inst_22_, v_inst_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___boxed(lean_object* v_00_u03b1_25_, lean_object* v_inst_26_, lean_object* v_inst_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lean_PersistentHashSet_instInhabited(v_00_u03b1_25_, v_inst_26_, v_inst_27_);
lean_dec_ref(v_inst_27_);
lean_dec_ref(v_inst_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg(lean_object* v_inst_29_, lean_object* v_inst_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v_inst_29_, v_inst_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg___boxed(lean_object* v_inst_32_, lean_object* v_inst_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_PersistentHashSet_instEmptyCollection___redArg(v_inst_32_, v_inst_33_);
lean_dec_ref(v_inst_33_);
lean_dec_ref(v_inst_32_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection(lean_object* v_00_u03b1_35_, lean_object* v_inst_36_, lean_object* v_inst_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v_inst_36_, v_inst_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_39_, lean_object* v_inst_40_, lean_object* v_inst_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_PersistentHashSet_instEmptyCollection(v_00_u03b1_39_, v_inst_40_, v_inst_41_);
lean_dec_ref(v_inst_41_);
lean_dec_ref(v_inst_40_);
return v_res_42_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_isEmpty___redArg(lean_object* v_s_43_){
_start:
{
uint8_t v___x_44_; 
v___x_44_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_s_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_isEmpty___redArg___boxed(lean_object* v_s_45_){
_start:
{
uint8_t v_res_46_; lean_object* v_r_47_; 
v_res_46_ = l_Lean_PersistentHashSet_isEmpty___redArg(v_s_45_);
lean_dec_ref(v_s_45_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_isEmpty(lean_object* v_00_u03b1_48_, lean_object* v_x_49_, lean_object* v_x_50_, lean_object* v_s_51_){
_start:
{
uint8_t v___x_52_; 
v___x_52_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_s_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_isEmpty___boxed(lean_object* v_00_u03b1_53_, lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_s_56_){
_start:
{
uint8_t v_res_57_; lean_object* v_r_58_; 
v_res_57_ = l_Lean_PersistentHashSet_isEmpty(v_00_u03b1_53_, v_x_54_, v_x_55_, v_s_56_);
lean_dec_ref(v_s_56_);
lean_dec_ref(v_x_55_);
lean_dec_ref(v_x_54_);
v_r_58_ = lean_box(v_res_57_);
return v_r_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_insert___redArg(lean_object* v_x_59_, lean_object* v_x_60_, lean_object* v_s_61_, lean_object* v_a_62_){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = lean_box(0);
v___x_64_ = l_Lean_PersistentHashMap_insert___redArg(v_x_59_, v_x_60_, v_s_61_, v_a_62_, v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_insert(lean_object* v_00_u03b1_65_, lean_object* v_x_66_, lean_object* v_x_67_, lean_object* v_s_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_box(0);
v___x_71_ = l_Lean_PersistentHashMap_insert___redArg(v_x_66_, v_x_67_, v_s_68_, v_a_69_, v___x_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_erase___redArg(lean_object* v_x_72_, lean_object* v_x_73_, lean_object* v_s_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_PersistentHashMap_erase___redArg(v_x_72_, v_x_73_, v_s_74_, v_a_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_erase(lean_object* v_00_u03b1_77_, lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_s_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_PersistentHashMap_erase___redArg(v_x_78_, v_x_79_, v_s_80_, v_a_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f___redArg(lean_object* v_x_83_, lean_object* v_x_84_, lean_object* v_s_85_, lean_object* v_a_86_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_83_, v_x_84_, v_s_85_, v_a_86_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v___x_88_; 
v___x_88_ = lean_box(0);
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_97_; 
v_val_89_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_97_ == 0)
{
v___x_91_ = v___x_87_;
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_val_89_);
lean_dec(v___x_87_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_97_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v_fst_93_; lean_object* v___x_95_; 
v_fst_93_ = lean_ctor_get(v_val_89_, 0);
lean_inc(v_fst_93_);
lean_dec(v_val_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v_fst_93_);
v___x_95_ = v___x_91_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_fst_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f(lean_object* v_00_u03b1_98_, lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_s_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_99_, v_x_100_, v_s_101_, v_a_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v___x_104_; 
v___x_104_ = lean_box(0);
return v___x_104_;
}
else
{
lean_object* v_val_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_113_; 
v_val_105_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_113_ == 0)
{
v___x_107_ = v___x_103_;
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_val_105_);
lean_dec(v___x_103_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_113_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v_fst_109_; lean_object* v___x_111_; 
v_fst_109_ = lean_ctor_get(v_val_105_, 0);
lean_inc(v_fst_109_);
lean_dec(v_val_105_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 0, v_fst_109_);
v___x_111_ = v___x_107_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_fst_109_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___redArg(lean_object* v_x_114_, lean_object* v_x_115_, lean_object* v_s_116_, lean_object* v_a_117_, lean_object* v_a_u2080_118_){
_start:
{
lean_object* v___x_119_; uint64_t v___x_120_; size_t v___x_121_; lean_object* v___x_122_; 
lean_inc(v_a_117_);
v___x_119_ = lean_apply_1(v_x_115_, v_a_117_);
v___x_120_ = lean_unbox_uint64(v___x_119_);
lean_dec_ref(v___x_119_);
v___x_121_ = lean_uint64_to_usize(v___x_120_);
v___x_122_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_114_, v_s_116_, v___x_121_, v_a_117_, v_a_u2080_118_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___redArg___boxed(lean_object* v_x_123_, lean_object* v_x_124_, lean_object* v_s_125_, lean_object* v_a_126_, lean_object* v_a_u2080_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_PersistentHashSet_findD___redArg(v_x_123_, v_x_124_, v_s_125_, v_a_126_, v_a_u2080_127_);
lean_dec(v_a_u2080_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD(lean_object* v_00_u03b1_129_, lean_object* v_x_130_, lean_object* v_x_131_, lean_object* v_s_132_, lean_object* v_a_133_, lean_object* v_a_u2080_134_){
_start:
{
lean_object* v___x_135_; uint64_t v___x_136_; size_t v___x_137_; lean_object* v___x_138_; 
lean_inc(v_a_133_);
v___x_135_ = lean_apply_1(v_x_131_, v_a_133_);
v___x_136_ = lean_unbox_uint64(v___x_135_);
lean_dec_ref(v___x_135_);
v___x_137_ = lean_uint64_to_usize(v___x_136_);
v___x_138_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_130_, v_s_132_, v___x_137_, v_a_133_, v_a_u2080_134_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___boxed(lean_object* v_00_u03b1_139_, lean_object* v_x_140_, lean_object* v_x_141_, lean_object* v_s_142_, lean_object* v_a_143_, lean_object* v_a_u2080_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_Lean_PersistentHashSet_findD(v_00_u03b1_139_, v_x_140_, v_x_141_, v_s_142_, v_a_143_, v_a_u2080_144_);
lean_dec(v_a_u2080_144_);
return v_res_145_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_contains___redArg(lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_s_148_, lean_object* v_a_149_){
_start:
{
uint8_t v___x_150_; 
v___x_150_ = l_Lean_PersistentHashMap_contains___redArg(v_x_146_, v_x_147_, v_s_148_, v_a_149_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___redArg___boxed(lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_s_153_, lean_object* v_a_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Lean_PersistentHashSet_contains___redArg(v_x_151_, v_x_152_, v_s_153_, v_a_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_contains(lean_object* v_00_u03b1_157_, lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_s_160_, lean_object* v_a_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = l_Lean_PersistentHashMap_contains___redArg(v_x_158_, v_x_159_, v_s_160_, v_a_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___boxed(lean_object* v_00_u03b1_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_s_166_, lean_object* v_a_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Lean_PersistentHashSet_contains(v_00_u03b1_163_, v_x_164_, v_x_165_, v_s_166_, v_a_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg___lam__0(lean_object* v_f_170_, lean_object* v_d_171_, lean_object* v_a_172_, lean_object* v_x_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_apply_2(v_f_170_, v_d_171_, v_a_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg(lean_object* v_inst_175_, lean_object* v_f_176_, lean_object* v_init_177_, lean_object* v_s_178_){
_start:
{
lean_object* v___f_179_; lean_object* v___x_180_; 
v___f_179_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_179_, 0, v_f_176_);
v___x_180_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_175_, v___f_179_, v_s_178_, v_init_177_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM(lean_object* v_00_u03b1_181_, lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_00_u03b2_184_, lean_object* v_m_185_, lean_object* v_inst_186_, lean_object* v_f_187_, lean_object* v_init_188_, lean_object* v_s_189_){
_start:
{
lean_object* v___f_190_; lean_object* v___x_191_; 
v___f_190_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_190_, 0, v_f_187_);
v___x_191_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_186_, v___f_190_, v_s_189_, v_init_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___boxed(lean_object* v_00_u03b1_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_00_u03b2_195_, lean_object* v_m_196_, lean_object* v_inst_197_, lean_object* v_f_198_, lean_object* v_init_199_, lean_object* v_s_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_PersistentHashSet_foldM(v_00_u03b1_192_, v_x_193_, v_x_194_, v_00_u03b2_195_, v_m_196_, v_inst_197_, v_f_198_, v_init_199_, v_s_200_);
lean_dec_ref(v_x_194_);
lean_dec_ref(v_x_193_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___redArg(lean_object* v_f_221_, lean_object* v_init_222_, lean_object* v_s_223_){
_start:
{
lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___f_224_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_224_, 0, v_f_221_);
v___x_225_ = ((lean_object*)(l_Lean_PersistentHashSet_fold___redArg___closed__9));
v___x_226_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_225_, v___f_224_, v_s_223_, v_init_222_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold(lean_object* v_00_u03b1_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_00_u03b2_230_, lean_object* v_f_231_, lean_object* v_init_232_, lean_object* v_s_233_){
_start:
{
lean_object* v___f_234_; lean_object* v___x_235_; lean_object* v___x_236_; 
v___f_234_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_234_, 0, v_f_231_);
v___x_235_ = ((lean_object*)(l_Lean_PersistentHashSet_fold___redArg___closed__9));
v___x_236_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_235_, v___f_234_, v_s_233_, v_init_232_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___boxed(lean_object* v_00_u03b1_237_, lean_object* v_x_238_, lean_object* v_x_239_, lean_object* v_00_u03b2_240_, lean_object* v_f_241_, lean_object* v_init_242_, lean_object* v_s_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lean_PersistentHashSet_fold(v_00_u03b1_237_, v_x_238_, v_x_239_, v_00_u03b2_240_, v_f_241_, v_init_242_, v_s_243_);
lean_dec_ref(v_x_239_);
lean_dec_ref(v_x_238_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0(lean_object* v_x_245_){
_start:
{
lean_object* v_fst_246_; 
v_fst_246_ = lean_ctor_get(v_x_245_, 0);
lean_inc(v_fst_246_);
return v_fst_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0___boxed(lean_object* v_x_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_PersistentHashSet_toList___redArg___lam__0(v_x_247_);
lean_dec_ref(v_x_247_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg(lean_object* v_s_250_){
_start:
{
lean_object* v___f_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___f_251_ = ((lean_object*)(l_Lean_PersistentHashSet_toList___redArg___closed__0));
v___x_252_ = l_Lean_PersistentHashMap_toList___redArg(v_s_250_);
v___x_253_ = lean_box(0);
v___x_254_ = l_List_mapTR_loop___redArg(v___f_251_, v___x_252_, v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList(lean_object* v_00_u03b1_255_, lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_s_258_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_PersistentHashSet_toList___redArg(v_s_258_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___boxed(lean_object* v_00_u03b1_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_s_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lean_PersistentHashSet_toList(v_00_u03b1_260_, v_x_261_, v_x_262_, v_s_263_);
lean_dec_ref(v_x_262_);
lean_dec_ref(v_x_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg___lam__0(lean_object* v_f_265_, lean_object* v_p_266_, lean_object* v_s_267_){
_start:
{
lean_object* v_fst_268_; lean_object* v___x_269_; 
v_fst_268_ = lean_ctor_get(v_p_266_, 0);
lean_inc(v_fst_268_);
lean_dec_ref(v_p_266_);
v___x_269_ = lean_apply_2(v_f_265_, v_fst_268_, v_s_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg(lean_object* v_inst_270_, lean_object* v_s_271_, lean_object* v_init_272_, lean_object* v_f_273_){
_start:
{
lean_object* v___f_274_; lean_object* v___x_275_; 
v___f_274_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_forIn___redArg___lam__0), 3, 1);
lean_closure_set(v___f_274_, 0, v_f_273_);
v___x_275_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_270_, v_s_271_, v_init_272_, v___f_274_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn(lean_object* v_00_u03b1_276_, lean_object* v_m_277_, lean_object* v_00_u03c3_278_, lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_inst_281_, lean_object* v_s_282_, lean_object* v_init_283_, lean_object* v_f_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_281_, v_s_282_, v_init_283_, v_f_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___boxed(lean_object* v_00_u03b1_286_, lean_object* v_m_287_, lean_object* v_00_u03c3_288_, lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_inst_291_, lean_object* v_s_292_, lean_object* v_init_293_, lean_object* v_f_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_PersistentHashSet_forIn(v_00_u03b1_286_, v_m_287_, v_00_u03c3_288_, v_x_289_, v_x_290_, v_inst_291_, v_s_292_, v_init_293_, v_f_294_);
lean_dec_ref(v_x_290_);
lean_dec_ref(v_x_289_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(lean_object* v_inst_296_, lean_object* v_00_u03b2_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_296_, v___y_298_, v___y_299_, v___y_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg(lean_object* v_inst_302_){
_start:
{
lean_object* v___f_303_; 
v___f_303_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_303_, 0, v_inst_302_);
return v___f_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad(lean_object* v_00_u03b1_304_, lean_object* v_m_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_inst_308_){
_start:
{
lean_object* v___f_309_; 
v___f_309_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0), 5, 1);
lean_closure_set(v___f_309_, 0, v_inst_308_);
return v___f_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_310_, lean_object* v_m_311_, lean_object* v_x_312_, lean_object* v_x_313_, lean_object* v_inst_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_PersistentHashSet_instForInOfMonad(v_00_u03b1_310_, v_m_311_, v_x_312_, v_x_313_, v_inst_314_);
lean_dec_ref(v_x_313_);
lean_dec_ref(v_x_312_);
return v_res_315_;
}
}
lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_PersistentHashSet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_PersistentHashSet(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_PersistentHashSet(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_PersistentHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_PersistentHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_PersistentHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_PersistentHashSet(builtin);
}
#ifdef __cplusplus
}
#endif
