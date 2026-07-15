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
lean_object* l_Lean_PersistentHashMap_findEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f___redArg___boxed(lean_object* v_x_98_, lean_object* v_x_99_, lean_object* v_s_100_, lean_object* v_a_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_PersistentHashSet_find_x3f___redArg(v_x_98_, v_x_99_, v_s_100_, v_a_101_);
lean_dec_ref(v_s_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f(lean_object* v_00_u03b1_103_, lean_object* v_x_104_, lean_object* v_x_105_, lean_object* v_s_106_, lean_object* v_a_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_104_, v_x_105_, v_s_106_, v_a_107_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v___x_109_; 
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
lean_object* v_val_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_118_; 
v_val_110_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_118_ == 0)
{
v___x_112_ = v___x_108_;
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_val_110_);
lean_dec(v___x_108_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_118_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_fst_114_; lean_object* v___x_116_; 
v_fst_114_ = lean_ctor_get(v_val_110_, 0);
lean_inc(v_fst_114_);
lean_dec(v_val_110_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v_fst_114_);
v___x_116_ = v___x_112_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_fst_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f___boxed(lean_object* v_00_u03b1_119_, lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_s_122_, lean_object* v_a_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_PersistentHashSet_find_x3f(v_00_u03b1_119_, v_x_120_, v_x_121_, v_s_122_, v_a_123_);
lean_dec_ref(v_s_122_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___redArg(lean_object* v_x_125_, lean_object* v_x_126_, lean_object* v_s_127_, lean_object* v_a_128_, lean_object* v_a_u2080_129_){
_start:
{
lean_object* v___x_130_; uint64_t v___x_131_; size_t v___x_132_; lean_object* v___x_133_; 
lean_inc(v_a_128_);
v___x_130_ = lean_apply_1(v_x_126_, v_a_128_);
v___x_131_ = lean_unbox_uint64(v___x_130_);
lean_dec_ref(v___x_130_);
v___x_132_ = lean_uint64_to_usize(v___x_131_);
v___x_133_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_125_, v_s_127_, v___x_132_, v_a_128_, v_a_u2080_129_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___redArg___boxed(lean_object* v_x_134_, lean_object* v_x_135_, lean_object* v_s_136_, lean_object* v_a_137_, lean_object* v_a_u2080_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_PersistentHashSet_findD___redArg(v_x_134_, v_x_135_, v_s_136_, v_a_137_, v_a_u2080_138_);
lean_dec(v_a_u2080_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD(lean_object* v_00_u03b1_140_, lean_object* v_x_141_, lean_object* v_x_142_, lean_object* v_s_143_, lean_object* v_a_144_, lean_object* v_a_u2080_145_){
_start:
{
lean_object* v___x_146_; uint64_t v___x_147_; size_t v___x_148_; lean_object* v___x_149_; 
lean_inc(v_a_144_);
v___x_146_ = lean_apply_1(v_x_142_, v_a_144_);
v___x_147_ = lean_unbox_uint64(v___x_146_);
lean_dec_ref(v___x_146_);
v___x_148_ = lean_uint64_to_usize(v___x_147_);
v___x_149_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_141_, v_s_143_, v___x_148_, v_a_144_, v_a_u2080_145_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___boxed(lean_object* v_00_u03b1_150_, lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_s_153_, lean_object* v_a_154_, lean_object* v_a_u2080_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_PersistentHashSet_findD(v_00_u03b1_150_, v_x_151_, v_x_152_, v_s_153_, v_a_154_, v_a_u2080_155_);
lean_dec(v_a_u2080_155_);
return v_res_156_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_contains___redArg(lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_s_159_, lean_object* v_a_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = l_Lean_PersistentHashMap_contains___redArg(v_x_157_, v_x_158_, v_s_159_, v_a_160_);
return v___x_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___redArg___boxed(lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_s_164_, lean_object* v_a_165_){
_start:
{
uint8_t v_res_166_; lean_object* v_r_167_; 
v_res_166_ = l_Lean_PersistentHashSet_contains___redArg(v_x_162_, v_x_163_, v_s_164_, v_a_165_);
v_r_167_ = lean_box(v_res_166_);
return v_r_167_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_contains(lean_object* v_00_u03b1_168_, lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_s_171_, lean_object* v_a_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = l_Lean_PersistentHashMap_contains___redArg(v_x_169_, v_x_170_, v_s_171_, v_a_172_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___boxed(lean_object* v_00_u03b1_174_, lean_object* v_x_175_, lean_object* v_x_176_, lean_object* v_s_177_, lean_object* v_a_178_){
_start:
{
uint8_t v_res_179_; lean_object* v_r_180_; 
v_res_179_ = l_Lean_PersistentHashSet_contains(v_00_u03b1_174_, v_x_175_, v_x_176_, v_s_177_, v_a_178_);
v_r_180_ = lean_box(v_res_179_);
return v_r_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg___lam__0(lean_object* v_f_181_, lean_object* v_d_182_, lean_object* v_a_183_, lean_object* v_x_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = lean_apply_2(v_f_181_, v_d_182_, v_a_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg(lean_object* v_inst_186_, lean_object* v_f_187_, lean_object* v_init_188_, lean_object* v_s_189_){
_start:
{
lean_object* v___f_190_; lean_object* v___x_191_; 
v___f_190_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_190_, 0, v_f_187_);
v___x_191_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_186_, v___f_190_, v_s_189_, v_init_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM(lean_object* v_00_u03b1_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_00_u03b2_195_, lean_object* v_m_196_, lean_object* v_inst_197_, lean_object* v_f_198_, lean_object* v_init_199_, lean_object* v_s_200_){
_start:
{
lean_object* v___f_201_; lean_object* v___x_202_; 
v___f_201_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_201_, 0, v_f_198_);
v___x_202_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_197_, v___f_201_, v_s_200_, v_init_199_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___boxed(lean_object* v_00_u03b1_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_00_u03b2_206_, lean_object* v_m_207_, lean_object* v_inst_208_, lean_object* v_f_209_, lean_object* v_init_210_, lean_object* v_s_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_Lean_PersistentHashSet_foldM(v_00_u03b1_203_, v_x_204_, v_x_205_, v_00_u03b2_206_, v_m_207_, v_inst_208_, v_f_209_, v_init_210_, v_s_211_);
lean_dec_ref(v_x_205_);
lean_dec_ref(v_x_204_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___redArg(lean_object* v_f_232_, lean_object* v_init_233_, lean_object* v_s_234_){
_start:
{
lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___f_235_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_235_, 0, v_f_232_);
v___x_236_ = ((lean_object*)(l_Lean_PersistentHashSet_fold___redArg___closed__9));
v___x_237_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_236_, v___f_235_, v_s_234_, v_init_233_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold(lean_object* v_00_u03b1_238_, lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_00_u03b2_241_, lean_object* v_f_242_, lean_object* v_init_243_, lean_object* v_s_244_){
_start:
{
lean_object* v___f_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___f_245_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_245_, 0, v_f_242_);
v___x_246_ = ((lean_object*)(l_Lean_PersistentHashSet_fold___redArg___closed__9));
v___x_247_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_246_, v___f_245_, v_s_244_, v_init_243_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___boxed(lean_object* v_00_u03b1_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_00_u03b2_251_, lean_object* v_f_252_, lean_object* v_init_253_, lean_object* v_s_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_PersistentHashSet_fold(v_00_u03b1_248_, v_x_249_, v_x_250_, v_00_u03b2_251_, v_f_252_, v_init_253_, v_s_254_);
lean_dec_ref(v_x_250_);
lean_dec_ref(v_x_249_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0(lean_object* v_x_256_){
_start:
{
lean_object* v_fst_257_; 
v_fst_257_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_fst_257_);
return v_fst_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0___boxed(lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_PersistentHashSet_toList___redArg___lam__0(v_x_258_);
lean_dec_ref(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg(lean_object* v_s_261_){
_start:
{
lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___f_262_ = ((lean_object*)(l_Lean_PersistentHashSet_toList___redArg___closed__0));
v___x_263_ = l_Lean_PersistentHashMap_toList___redArg(v_s_261_);
v___x_264_ = lean_box(0);
v___x_265_ = l_List_mapTR_loop___redArg(v___f_262_, v___x_263_, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList(lean_object* v_00_u03b1_266_, lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_s_269_){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_PersistentHashSet_toList___redArg(v_s_269_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___boxed(lean_object* v_00_u03b1_271_, lean_object* v_x_272_, lean_object* v_x_273_, lean_object* v_s_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_PersistentHashSet_toList(v_00_u03b1_271_, v_x_272_, v_x_273_, v_s_274_);
lean_dec_ref(v_x_273_);
lean_dec_ref(v_x_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg___lam__0(lean_object* v_f_276_, lean_object* v_p_277_, lean_object* v_s_278_){
_start:
{
lean_object* v_fst_279_; lean_object* v___x_280_; 
v_fst_279_ = lean_ctor_get(v_p_277_, 0);
lean_inc(v_fst_279_);
lean_dec_ref(v_p_277_);
v___x_280_ = lean_apply_2(v_f_276_, v_fst_279_, v_s_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg(lean_object* v_inst_281_, lean_object* v_s_282_, lean_object* v_init_283_, lean_object* v_f_284_){
_start:
{
lean_object* v___f_285_; lean_object* v___x_286_; 
v___f_285_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_forIn___redArg___lam__0), 3, 1);
lean_closure_set(v___f_285_, 0, v_f_284_);
v___x_286_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_281_, v_s_282_, v_init_283_, v___f_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg___boxed(lean_object* v_inst_287_, lean_object* v_s_288_, lean_object* v_init_289_, lean_object* v_f_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_287_, v_s_288_, v_init_289_, v_f_290_);
lean_dec_ref(v_s_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn(lean_object* v_00_u03b1_292_, lean_object* v_m_293_, lean_object* v_00_u03c3_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_inst_297_, lean_object* v_s_298_, lean_object* v_init_299_, lean_object* v_f_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_297_, v_s_298_, v_init_299_, v_f_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___boxed(lean_object* v_00_u03b1_302_, lean_object* v_m_303_, lean_object* v_00_u03c3_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_inst_307_, lean_object* v_s_308_, lean_object* v_init_309_, lean_object* v_f_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_PersistentHashSet_forIn(v_00_u03b1_302_, v_m_303_, v_00_u03c3_304_, v_x_305_, v_x_306_, v_inst_307_, v_s_308_, v_init_309_, v_f_310_);
lean_dec_ref(v_s_308_);
lean_dec_ref(v_x_306_);
lean_dec_ref(v_x_305_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(lean_object* v_inst_312_, lean_object* v_00_u03b2_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_312_, v___y_314_, v___y_315_, v___y_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed(lean_object* v_inst_318_, lean_object* v_00_u03b2_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(v_inst_318_, v_00_u03b2_319_, v___y_320_, v___y_321_, v___y_322_);
lean_dec_ref(v___y_320_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg(lean_object* v_inst_324_){
_start:
{
lean_object* v___f_325_; 
v___f_325_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_325_, 0, v_inst_324_);
return v___f_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad(lean_object* v_00_u03b1_326_, lean_object* v_m_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_inst_330_){
_start:
{
lean_object* v___f_331_; 
v___f_331_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_331_, 0, v_inst_330_);
return v___f_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_332_, lean_object* v_m_333_, lean_object* v_x_334_, lean_object* v_x_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_PersistentHashSet_instForInOfMonad(v_00_u03b1_332_, v_m_333_, v_x_334_, v_x_335_, v_inst_336_);
lean_dec_ref(v_x_335_);
lean_dec_ref(v_x_334_);
return v_res_337_;
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
