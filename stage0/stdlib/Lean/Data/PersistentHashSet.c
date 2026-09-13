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
lean_object* l_Lean_PersistentHashMap_empty___redArg();
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
static lean_once_cell_t l_Lean_PersistentHashSet_empty___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashSet_empty___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Lean_PersistentHashSet_empty___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_empty___redArg();
return v___x_1_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___redArg(){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_PersistentHashSet_empty___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty(lean_object* v_00_u03b1_6_, lean_object* v_inst_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___boxed(lean_object* v_00_u03b1_10_, lean_object* v_inst_11_, lean_object* v_inst_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean_PersistentHashSet_empty(v_00_u03b1_10_, v_inst_11_, v_inst_12_);
lean_dec_ref(v_inst_12_);
lean_dec_ref(v_inst_11_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___redArg___boxed(lean_object* v___dummy_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_PersistentHashSet_instInhabited___redArg();
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited(lean_object* v_00_u03b1_18_, lean_object* v_inst_19_, lean_object* v_inst_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___boxed(lean_object* v_00_u03b1_22_, lean_object* v_inst_23_, lean_object* v_inst_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Lean_PersistentHashSet_instInhabited(v_00_u03b1_22_, v_inst_23_, v_inst_24_);
lean_dec_ref(v_inst_24_);
lean_dec_ref(v_inst_23_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_PersistentHashSet_instEmptyCollection___redArg();
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection(lean_object* v_00_u03b1_30_, lean_object* v_inst_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_34_, lean_object* v_inst_35_, lean_object* v_inst_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_PersistentHashSet_instEmptyCollection(v_00_u03b1_34_, v_inst_35_, v_inst_36_);
lean_dec_ref(v_inst_36_);
lean_dec_ref(v_inst_35_);
return v_res_37_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_isEmpty___redArg(lean_object* v_s_38_){
_start:
{
uint8_t v___x_39_; 
v___x_39_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_s_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_isEmpty___redArg___boxed(lean_object* v_s_40_){
_start:
{
uint8_t v_res_41_; lean_object* v_r_42_; 
v_res_41_ = l_Lean_PersistentHashSet_isEmpty___redArg(v_s_40_);
lean_dec_ref(v_s_40_);
v_r_42_ = lean_box(v_res_41_);
return v_r_42_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_isEmpty(lean_object* v_00_u03b1_43_, lean_object* v_x_44_, lean_object* v_x_45_, lean_object* v_s_46_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_s_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_isEmpty___boxed(lean_object* v_00_u03b1_48_, lean_object* v_x_49_, lean_object* v_x_50_, lean_object* v_s_51_){
_start:
{
uint8_t v_res_52_; lean_object* v_r_53_; 
v_res_52_ = l_Lean_PersistentHashSet_isEmpty(v_00_u03b1_48_, v_x_49_, v_x_50_, v_s_51_);
lean_dec_ref(v_s_51_);
lean_dec_ref(v_x_50_);
lean_dec_ref(v_x_49_);
v_r_53_ = lean_box(v_res_52_);
return v_r_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_insert___redArg(lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_s_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = lean_box(0);
v___x_59_ = l_Lean_PersistentHashMap_insert___redArg(v_x_54_, v_x_55_, v_s_56_, v_a_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_insert(lean_object* v_00_u03b1_60_, lean_object* v_x_61_, lean_object* v_x_62_, lean_object* v_s_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_65_ = lean_box(0);
v___x_66_ = l_Lean_PersistentHashMap_insert___redArg(v_x_61_, v_x_62_, v_s_63_, v_a_64_, v___x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_erase___redArg(lean_object* v_x_67_, lean_object* v_x_68_, lean_object* v_s_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Lean_PersistentHashMap_erase___redArg(v_x_67_, v_x_68_, v_s_69_, v_a_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_erase(lean_object* v_00_u03b1_72_, lean_object* v_x_73_, lean_object* v_x_74_, lean_object* v_s_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Lean_PersistentHashMap_erase___redArg(v_x_73_, v_x_74_, v_s_75_, v_a_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f___redArg(lean_object* v_x_78_, lean_object* v_x_79_, lean_object* v_s_80_, lean_object* v_a_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_PersistentHashMap_findEntry_x3f___redArg(v_x_78_, v_x_79_, v_s_80_, v_a_81_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = lean_box(0);
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_92_; 
v_val_84_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_92_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_92_ == 0)
{
v___x_86_ = v___x_82_;
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_val_84_);
lean_dec(v___x_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_92_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
lean_object* v_fst_88_; lean_object* v___x_90_; 
v_fst_88_ = lean_ctor_get(v_val_84_, 0);
lean_inc(v_fst_88_);
lean_dec(v_val_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v_fst_88_);
v___x_90_ = v___x_86_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_fst_88_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f___redArg___boxed(lean_object* v_x_93_, lean_object* v_x_94_, lean_object* v_s_95_, lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_PersistentHashSet_find_x3f___redArg(v_x_93_, v_x_94_, v_s_95_, v_a_96_);
lean_dec_ref(v_s_95_);
return v_res_97_;
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_find_x3f___boxed(lean_object* v_00_u03b1_114_, lean_object* v_x_115_, lean_object* v_x_116_, lean_object* v_s_117_, lean_object* v_a_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_PersistentHashSet_find_x3f(v_00_u03b1_114_, v_x_115_, v_x_116_, v_s_117_, v_a_118_);
lean_dec_ref(v_s_117_);
return v_res_119_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___redArg(lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_s_122_, lean_object* v_a_123_, lean_object* v_a_u2080_124_){
_start:
{
lean_object* v___x_125_; uint64_t v___x_126_; size_t v___x_127_; lean_object* v___x_128_; 
lean_inc(v_a_123_);
v___x_125_ = lean_apply_1(v_x_121_, v_a_123_);
v___x_126_ = lean_unbox_uint64(v___x_125_);
lean_dec_ref(v___x_125_);
v___x_127_ = lean_uint64_to_usize(v___x_126_);
v___x_128_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_120_, v_s_122_, v___x_127_, v_a_123_, v_a_u2080_124_);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___redArg___boxed(lean_object* v_x_129_, lean_object* v_x_130_, lean_object* v_s_131_, lean_object* v_a_132_, lean_object* v_a_u2080_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_PersistentHashSet_findD___redArg(v_x_129_, v_x_130_, v_s_131_, v_a_132_, v_a_u2080_133_);
lean_dec(v_a_u2080_133_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD(lean_object* v_00_u03b1_135_, lean_object* v_x_136_, lean_object* v_x_137_, lean_object* v_s_138_, lean_object* v_a_139_, lean_object* v_a_u2080_140_){
_start:
{
lean_object* v___x_141_; uint64_t v___x_142_; size_t v___x_143_; lean_object* v___x_144_; 
lean_inc(v_a_139_);
v___x_141_ = lean_apply_1(v_x_137_, v_a_139_);
v___x_142_ = lean_unbox_uint64(v___x_141_);
lean_dec_ref(v___x_141_);
v___x_143_ = lean_uint64_to_usize(v___x_142_);
v___x_144_ = l_Lean_PersistentHashMap_findKeyDAux___redArg(v_x_136_, v_s_138_, v___x_143_, v_a_139_, v_a_u2080_140_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_findD___boxed(lean_object* v_00_u03b1_145_, lean_object* v_x_146_, lean_object* v_x_147_, lean_object* v_s_148_, lean_object* v_a_149_, lean_object* v_a_u2080_150_){
_start:
{
lean_object* v_res_151_; 
v_res_151_ = l_Lean_PersistentHashSet_findD(v_00_u03b1_145_, v_x_146_, v_x_147_, v_s_148_, v_a_149_, v_a_u2080_150_);
lean_dec(v_a_u2080_150_);
return v_res_151_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_contains___redArg(lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_s_154_, lean_object* v_a_155_){
_start:
{
uint8_t v___x_156_; 
v___x_156_ = l_Lean_PersistentHashMap_contains___redArg(v_x_152_, v_x_153_, v_s_154_, v_a_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___redArg___boxed(lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_s_159_, lean_object* v_a_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_PersistentHashSet_contains___redArg(v_x_157_, v_x_158_, v_s_159_, v_a_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashSet_contains(lean_object* v_00_u03b1_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_s_166_, lean_object* v_a_167_){
_start:
{
uint8_t v___x_168_; 
v___x_168_ = l_Lean_PersistentHashMap_contains___redArg(v_x_164_, v_x_165_, v_s_166_, v_a_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___boxed(lean_object* v_00_u03b1_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_s_172_, lean_object* v_a_173_){
_start:
{
uint8_t v_res_174_; lean_object* v_r_175_; 
v_res_174_ = l_Lean_PersistentHashSet_contains(v_00_u03b1_169_, v_x_170_, v_x_171_, v_s_172_, v_a_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg___lam__0(lean_object* v_f_176_, lean_object* v_d_177_, lean_object* v_a_178_, lean_object* v_x_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lean_apply_2(v_f_176_, v_d_177_, v_a_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg(lean_object* v_inst_181_, lean_object* v_f_182_, lean_object* v_init_183_, lean_object* v_s_184_){
_start:
{
lean_object* v___f_185_; lean_object* v___x_186_; 
v___f_185_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_185_, 0, v_f_182_);
v___x_186_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_181_, v___f_185_, v_s_184_, v_init_183_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM(lean_object* v_00_u03b1_187_, lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_00_u03b2_190_, lean_object* v_m_191_, lean_object* v_inst_192_, lean_object* v_f_193_, lean_object* v_init_194_, lean_object* v_s_195_){
_start:
{
lean_object* v___f_196_; lean_object* v___x_197_; 
v___f_196_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_196_, 0, v_f_193_);
v___x_197_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_192_, v___f_196_, v_s_195_, v_init_194_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___boxed(lean_object* v_00_u03b1_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_00_u03b2_201_, lean_object* v_m_202_, lean_object* v_inst_203_, lean_object* v_f_204_, lean_object* v_init_205_, lean_object* v_s_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_PersistentHashSet_foldM(v_00_u03b1_198_, v_x_199_, v_x_200_, v_00_u03b2_201_, v_m_202_, v_inst_203_, v_f_204_, v_init_205_, v_s_206_);
lean_dec_ref(v_x_200_);
lean_dec_ref(v_x_199_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___redArg(lean_object* v_f_227_, lean_object* v_init_228_, lean_object* v_s_229_){
_start:
{
lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v___f_230_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_230_, 0, v_f_227_);
v___x_231_ = ((lean_object*)(l_Lean_PersistentHashSet_fold___redArg___closed__9));
v___x_232_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_231_, v___f_230_, v_s_229_, v_init_228_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold(lean_object* v_00_u03b1_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_00_u03b2_236_, lean_object* v_f_237_, lean_object* v_init_238_, lean_object* v_s_239_){
_start:
{
lean_object* v___f_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___f_240_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_240_, 0, v_f_237_);
v___x_241_ = ((lean_object*)(l_Lean_PersistentHashSet_fold___redArg___closed__9));
v___x_242_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_241_, v___f_240_, v_s_239_, v_init_238_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___boxed(lean_object* v_00_u03b1_243_, lean_object* v_x_244_, lean_object* v_x_245_, lean_object* v_00_u03b2_246_, lean_object* v_f_247_, lean_object* v_init_248_, lean_object* v_s_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_PersistentHashSet_fold(v_00_u03b1_243_, v_x_244_, v_x_245_, v_00_u03b2_246_, v_f_247_, v_init_248_, v_s_249_);
lean_dec_ref(v_x_245_);
lean_dec_ref(v_x_244_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0(lean_object* v_x_251_){
_start:
{
lean_object* v_fst_252_; 
v_fst_252_ = lean_ctor_get(v_x_251_, 0);
lean_inc(v_fst_252_);
return v_fst_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0___boxed(lean_object* v_x_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_PersistentHashSet_toList___redArg___lam__0(v_x_253_);
lean_dec_ref(v_x_253_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg(lean_object* v_s_256_){
_start:
{
lean_object* v___f_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___f_257_ = ((lean_object*)(l_Lean_PersistentHashSet_toList___redArg___closed__0));
v___x_258_ = l_Lean_PersistentHashMap_toList___redArg(v_s_256_);
v___x_259_ = lean_box(0);
v___x_260_ = l_List_mapTR_loop___redArg(v___f_257_, v___x_258_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList(lean_object* v_00_u03b1_261_, lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_s_264_){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_PersistentHashSet_toList___redArg(v_s_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___boxed(lean_object* v_00_u03b1_266_, lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_s_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_PersistentHashSet_toList(v_00_u03b1_266_, v_x_267_, v_x_268_, v_s_269_);
lean_dec_ref(v_x_268_);
lean_dec_ref(v_x_267_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg___lam__0(lean_object* v_f_271_, lean_object* v_p_272_, lean_object* v_s_273_){
_start:
{
lean_object* v_fst_274_; lean_object* v___x_275_; 
v_fst_274_ = lean_ctor_get(v_p_272_, 0);
lean_inc(v_fst_274_);
lean_dec_ref(v_p_272_);
v___x_275_ = lean_apply_2(v_f_271_, v_fst_274_, v_s_273_);
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg(lean_object* v_inst_276_, lean_object* v_s_277_, lean_object* v_init_278_, lean_object* v_f_279_){
_start:
{
lean_object* v___f_280_; lean_object* v___x_281_; 
v___f_280_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_forIn___redArg___lam__0), 3, 1);
lean_closure_set(v___f_280_, 0, v_f_279_);
v___x_281_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_276_, v_s_277_, v_init_278_, v___f_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg___boxed(lean_object* v_inst_282_, lean_object* v_s_283_, lean_object* v_init_284_, lean_object* v_f_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_282_, v_s_283_, v_init_284_, v_f_285_);
lean_dec_ref(v_s_283_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn(lean_object* v_00_u03b1_287_, lean_object* v_m_288_, lean_object* v_00_u03c3_289_, lean_object* v_x_290_, lean_object* v_x_291_, lean_object* v_inst_292_, lean_object* v_s_293_, lean_object* v_init_294_, lean_object* v_f_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_292_, v_s_293_, v_init_294_, v_f_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___boxed(lean_object* v_00_u03b1_297_, lean_object* v_m_298_, lean_object* v_00_u03c3_299_, lean_object* v_x_300_, lean_object* v_x_301_, lean_object* v_inst_302_, lean_object* v_s_303_, lean_object* v_init_304_, lean_object* v_f_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_PersistentHashSet_forIn(v_00_u03b1_297_, v_m_298_, v_00_u03c3_299_, v_x_300_, v_x_301_, v_inst_302_, v_s_303_, v_init_304_, v_f_305_);
lean_dec_ref(v_s_303_);
lean_dec_ref(v_x_301_);
lean_dec_ref(v_x_300_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(lean_object* v_inst_307_, lean_object* v_00_u03b2_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_307_, v___y_309_, v___y_310_, v___y_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed(lean_object* v_inst_313_, lean_object* v_00_u03b2_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(v_inst_313_, v_00_u03b2_314_, v___y_315_, v___y_316_, v___y_317_);
lean_dec_ref(v___y_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg(lean_object* v_inst_319_){
_start:
{
lean_object* v___f_320_; 
v___f_320_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_320_, 0, v_inst_319_);
return v___f_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad(lean_object* v_00_u03b1_321_, lean_object* v_m_322_, lean_object* v_x_323_, lean_object* v_x_324_, lean_object* v_inst_325_){
_start:
{
lean_object* v___f_326_; 
v___f_326_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_326_, 0, v_inst_325_);
return v___f_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_327_, lean_object* v_m_328_, lean_object* v_x_329_, lean_object* v_x_330_, lean_object* v_inst_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_PersistentHashSet_instForInOfMonad(v_00_u03b1_327_, v_m_328_, v_x_329_, v_x_330_, v_inst_331_);
lean_dec_ref(v_x_330_);
lean_dec_ref(v_x_329_);
return v_res_332_;
}
}
lean_object* runtime_initialize_Lean_Data_PersistentHashMap(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_PersistentHashSet(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
