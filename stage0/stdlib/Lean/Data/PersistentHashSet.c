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
lean_object* l_Lean_PersistentHashSet_empty___redArg(){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_3_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashSet_empty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4_;
v_res_4_ = l_Lean_PersistentHashSet_empty___redArg();
stack->m_obj
 = v_res_4_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty___redArg___boxed(lean_object* v___dummy_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Lean_PersistentHashSet_empty___redArg();
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_empty(lean_object* v_00_u03b1_7_, lean_object* v_inst_8_, lean_object* v_inst_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
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
lean_object* l_Lean_PersistentHashSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_16_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashSet_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_17_;
v_res_17_ = l_Lean_PersistentHashSet_instInhabited___redArg();
stack->m_obj
 = v_res_17_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___redArg___boxed(lean_object* v___dummy_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lean_PersistentHashSet_instInhabited___redArg();
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited(lean_object* v_00_u03b1_20_, lean_object* v_inst_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instInhabited___boxed(lean_object* v_00_u03b1_24_, lean_object* v_inst_25_, lean_object* v_inst_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = l_Lean_PersistentHashSet_instInhabited(v_00_u03b1_24_, v_inst_25_, v_inst_26_);
lean_dec_ref(v_inst_26_);
lean_dec_ref(v_inst_25_);
return v_res_27_;
}
}
lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_29_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashSet_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_30_;
v_res_30_ = l_Lean_PersistentHashSet_instEmptyCollection___redArg();
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_PersistentHashSet_instEmptyCollection___redArg();
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection(lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_inst_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Lean_PersistentHashSet_empty___redArg___closed__0, &l_Lean_PersistentHashSet_empty___redArg___closed__0_once, _init_l_Lean_PersistentHashSet_empty___redArg___closed__0);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_PersistentHashSet_instEmptyCollection(v_00_u03b1_37_, v_inst_38_, v_inst_39_);
lean_dec_ref(v_inst_39_);
lean_dec_ref(v_inst_38_);
return v_res_40_;
}
}
uint8_t l_Lean_PersistentHashSet_isEmpty___redArg(lean_object* v_s_41_){
_start:
{
uint8_t v___x_42_; 
v___x_42_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_s_41_);
return v___x_42_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashSet_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_41_ = stack[0].m_obj;
uint8_t v_res_43_;
v_res_43_ = l_Lean_PersistentHashSet_isEmpty___redArg(v_s_41_);
stack->m_num = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_isEmpty___redArg___boxed(lean_object* v_s_44_){
_start:
{
uint8_t v_res_45_; lean_object* v_r_46_; 
v_res_45_ = l_Lean_PersistentHashSet_isEmpty___redArg(v_s_44_);
lean_dec_ref(v_s_44_);
v_r_46_ = lean_box(v_res_45_);
return v_r_46_;
}
}
uint8_t l_Lean_PersistentHashSet_isEmpty(lean_object* v_00_u03b1_47_, lean_object* v_x_48_, lean_object* v_x_49_, lean_object* v_s_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_s_50_);
return v___x_51_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashSet_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_48_ = stack[1].m_obj;
lean_object* v_x_49_ = stack[2].m_obj;
lean_object* v_s_50_ = stack[3].m_obj;
uint8_t v_res_52_;
v_res_52_ = l_Lean_PersistentHashSet_isEmpty(lean_box(0), v_x_48_, v_x_49_, v_s_50_);
stack->m_num = v_res_52_;
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
uint8_t l_Lean_PersistentHashSet_contains___redArg(lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_s_159_, lean_object* v_a_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = l_Lean_PersistentHashMap_contains___redArg(v_x_157_, v_x_158_, v_s_159_, v_a_160_);
return v___x_161_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashSet_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_157_ = stack[0].m_obj;
lean_object* v_x_158_ = stack[1].m_obj;
lean_object* v_s_159_ = stack[2].m_obj;
lean_object* v_a_160_ = stack[3].m_obj;
uint8_t v_res_162_;
v_res_162_ = l_Lean_PersistentHashSet_contains___redArg(v_x_157_, v_x_158_, v_s_159_, v_a_160_);
stack->m_num = v_res_162_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___redArg___boxed(lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_s_165_, lean_object* v_a_166_){
_start:
{
uint8_t v_res_167_; lean_object* v_r_168_; 
v_res_167_ = l_Lean_PersistentHashSet_contains___redArg(v_x_163_, v_x_164_, v_s_165_, v_a_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
uint8_t l_Lean_PersistentHashSet_contains(lean_object* v_00_u03b1_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_s_172_, lean_object* v_a_173_){
_start:
{
uint8_t v___x_174_; 
v___x_174_ = l_Lean_PersistentHashMap_contains___redArg(v_x_170_, v_x_171_, v_s_172_, v_a_173_);
return v___x_174_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_170_ = stack[1].m_obj;
lean_object* v_x_171_ = stack[2].m_obj;
lean_object* v_s_172_ = stack[3].m_obj;
lean_object* v_a_173_ = stack[4].m_obj;
uint8_t v_res_175_;
v_res_175_ = l_Lean_PersistentHashSet_contains(lean_box(0), v_x_170_, v_x_171_, v_s_172_, v_a_173_);
stack->m_num = v_res_175_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_contains___boxed(lean_object* v_00_u03b1_176_, lean_object* v_x_177_, lean_object* v_x_178_, lean_object* v_s_179_, lean_object* v_a_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Lean_PersistentHashSet_contains(v_00_u03b1_176_, v_x_177_, v_x_178_, v_s_179_, v_a_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg___lam__0(lean_object* v_f_183_, lean_object* v_d_184_, lean_object* v_a_185_, lean_object* v_x_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = lean_apply_2(v_f_183_, v_d_184_, v_a_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___redArg(lean_object* v_inst_188_, lean_object* v_f_189_, lean_object* v_init_190_, lean_object* v_s_191_){
_start:
{
lean_object* v___f_192_; lean_object* v___x_193_; 
v___f_192_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_192_, 0, v_f_189_);
v___x_193_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_188_, v___f_192_, v_s_191_, v_init_190_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM(lean_object* v_00_u03b1_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_00_u03b2_197_, lean_object* v_m_198_, lean_object* v_inst_199_, lean_object* v_f_200_, lean_object* v_init_201_, lean_object* v_s_202_){
_start:
{
lean_object* v___f_203_; lean_object* v___x_204_; 
v___f_203_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_203_, 0, v_f_200_);
v___x_204_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v_inst_199_, v___f_203_, v_s_202_, v_init_201_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_foldM___boxed(lean_object* v_00_u03b1_205_, lean_object* v_x_206_, lean_object* v_x_207_, lean_object* v_00_u03b2_208_, lean_object* v_m_209_, lean_object* v_inst_210_, lean_object* v_f_211_, lean_object* v_init_212_, lean_object* v_s_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_PersistentHashSet_foldM(v_00_u03b1_205_, v_x_206_, v_x_207_, v_00_u03b2_208_, v_m_209_, v_inst_210_, v_f_211_, v_init_212_, v_s_213_);
lean_dec_ref(v_x_207_);
lean_dec_ref(v_x_206_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___redArg(lean_object* v_f_234_, lean_object* v_init_235_, lean_object* v_s_236_){
_start:
{
lean_object* v___f_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v___f_237_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_237_, 0, v_f_234_);
v___x_238_ = ((lean_object*)(l_Lean_PersistentHashSet_fold___redArg___closed__9));
v___x_239_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_238_, v___f_237_, v_s_236_, v_init_235_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold(lean_object* v_00_u03b1_240_, lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_00_u03b2_243_, lean_object* v_f_244_, lean_object* v_init_245_, lean_object* v_s_246_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___f_247_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_247_, 0, v_f_244_);
v___x_248_ = ((lean_object*)(l_Lean_PersistentHashSet_fold___redArg___closed__9));
v___x_249_ = l_Lean_PersistentHashMap_foldlMAux___redArg(v___x_248_, v___f_247_, v_s_246_, v_init_245_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_fold___boxed(lean_object* v_00_u03b1_250_, lean_object* v_x_251_, lean_object* v_x_252_, lean_object* v_00_u03b2_253_, lean_object* v_f_254_, lean_object* v_init_255_, lean_object* v_s_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_PersistentHashSet_fold(v_00_u03b1_250_, v_x_251_, v_x_252_, v_00_u03b2_253_, v_f_254_, v_init_255_, v_s_256_);
lean_dec_ref(v_x_252_);
lean_dec_ref(v_x_251_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0(lean_object* v_x_258_){
_start:
{
lean_object* v_fst_259_; 
v_fst_259_ = lean_ctor_get(v_x_258_, 0);
lean_inc(v_fst_259_);
return v_fst_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg___lam__0___boxed(lean_object* v_x_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_PersistentHashSet_toList___redArg___lam__0(v_x_260_);
lean_dec_ref(v_x_260_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___redArg(lean_object* v_s_263_){
_start:
{
lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___f_264_ = ((lean_object*)(l_Lean_PersistentHashSet_toList___redArg___closed__0));
v___x_265_ = l_Lean_PersistentHashMap_toList___redArg(v_s_263_);
v___x_266_ = lean_box(0);
v___x_267_ = l_List_mapTR_loop___redArg(v___f_264_, v___x_265_, v___x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList(lean_object* v_00_u03b1_268_, lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_s_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_PersistentHashSet_toList___redArg(v_s_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_toList___boxed(lean_object* v_00_u03b1_273_, lean_object* v_x_274_, lean_object* v_x_275_, lean_object* v_s_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_PersistentHashSet_toList(v_00_u03b1_273_, v_x_274_, v_x_275_, v_s_276_);
lean_dec_ref(v_x_275_);
lean_dec_ref(v_x_274_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg___lam__0(lean_object* v_f_278_, lean_object* v_p_279_, lean_object* v_s_280_){
_start:
{
lean_object* v_fst_281_; lean_object* v___x_282_; 
v_fst_281_ = lean_ctor_get(v_p_279_, 0);
lean_inc(v_fst_281_);
lean_dec_ref(v_p_279_);
v___x_282_ = lean_apply_2(v_f_278_, v_fst_281_, v_s_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg(lean_object* v_inst_283_, lean_object* v_s_284_, lean_object* v_init_285_, lean_object* v_f_286_){
_start:
{
lean_object* v___f_287_; lean_object* v___x_288_; 
v___f_287_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_forIn___redArg___lam__0), 3, 1);
lean_closure_set(v___f_287_, 0, v_f_286_);
v___x_288_ = l_Lean_PersistentHashMap_forIn___redArg(v_inst_283_, v_s_284_, v_init_285_, v___f_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___redArg___boxed(lean_object* v_inst_289_, lean_object* v_s_290_, lean_object* v_init_291_, lean_object* v_f_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_289_, v_s_290_, v_init_291_, v_f_292_);
lean_dec_ref(v_s_290_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn(lean_object* v_00_u03b1_294_, lean_object* v_m_295_, lean_object* v_00_u03c3_296_, lean_object* v_x_297_, lean_object* v_x_298_, lean_object* v_inst_299_, lean_object* v_s_300_, lean_object* v_init_301_, lean_object* v_f_302_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_299_, v_s_300_, v_init_301_, v_f_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_forIn___boxed(lean_object* v_00_u03b1_304_, lean_object* v_m_305_, lean_object* v_00_u03c3_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_inst_309_, lean_object* v_s_310_, lean_object* v_init_311_, lean_object* v_f_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_PersistentHashSet_forIn(v_00_u03b1_304_, v_m_305_, v_00_u03c3_306_, v_x_307_, v_x_308_, v_inst_309_, v_s_310_, v_init_311_, v_f_312_);
lean_dec_ref(v_s_310_);
lean_dec_ref(v_x_308_);
lean_dec_ref(v_x_307_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(lean_object* v_inst_314_, lean_object* v_00_u03b2_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_PersistentHashSet_forIn___redArg(v_inst_314_, v___y_316_, v___y_317_, v___y_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed(lean_object* v_inst_320_, lean_object* v_00_u03b2_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0(v_inst_320_, v_00_u03b2_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec_ref(v___y_322_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___redArg(lean_object* v_inst_326_){
_start:
{
lean_object* v___f_327_; 
v___f_327_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_327_, 0, v_inst_326_);
return v___f_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad(lean_object* v_00_u03b1_328_, lean_object* v_m_329_, lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_inst_332_){
_start:
{
lean_object* v___f_333_; 
v___f_333_ = lean_alloc_closure((void*)(l_Lean_PersistentHashSet_instForInOfMonad___redArg___lam__0___boxed), 5, 1);
lean_closure_set(v___f_333_, 0, v_inst_332_);
return v___f_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_334_, lean_object* v_m_335_, lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_inst_338_){
_start:
{
lean_object* v_res_339_; 
v_res_339_ = l_Lean_PersistentHashSet_instForInOfMonad(v_00_u03b1_334_, v_m_335_, v_x_336_, v_x_337_, v_inst_338_);
lean_dec_ref(v_x_337_);
lean_dec_ref(v_x_336_);
return v_res_339_;
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
