// Lean compiler output
// Module: Init.Data.List.Perm
// Imports: import all Init.Data.List.Attach public import Init.Data.List.Attach import Init.Data.List.Erase import Init.Data.List.Pairwise import Init.Data.List.Sublist import Init.Data.List.TakeDrop import Init.Data.Nat.Lemmas
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
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isPerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_instTransPerm___redArg();
LEAN_EXPORT lean_object* l_List_instTransPerm___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_instTransPerm(lean_object*);
LEAN_EXPORT lean_object* l_List_isSetoid___redArg();
LEAN_EXPORT lean_object* l_List_isSetoid___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_isSetoid(lean_object*);
LEAN_EXPORT uint8_t l_List_decidablePerm___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidablePerm___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_decidablePerm(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_decidablePerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instTransPerm___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_List_instTransPerm___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_List_instTransPerm___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_List_instTransPerm___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_List_instTransPerm___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_List_instTransPerm(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
lean_object* l_List_isSetoid___redArg(){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT void l_List_isSetoid___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_10_;
v_res_10_ = l_List_isSetoid___redArg();
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_List_isSetoid___redArg___boxed(lean_object* v___dummy_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_List_isSetoid___redArg();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_List_isSetoid(lean_object* v_00_u03b1_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_box(0);
return v___x_14_;
}
}
uint8_t l_List_decidablePerm___redArg(lean_object* v_inst_15_, lean_object* v_l_u2081_16_, lean_object* v_l_u2082_17_){
_start:
{
lean_object* v___f_18_; uint8_t v___x_19_; 
v___f_18_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_18_, 0, v_inst_15_);
v___x_19_ = l_List_isPerm___redArg(v___f_18_, v_l_u2081_16_, v_l_u2082_17_);
return v___x_19_;
}
}
LEAN_EXPORT void l_List_decidablePerm___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_15_ = stack[0].m_obj;
lean_object* v_l_u2081_16_ = stack[1].m_obj;
lean_object* v_l_u2082_17_ = stack[2].m_obj;
uint8_t v_res_20_;
v_res_20_ = l_List_decidablePerm___redArg(v_inst_15_, v_l_u2081_16_, v_l_u2082_17_);
stack->m_num = v_res_20_;
}
LEAN_EXPORT lean_object* l_List_decidablePerm___redArg___boxed(lean_object* v_inst_21_, lean_object* v_l_u2081_22_, lean_object* v_l_u2082_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_List_decidablePerm___redArg(v_inst_21_, v_l_u2081_22_, v_l_u2082_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
uint8_t l_List_decidablePerm(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_l_u2081_28_, lean_object* v_l_u2082_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = l_List_decidablePerm___redArg(v_inst_27_, v_l_u2081_28_, v_l_u2082_29_);
return v___x_30_;
}
}
LEAN_EXPORT void l_List_decidablePerm_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_27_ = stack[1].m_obj;
lean_object* v_l_u2081_28_ = stack[2].m_obj;
lean_object* v_l_u2082_29_ = stack[3].m_obj;
uint8_t v_res_31_;
v_res_31_ = l_List_decidablePerm(lean_box(0), v_inst_27_, v_l_u2081_28_, v_l_u2082_29_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l_List_decidablePerm___boxed(lean_object* v_00_u03b1_32_, lean_object* v_inst_33_, lean_object* v_l_u2081_34_, lean_object* v_l_u2082_35_){
_start:
{
uint8_t v_res_36_; lean_object* v_r_37_; 
v_res_36_ = l_List_decidablePerm(v_00_u03b1_32_, v_inst_33_, v_l_u2081_34_, v_l_u2082_35_);
v_r_37_ = lean_box(v_res_36_);
return v_r_37_;
}
}
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Perm(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Perm(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Perm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Perm(builtin);
}
#ifdef __cplusplus
}
#endif
