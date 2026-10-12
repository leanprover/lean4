// Lean compiler output
// Module: Init.Data.List.Nat.Count
// Imports: public import Init.GetElem import Init.ByCases import Init.Data.Bool import Init.Data.List.Count import Init.Data.List.Lemmas import Init.Data.List.Sublist import Init.Data.Nat.Lemmas import Init.Data.Nat.MinMax import Init.Omega
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
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg(uint8_t v_x_1_, lean_object* v_h__1_2_, lean_object* v_h__2_3_){
_start:
{
if (v_x_1_ == 0)
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_dec(v_h__1_2_);
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_h__2_3_, v___x_4_);
return v___x_5_;
}
else
{
lean_object* v___x_6_; lean_object* v___x_7_; 
lean_dec(v_h__2_3_);
v___x_6_ = lean_box(0);
v___x_7_ = lean_apply_1(v_h__1_2_, v___x_6_);
return v___x_7_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_1_ = stack[0].m_num;
lean_object* v_h__1_2_ = stack[1].m_obj;
lean_object* v_h__2_3_ = stack[2].m_obj;
lean_object* v_res_8_;
v_res_8_ = l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg(v_x_1_, v_h__1_2_, v_h__2_3_);
stack->m_obj
 = v_res_8_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg___boxed(lean_object* v_x_9_, lean_object* v_h__1_10_, lean_object* v_h__2_11_){
_start:
{
uint8_t v_x_24__boxed_12_; lean_object* v_res_13_; 
v_x_24__boxed_12_ = lean_unbox(v_x_9_);
v_res_13_ = l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___redArg(v_x_24__boxed_12_, v_h__1_10_, v_h__2_11_);
return v_res_13_;
}
}
lean_object* l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter(lean_object* v_motive_14_, uint8_t v_x_15_, lean_object* v_h__1_16_, lean_object* v_h__2_17_){
_start:
{
if (v_x_15_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_h__1_16_);
v___x_18_ = lean_box(0);
v___x_19_ = lean_apply_1(v_h__2_17_, v___x_18_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_h__2_17_);
v___x_20_ = lean_box(0);
v___x_21_ = lean_apply_1(v_h__1_16_, v___x_20_);
return v___x_21_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_15_ = stack[1].m_num;
lean_object* v_h__1_16_ = stack[2].m_obj;
lean_object* v_h__2_17_ = stack[3].m_obj;
lean_object* v_res_22_;
v_res_22_ = l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter(lean_box(0), v_x_15_, v_h__1_16_, v_h__2_17_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter___boxed(lean_object* v_motive_23_, lean_object* v_x_24_, lean_object* v_h__1_25_, lean_object* v_h__2_26_){
_start:
{
uint8_t v_x_41__boxed_27_; lean_object* v_res_28_; 
v_x_41__boxed_27_ = lean_unbox(v_x_24_);
v_res_28_ = l___private_Init_Data_List_Nat_Count_0__List_filter_match__1_splitter(v_motive_23_, v_x_41__boxed_27_, v_h__1_25_, v_h__2_26_);
return v_res_28_;
}
}
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_Nat_Count(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_Nat_Count(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Count(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_MinMax(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_Count(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_MinMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Nat_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_Nat_Count(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_Nat_Count(builtin);
}
#ifdef __cplusplus
}
#endif
