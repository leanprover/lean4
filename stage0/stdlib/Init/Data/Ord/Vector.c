// Lean compiler output
// Module: Init.Data.Ord.Vector
// Imports: public import Init.Data.Order.Ord public import Init.Data.Vector.Basic import Init.Data.Vector.Lemmas
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
uint8_t l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_compareLex___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_compareLex___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Vector_compareLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instOrd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Vector_instOrd(lean_object*, lean_object*, lean_object*);
uint8_t l_Vector_compareLex___redArg(lean_object* v_cmp_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_cmp_1_, v_a_2_, v_b_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_Vector_compareLex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cmp_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_b_3_ = stack[2].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_Vector_compareLex___redArg(v_cmp_1_, v_a_2_, v_b_3_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_Vector_compareLex___redArg___boxed(lean_object* v_cmp_7_, lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_Vector_compareLex___redArg(v_cmp_7_, v_a_8_, v_b_9_);
lean_dec_ref(v_b_9_);
lean_dec_ref(v_a_8_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
uint8_t l_Vector_compareLex(lean_object* v_00_u03b1_12_, lean_object* v_n_13_, lean_object* v_cmp_14_, lean_object* v_a_15_, lean_object* v_b_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(lean_box(0), v_cmp_14_, v_a_15_, v_b_16_, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT void l_Vector_compareLex_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_13_ = stack[1].m_obj;
lean_object* v_cmp_14_ = stack[2].m_obj;
lean_object* v_a_15_ = stack[3].m_obj;
lean_object* v_b_16_ = stack[4].m_obj;
uint8_t v_res_19_;
v_res_19_ = l_Vector_compareLex(lean_box(0), v_n_13_, v_cmp_14_, v_a_15_, v_b_16_);
stack->m_num = v_res_19_;
}
LEAN_EXPORT lean_object* l_Vector_compareLex___boxed(lean_object* v_00_u03b1_20_, lean_object* v_n_21_, lean_object* v_cmp_22_, lean_object* v_a_23_, lean_object* v_b_24_){
_start:
{
uint8_t v_res_25_; lean_object* v_r_26_; 
v_res_25_ = l_Vector_compareLex(v_00_u03b1_20_, v_n_21_, v_cmp_22_, v_a_23_, v_b_24_);
lean_dec_ref(v_b_24_);
lean_dec_ref(v_a_23_);
lean_dec(v_n_21_);
v_r_26_ = lean_box(v_res_25_);
return v_r_26_;
}
}
LEAN_EXPORT lean_object* l_Vector_instOrd___redArg(lean_object* v_n_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lean_alloc_closure((void*)(l_Vector_compareLex___boxed), 5, 3);
lean_closure_set(v___x_29_, 0, lean_box(0));
lean_closure_set(v___x_29_, 1, v_n_27_);
lean_closure_set(v___x_29_, 2, v_inst_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Vector_instOrd(lean_object* v_00_u03b1_30_, lean_object* v_n_31_, lean_object* v_inst_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_alloc_closure((void*)(l_Vector_compareLex___boxed), 5, 3);
lean_closure_set(v___x_33_, 0, lean_box(0));
lean_closure_set(v___x_33_, 1, v_n_31_);
lean_closure_set(v___x_33_, 2, v_inst_32_);
return v___x_33_;
}
}
lean_object* runtime_initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Ord_Vector(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Ord_Vector(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Order_Ord(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Ord_Vector(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Order_Ord(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Ord_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Ord_Vector(builtin);
}
#ifdef __cplusplus
}
#endif
