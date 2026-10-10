// Lean compiler output
// Module: Init.Data.Subtype.OrderExtra
// Imports: public import Init.Data.Ord.Basic
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
LEAN_EXPORT uint8_t l_instOrdSubtype___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdSubtype___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrdSubtype___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instOrdSubtype(lean_object*, lean_object*, lean_object*);
uint8_t l_instOrdSubtype___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_a_2_, lean_object* v_b_3_){
_start:
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_apply_2(v_inst_1_, v_a_2_, v_b_3_);
v___x_5_ = lean_unbox(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT void l_instOrdSubtype___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_b_3_ = stack[2].m_obj;
uint8_t v_res_6_;
v_res_6_ = l_instOrdSubtype___redArg___lam__0(v_inst_1_, v_a_2_, v_b_3_);
stack->m_num = v_res_6_;
}
LEAN_EXPORT lean_object* l_instOrdSubtype___redArg___lam__0___boxed(lean_object* v_inst_7_, lean_object* v_a_8_, lean_object* v_b_9_){
_start:
{
uint8_t v_res_10_; lean_object* v_r_11_; 
v_res_10_ = l_instOrdSubtype___redArg___lam__0(v_inst_7_, v_a_8_, v_b_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT lean_object* l_instOrdSubtype___redArg(lean_object* v_inst_12_){
_start:
{
lean_object* v___f_13_; 
v___f_13_ = lean_alloc_closure((void*)(l_instOrdSubtype___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_13_, 0, v_inst_12_);
return v___f_13_;
}
}
LEAN_EXPORT lean_object* l_instOrdSubtype(lean_object* v_00_u03b1_14_, lean_object* v_inst_15_, lean_object* v_P_16_){
_start:
{
lean_object* v___f_17_; 
v___f_17_ = lean_alloc_closure((void*)(l_instOrdSubtype___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_17_, 0, v_inst_15_);
return v___f_17_;
}
}
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Subtype_OrderExtra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Subtype_OrderExtra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Subtype_OrderExtra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Subtype_OrderExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Subtype_OrderExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Subtype_OrderExtra(builtin);
}
#ifdef __cplusplus
}
#endif
