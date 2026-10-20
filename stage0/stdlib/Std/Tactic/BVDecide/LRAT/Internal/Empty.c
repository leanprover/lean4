// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Empty
// Imports: public import Std.Tactic.BVDecide.LRAT.Internal.Rup
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
extern lean_object* l_ByteArray_empty;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__0 = (const lean_object*)&l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__0_value;
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__1;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_3_ = l_ByteArray_empty;
v___x_4_ = ((lean_object*)(l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__0));
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
lean_ctor_set(v___x_5_, 1, v___x_3_);
return v___x_5_;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty(lean_object* v_s_6_, lean_object* v_rupHints_7_){
_start:
{
lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_8_ = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__1, &l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__1_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___closed__1);
v___x_9_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkRup(v_s_6_, v___x_8_, v_rupHints_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty___boxed(lean_object* v_s_10_, lean_object* v_rupHints_11_){
_start:
{
uint8_t v_res_12_; lean_object* v_r_13_; 
v_res_12_ = l_Std_Tactic_BVDecide_LRAT_Internal_State_checkEmpty(v_s_10_, v_rupHints_11_);
lean_dec_ref(v_rupHints_11_);
lean_dec_ref(v_s_10_);
v_r_13_ = lean_box(v_res_12_);
return v_r_13_;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Rup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Empty(builtin);
}
#ifdef __cplusplus
}
#endif
