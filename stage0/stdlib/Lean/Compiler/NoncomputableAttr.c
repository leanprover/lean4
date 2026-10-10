// Lean compiler output
// Module: Lean.Compiler.NoncomputableAttr
// Imports: public import Lean.EnvExtension
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "noncomputableExt"};
static const lean_object* l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(159, 71, 152, 254, 79, 213, 51, 33)}};
static const lean_object* l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_noncomputableExt;
LEAN_EXPORT lean_object* l_Lean_addNoncomputable(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isNoncomputable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isNoncomputable___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_));
v___x_8_ = lean_box(0);
v___x_9_ = 0;
v___x_10_ = l_Lean_mkTagDeclarationExtension(v___x_7_, v___x_8_, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_11_;
v_res_11_ = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_();
stack->m_obj
 = v_res_11_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2____boxed(lean_object* v_a_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_();
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_addNoncomputable(lean_object* v_env_14_, lean_object* v_declName_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = l_Lean_noncomputableExt;
v___x_17_ = l_Lean_TagDeclarationExtension_tag(v___x_16_, v_env_14_, v_declName_15_);
return v___x_17_;
}
}
uint8_t l_Lean_isNoncomputable(lean_object* v_env_18_, lean_object* v_declName_19_, lean_object* v_asyncMode_20_){
_start:
{
lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_21_ = l_Lean_noncomputableExt;
v___x_22_ = l_Lean_TagDeclarationExtension_isTagged(v___x_21_, v_env_18_, v_declName_19_, v_asyncMode_20_);
return v___x_22_;
}
}
LEAN_EXPORT void l_Lean_isNoncomputable_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_18_ = stack[0].m_obj;
lean_object* v_declName_19_ = stack[1].m_obj;
lean_object* v_asyncMode_20_ = stack[2].m_obj;
uint8_t v_res_23_;
v_res_23_ = l_Lean_isNoncomputable(v_env_18_, v_declName_19_, v_asyncMode_20_);
stack->m_num = v_res_23_;
}
LEAN_EXPORT lean_object* l_Lean_isNoncomputable___boxed(lean_object* v_env_24_, lean_object* v_declName_25_, lean_object* v_asyncMode_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_Lean_isNoncomputable(v_env_24_, v_declName_25_, v_asyncMode_26_);
lean_dec(v_asyncMode_26_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_noncomputableExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_noncomputableExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NoncomputableAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_NoncomputableAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_NoncomputableAttr(builtin);
}
#ifdef __cplusplus
}
#endif
