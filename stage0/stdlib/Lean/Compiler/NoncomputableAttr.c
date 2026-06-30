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
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_));
v___x_8_ = lean_box(0);
v___x_9_ = l_Lean_mkTagDeclarationExtension(v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2____boxed(lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Compiler_NoncomputableAttr_0__Lean_initFn_00___x40_Lean_Compiler_NoncomputableAttr_174063325____hygCtx___hyg_2_();
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_addNoncomputable(lean_object* v_env_12_, lean_object* v_declName_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = l_Lean_noncomputableExt;
v___x_15_ = l_Lean_TagDeclarationExtension_tag(v___x_14_, v_env_12_, v_declName_13_);
return v___x_15_;
}
}
LEAN_EXPORT uint8_t l_Lean_isNoncomputable(lean_object* v_env_16_, lean_object* v_declName_17_, lean_object* v_asyncMode_18_){
_start:
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = l_Lean_noncomputableExt;
v___x_20_ = l_Lean_TagDeclarationExtension_isTagged(v___x_19_, v_env_16_, v_declName_17_, v_asyncMode_18_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_isNoncomputable___boxed(lean_object* v_env_21_, lean_object* v_declName_22_, lean_object* v_asyncMode_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lean_isNoncomputable(v_env_21_, v_declName_22_, v_asyncMode_23_);
lean_dec(v_asyncMode_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
