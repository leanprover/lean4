// Lean compiler output
// Module: Lean.Modifiers
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
lean_object* l_Lean_Environment_mainModule(lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_mkPrivateNameCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkTagDeclarationExtension(lean_object*, lean_object*);
uint8_t l_Lean_TagDeclarationExtension_isTagged(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TagDeclarationExtension_tag(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "protectedExt"};
static const lean_object* l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Modifiers_0__Lean_initFn___closed__0_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Modifiers_0__Lean_initFn___closed__1_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 46, 162, 33, 14, 69, 149, 205)}};
static const lean_object* l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_protectedExt;
LEAN_EXPORT lean_object* l_Lean_addProtected(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isProtected(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProtected___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkPrivateName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Modifiers_0__Lean_initFn___closed__2_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_));
v___x_8_ = lean_box(2);
v___x_9_ = l_Lean_mkTagDeclarationExtension(v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2____boxed(lean_object* v_a_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_();
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_addProtected(lean_object* v_env_12_, lean_object* v_n_13_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = l_Lean_protectedExt;
v___x_15_ = l_Lean_TagDeclarationExtension_tag(v___x_14_, v_env_12_, v_n_13_);
return v___x_15_;
}
}
LEAN_EXPORT uint8_t l_Lean_isProtected(lean_object* v_env_16_, lean_object* v_n_17_){
_start:
{
lean_object* v___x_18_; lean_object* v_toEnvExtension_19_; lean_object* v_asyncMode_20_; uint8_t v___x_21_; 
v___x_18_ = l_Lean_protectedExt;
v_toEnvExtension_19_ = lean_ctor_get(v___x_18_, 0);
v_asyncMode_20_ = lean_ctor_get(v_toEnvExtension_19_, 2);
v___x_21_ = l_Lean_TagDeclarationExtension_isTagged(v___x_18_, v_env_16_, v_n_17_, v_asyncMode_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProtected___boxed(lean_object* v_env_22_, lean_object* v_n_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l_Lean_isProtected(v_env_22_, v_n_23_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPrivateName(lean_object* v_env_26_, lean_object* v_n_27_){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = l_Lean_Environment_mainModule(v_env_26_);
v___x_29_ = l_Lean_privateToUserName(v_n_27_);
v___x_30_ = l_Lean_mkPrivateNameCore(v___x_28_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkPrivateName___boxed(lean_object* v_env_31_, lean_object* v_n_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_mkPrivateName(v_env_31_, v_n_32_);
lean_dec_ref(v_env_31_);
return v_res_33_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Modifiers(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Modifiers_0__Lean_initFn_00___x40_Lean_Modifiers_2938752216____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_protectedExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_protectedExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Modifiers(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Modifiers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Modifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Modifiers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Modifiers(builtin);
}
#ifdef __cplusplus
}
#endif
