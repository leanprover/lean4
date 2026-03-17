// Lean compiler output
// Module: Lake.Config.Script
// Imports: public import Init.Dynamic public import Init.System.IO public import Lake.Util.Exit public import Lake.Config.Context
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
static const lean_string_object l_Lake_instTypeNameScriptFn_unsafe__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_instTypeNameScriptFn_unsafe__1___closed__0 = (const lean_object*)&l_Lake_instTypeNameScriptFn_unsafe__1___closed__0_value;
static const lean_string_object l_Lake_instTypeNameScriptFn_unsafe__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ScriptFn"};
static const lean_object* l_Lake_instTypeNameScriptFn_unsafe__1___closed__1 = (const lean_object*)&l_Lake_instTypeNameScriptFn_unsafe__1___closed__1_value;
static const lean_ctor_object l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instTypeNameScriptFn_unsafe__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value_aux_0),((lean_object*)&l_Lake_instTypeNameScriptFn_unsafe__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 20, 53, 85, 81, 66, 33, 235)}};
static const lean_object* l_Lake_instTypeNameScriptFn_unsafe__1___closed__2 = (const lean_object*)&l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameScriptFn_unsafe__1 = (const lean_object*)&l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_instTypeNameScriptFn = (const lean_object*)&l_Lake_instTypeNameScriptFn_unsafe__1___closed__2_value;
static const lean_string_object l_Lake_instInhabitedScript_default___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "(`Inhabited.default` for `IO.Error`)"};
static const lean_object* l_Lake_instInhabitedScript_default___lam__0___closed__0 = (const lean_object*)&l_Lake_instInhabitedScript_default___lam__0___closed__0_value;
static const lean_ctor_object l_Lake_instInhabitedScript_default___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 18}, .m_objs = {((lean_object*)&l_Lake_instInhabitedScript_default___lam__0___closed__0_value)}};
static const lean_object* l_Lake_instInhabitedScript_default___lam__0___closed__1 = (const lean_object*)&l_Lake_instInhabitedScript_default___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript_default___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript_default___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instInhabitedScript_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instInhabitedScript_default___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instInhabitedScript_default___closed__0 = (const lean_object*)&l_Lake_instInhabitedScript_default___closed__0_value;
static const lean_string_object l_Lake_instInhabitedScript_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_instInhabitedScript_default___closed__1 = (const lean_object*)&l_Lake_instInhabitedScript_default___closed__1_value;
static const lean_ctor_object l_Lake_instInhabitedScript_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instInhabitedScript_default___closed__1_value),((lean_object*)&l_Lake_instInhabitedScript_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_instInhabitedScript_default___closed__2 = (const lean_object*)&l_Lake_instInhabitedScript_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedScript_default = (const lean_object*)&l_Lake_instInhabitedScript_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lake_instInhabitedScript = (const lean_object*)&l_Lake_instInhabitedScript_default___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_Script_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Script_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript_default___lam__0(lean_object* v_x_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_14_ = ((lean_object*)(l_Lake_instInhabitedScript_default___lam__0___closed__1));
v___x_15_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lake_instInhabitedScript_default___lam__0___boxed(lean_object* v_x_16_, lean_object* v___y_17_, lean_object* v___y_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lake_instInhabitedScript_default___lam__0(v_x_16_, v___y_17_);
lean_dec(v___y_17_);
lean_dec(v_x_16_);
return v_res_19_;
}
}
LEAN_EXPORT lean_object* l_Lake_Script_run(lean_object* v_args_28_, lean_object* v_self_29_, lean_object* v_a_30_){
_start:
{
lean_object* v_fn_32_; lean_object* v___x_33_; 
v_fn_32_ = lean_ctor_get(v_self_29_, 1);
lean_inc_ref(v_fn_32_);
lean_dec_ref(v_self_29_);
v___x_33_ = lean_apply_3(v_fn_32_, v_args_28_, v_a_30_, lean_box(0));
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lake_Script_run___boxed(lean_object* v_args_34_, lean_object* v_self_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_Script_run(v_args_34_, v_self_35_, v_a_36_);
return v_res_38_;
}
}
lean_object* runtime_initialize_Init_Dynamic(uint8_t builtin);
lean_object* runtime_initialize_Init_System_IO(uint8_t builtin);
lean_object* runtime_initialize_Lake_Util_Exit(uint8_t builtin);
lean_object* runtime_initialize_Lake_Config_Context(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Config_Script(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Config_Script(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Dynamic(uint8_t builtin);
lean_object* initialize_Init_System_IO(uint8_t builtin);
lean_object* initialize_Lake_Util_Exit(uint8_t builtin);
lean_object* initialize_Lake_Config_Context(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Script(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Dynamic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_IO(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Exit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Config_Script(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Config_Script(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Config_Script(builtin);
}
#ifdef __cplusplus
}
#endif
