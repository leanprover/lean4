// Lean compiler output
// Module: Lean.Elab.Tactic.BoolToPropSimps
// Imports: public import Lean.Meta.Tactic.Simp.Attr
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerSimpAttr(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "bool_to_prop"};
static const lean_object* l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(230, 90, 229, 136, 228, 174, 42, 173)}};
static const lean_object* l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 94, .m_capacity = 94, .m_length = 93, .m_data = "simp lemmas converting boolean expressions in terms of `decide` into propositional statements"};
static const lean_object* l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__3_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__0_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(175, 150, 210, 209, 141, 143, 60, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_bool__to__prop;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__1_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_));
v___x_11_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__2_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_));
v___x_12_ = ((lean_object*)(l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn___closed__4_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_));
v___x_13_ = l_Lean_Meta_registerSimpAttr(v___x_10_, v___x_11_, v___x_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2____boxed(lean_object* v_a_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
return v_res_15_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_BoolToPropSimps(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_BoolToPropSimps_0__Lean_initFn_00___x40_Lean_Elab_Tactic_BoolToPropSimps_428426324____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_bool__to__prop = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_bool__to__prop);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_BoolToPropSimps(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BoolToPropSimps(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_BoolToPropSimps(builtin);
}
#ifdef __cplusplus
}
#endif
