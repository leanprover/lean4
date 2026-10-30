// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.SimpAttr
// Imports: public import Lean.Meta.Sym.Simp.Attr
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_registerSymSimpAttr(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "vcgen_simp"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__0_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 170, 91, 161, 251, 76, 171, 2)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "simp theorems used by vcgen"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "VCGen"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "vcgenSimpExt"};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__3_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__4_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__5_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__6_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(206, 175, 173, 61, 99, 140, 39, 150)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__7_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(88, 240, 79, 229, 179, 36, 234, 84)}};
static const lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_vcgenSimpExt;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__1_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_));
v___x_18_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__2_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_));
v___x_19_ = ((lean_object*)(l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn___closed__8_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_));
v___x_20_ = l_Lean_Meta_Sym_Simp_registerSymSimpAttr(v___x_17_, v___x_18_, v___x_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2____boxed(lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_();
return v_res_22_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_SimpAttr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_VCGen_SimpAttr_0__Lean_Elab_Tactic_VCGen_initFn_00___x40_Lean_Elab_Tactic_VCGen_SimpAttr_727399933____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Tactic_VCGen_vcgenSimpExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_vcgenSimpExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_SimpAttr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_Attr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_SimpAttr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_Attr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_SimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_SimpAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_SimpAttr(builtin);
}
#ifdef __cplusplus
}
#endif
