// Lean compiler output
// Module: Lean.Linter.CoreInternal
// Imports: public import Lean.Linter.InternalModule
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Linter_addBuiltinLinterSet(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "coreInternal"};
static const lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 202, 150, 38, 196, 187, 132, 57)}};
static const lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "internalModule"};
static const lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 202, 150, 38, 196, 187, 132, 57)}};
static const lean_ctor_object l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 143, 209, 6, 103, 6, 164, 164)}};
static const lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_));
v___x_12_ = l_Lean_NameSet_empty;
v___x_13_ = l_Lean_NameSet_insert(v___x_12_, v___x_11_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = ((lean_object*)(l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_));
v___x_16_ = lean_obj_once(&l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_, &l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_);
v___x_17_ = l_Lean_Linter_addBuiltinLinterSet(v___x_15_, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2____boxed(lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_();
return v_res_19_;
}
}
lean_object* runtime_initialize_Lean_Linter_InternalModule(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_CoreInternal(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Linter_InternalModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_CoreInternal_0__Lean_Linter_initFn_00___x40_Lean_Linter_CoreInternal_1031680685____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_CoreInternal(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_InternalModule(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_CoreInternal(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_InternalModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_CoreInternal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_CoreInternal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_CoreInternal(builtin);
}
#ifdef __cplusplus
}
#endif
