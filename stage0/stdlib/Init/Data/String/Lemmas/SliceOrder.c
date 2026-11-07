// Lean compiler output
// Module: Init.Data.String.Lemmas.SliceOrder
// Imports: public import Init.Data.String.Slice.Basic public import Init.Data.Order.PackageFactories import all Init.Data.String.Slice.Basic import Init.Data.String.Lemmas.Pattern.Memcmp import Init.Data.String.Lemmas.Basic import Init.Data.String.Lemmas.Slice
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
lean_object* l_String_Slice_compare___boxed(lean_object*, lean_object*);
lean_object* l_String_Slice_instDecidableLT___boxed(lean_object*, lean_object*);
lean_object* l_String_Slice_instDecidableLE___boxed(lean_object*, lean_object*);
lean_object* l_String_Slice_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instLinearPreorderPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_compare___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instLinearPreorderPackage___closed__0 = (const lean_object*)&l_String_Slice_instLinearPreorderPackage___closed__0_value;
static const lean_closure_object l_String_Slice_instLinearPreorderPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instLinearPreorderPackage___closed__1 = (const lean_object*)&l_String_Slice_instLinearPreorderPackage___closed__1_value;
static lean_once_cell_t l_String_Slice_instLinearPreorderPackage___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_instLinearPreorderPackage___closed__2;
static lean_once_cell_t l_String_Slice_instLinearPreorderPackage___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_instLinearPreorderPackage___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_instLinearPreorderPackage;
static lean_object* _init_l_String_Slice_instLinearPreorderPackage___closed__2(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_this_6_; lean_object* v_this_7_; lean_object* v___x_8_; 
v___x_3_ = lean_alloc_closure((void*)(l_String_Slice_instDecidableLT___boxed), 2, 0);
v___x_4_ = lean_alloc_closure((void*)(l_String_Slice_instDecidableLE___boxed), 2, 0);
v___x_5_ = ((lean_object*)(l_String_Slice_instLinearPreorderPackage___closed__1));
v_this_6_ = lean_box(0);
v_this_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_8_, 0, v_this_7_);
lean_ctor_set(v___x_8_, 1, v_this_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
lean_ctor_set(v___x_8_, 3, v___x_4_);
lean_ctor_set(v___x_8_, 4, v___x_3_);
return v___x_8_;
}
}
static lean_object* _init_l_String_Slice_instLinearPreorderPackage___closed__3(void){
_start:
{
lean_object* v_this_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_this_9_ = ((lean_object*)(l_String_Slice_instLinearPreorderPackage___closed__0));
v___x_10_ = lean_obj_once(&l_String_Slice_instLinearPreorderPackage___closed__2, &l_String_Slice_instLinearPreorderPackage___closed__2_once, _init_l_String_Slice_instLinearPreorderPackage___closed__2);
v___x_11_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v_this_9_);
return v___x_11_;
}
}
static lean_object* _init_l_String_Slice_instLinearPreorderPackage(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_String_Slice_instLinearPreorderPackage___closed__3, &l_String_Slice_instLinearPreorderPackage___closed__3_once, _init_l_String_Slice_instLinearPreorderPackage___closed__3);
return v___x_12_;
}
}
lean_object* runtime_initialize_Init_Data_String_Slice_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Slice_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Pattern_Memcmp(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Lemmas_Slice(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Lemmas_SliceOrder(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_Slice_instLinearPreorderPackage = _init_l_String_Slice_instLinearPreorderPackage();
lean_mark_persistent(l_String_Slice_instLinearPreorderPackage);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Lemmas_SliceOrder(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Slice_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Pattern_Memcmp(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas_Slice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Lemmas_SliceOrder(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Pattern_Memcmp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Lemmas_SliceOrder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Lemmas_SliceOrder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Lemmas_SliceOrder(builtin);
}
#ifdef __cplusplus
}
#endif
