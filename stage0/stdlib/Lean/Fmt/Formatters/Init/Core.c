// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Core
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Core import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtEmptyBraces___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "term{}"};
static const lean_object* l_Lean_Fmt_fmtEmptyBraces___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtEmptyBraces___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtEmptyBraces___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtEmptyBraces___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 141, 217, 101, 193, 131, 35, 71)}};
static const lean_object* l_Lean_Fmt_fmtEmptyBraces___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtEmptyBraces___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEmptyBraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEmptyBraces___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtEmptyBraces"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(116, 51, 16, 123, 102, 87, 78, 181)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEmptyBraces(lean_object* v_x_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Fmt_fmtEmptyBraces___closed__1));
lean_inc(v_x_4_);
v___x_8_ = l_Lean_Syntax_isOfKind(v_x_4_, v___x_7_);
if (v___x_8_ == 0)
{
lean_object* v___x_9_; lean_object* v___x_10_; 
lean_dec(v_x_4_);
v___x_9_ = l_Lean_Fmt_Error_partialFormatter;
v___x_10_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v_a_6_);
return v___x_10_;
}
else
{
lean_object* v___x_11_; lean_object* v_lbTk_12_; lean_object* v___x_13_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v_lbTk_12_ = l_Lean_Syntax_getArg(v_x_4_, v___x_11_);
v___x_13_ = l_Lean_Fmt_fmt(v_lbTk_12_, v_a_5_, v_a_6_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v_a_14_; lean_object* v_a_15_; lean_object* v___x_16_; lean_object* v_rbTk_17_; lean_object* v___x_18_; 
v_a_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc(v_a_14_);
v_a_15_ = lean_ctor_get(v___x_13_, 1);
lean_inc(v_a_15_);
lean_dec_ref_known(v___x_13_, 2);
v___x_16_ = lean_unsigned_to_nat(1u);
v_rbTk_17_ = l_Lean_Syntax_getArg(v_x_4_, v___x_16_);
lean_dec(v_x_4_);
v___x_18_ = l_Lean_Fmt_fmt(v_rbTk_17_, v_a_5_, v_a_15_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v_a_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_32_; 
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_a_20_ = lean_ctor_get(v___x_18_, 1);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_32_ == 0)
{
v___x_22_ = v___x_18_;
v_isShared_23_ = v_isSharedCheck_32_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_a_20_);
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_32_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_24_ = lean_unsigned_to_nat(2u);
v___x_25_ = lean_mk_empty_array_with_capacity(v___x_24_);
v___x_26_ = lean_array_push(v___x_25_, v_a_14_);
v___x_27_ = lean_array_push(v___x_26_, v_a_19_);
v___x_28_ = l_Lean_Fmt_Layouts_atomic(v___x_27_);
lean_dec_ref(v___x_27_);
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v___x_28_);
v___x_30_ = v___x_22_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_28_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_a_20_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
else
{
lean_dec(v_a_14_);
return v___x_18_;
}
}
else
{
lean_dec(v_x_4_);
return v___x_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtEmptyBraces___boxed(lean_object* v_x_33_, lean_object* v_a_34_, lean_object* v_a_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Fmt_fmtEmptyBraces(v_x_33_, v_a_34_, v_a_35_);
lean_dec_ref(v_a_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1(){
_start:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_45_ = l_Lean_Fmt_fmtAttribute;
v___x_46_ = ((lean_object*)(l_Lean_Fmt_fmtEmptyBraces___closed__1));
v___x_47_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___closed__3));
v___x_48_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtEmptyBraces___boxed), 3, 0);
v___x_49_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_45_, v___x_46_, v___x_47_, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1___boxed(lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1();
return v_res_51_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Core(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Core_0__Lean_Fmt_fmtEmptyBraces___regBuiltin_Lean_Fmt_fmtEmptyBraces__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Core(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Core(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Core(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Core(builtin);
}
#ifdef __cplusplus
}
#endif
