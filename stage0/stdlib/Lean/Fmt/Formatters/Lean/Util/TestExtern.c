// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Util.TestExtern
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Util.TestExtern import Init.Data
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTestExtern___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtTestExtern___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTestExtern___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtTestExtern___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "testExternCmd"};
static const lean_object* l_Lean_Fmt_fmtTestExtern___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTestExtern___closed__1_value;
static const lean_ctor_object l_Lean_Fmt_fmtTestExtern___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTestExtern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtTestExtern___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTestExtern___closed__2_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTestExtern___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 105, 245, 61, 9, 235, 143, 113)}};
static const lean_object* l_Lean_Fmt_fmtTestExtern___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTestExtern___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTestExtern(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTestExtern___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "fmtTestExtern"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTestExtern___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(102, 130, 82, 84, 64, 238, 57, 65)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTestExtern(lean_object* v_x_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lean_Fmt_fmtTestExtern___closed__2));
lean_inc(v_x_6_);
v___x_10_ = l_Lean_Syntax_isOfKind(v_x_6_, v___x_9_);
if (v___x_10_ == 0)
{
lean_object* v___x_11_; lean_object* v___x_12_; 
lean_dec(v_x_6_);
v___x_11_ = l_Lean_Fmt_Error_partialFormatter;
v___x_12_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v_a_8_);
return v___x_12_;
}
else
{
lean_object* v___x_13_; lean_object* v_testExternTk_14_; lean_object* v___x_15_; 
v___x_13_ = lean_unsigned_to_nat(0u);
v_testExternTk_14_ = l_Lean_Syntax_getArg(v_x_6_, v___x_13_);
v___x_15_ = l_Lean_Fmt_fmt(v_testExternTk_14_, v_a_7_, v_a_8_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v_a_16_; lean_object* v_a_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v_a_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_a_16_);
v_a_17_ = lean_ctor_get(v___x_15_, 1);
lean_inc(v_a_17_);
lean_dec_ref_known(v___x_15_, 2);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = l_Lean_Syntax_getArg(v_x_6_, v___x_18_);
lean_dec(v_x_6_);
v___x_20_ = l_Lean_Fmt_fmt(v___x_19_, v_a_7_, v_a_17_);
if (lean_obj_tag(v___x_20_) == 0)
{
lean_object* v_a_21_; lean_object* v_a_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_36_; 
v_a_21_ = lean_ctor_get(v___x_20_, 0);
v_a_22_ = lean_ctor_get(v___x_20_, 1);
v_isSharedCheck_36_ = !lean_is_exclusive(v___x_20_);
if (v_isSharedCheck_36_ == 0)
{
v___x_24_ = v___x_20_;
v_isShared_25_ = v_isSharedCheck_36_;
goto v_resetjp_23_;
}
else
{
lean_inc(v_a_22_);
lean_inc(v_a_21_);
lean_dec(v___x_20_);
v___x_24_ = lean_box(0);
v_isShared_25_ = v_isSharedCheck_36_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_34_; 
v___x_26_ = lean_unsigned_to_nat(2u);
v___x_27_ = lean_mk_empty_array_with_capacity(v___x_26_);
v___x_28_ = lean_array_push(v___x_27_, v_a_16_);
v___x_29_ = lean_array_push(v___x_28_, v_a_21_);
v___x_30_ = 0;
v___x_31_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_31_, 0, v___x_10_);
lean_ctor_set_uint8(v___x_31_, 1, v___x_30_);
lean_ctor_set_uint8(v___x_31_, 2, v___x_30_);
lean_ctor_set_uint8(v___x_31_, 3, v___x_30_);
v___x_32_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_29_, v___x_31_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 0, v___x_32_);
v___x_34_ = v___x_24_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_35_, 1, v_a_22_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
else
{
lean_dec(v_a_16_);
return v___x_20_;
}
}
else
{
lean_dec(v_x_6_);
return v___x_15_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTestExtern___boxed(lean_object* v_x_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Fmt_fmtTestExtern(v_x_37_, v_a_38_, v_a_39_);
lean_dec_ref(v_a_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1(){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_48_ = l_Lean_Fmt_fmtAttribute;
v___x_49_ = ((lean_object*)(l_Lean_Fmt_fmtTestExtern___closed__2));
v___x_50_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___closed__2));
v___x_51_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTestExtern___boxed), 3, 0);
v___x_52_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_48_, v___x_49_, v___x_50_, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1___boxed(lean_object* v_a_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1();
return v_res_54_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Util_TestExtern(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Util_TestExtern_0__Lean_Fmt_fmtTestExtern___regBuiltin_Lean_Fmt_fmtTestExtern__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Util_TestExtern(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Util_TestExtern(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Util_TestExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Util_TestExtern(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Util_TestExtern(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_TestExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Util_TestExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Util_TestExtern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Util_TestExtern(builtin);
}
#ifdef __cplusplus
}
#endif
