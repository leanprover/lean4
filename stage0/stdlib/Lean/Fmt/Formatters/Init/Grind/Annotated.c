// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Grind.Annotated
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Grind.Annotated import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtGrindAnnotated___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtGrindAnnotated___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtGrindAnnotated___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_fmtGrindAnnotated___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtGrindAnnotated___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lean_Fmt_fmtGrindAnnotated___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtGrindAnnotated___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "grindAnnotated"};
static const lean_object* l_Lean_Fmt_fmtGrindAnnotated___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnnotated___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnnotated___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnnotated___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnnotated___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__3_value),LEAN_SCALAR_PTR_LITERAL(197, 145, 42, 29, 223, 69, 23, 152)}};
static const lean_object* l_Lean_Fmt_fmtGrindAnnotated___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__4_value;
static const lean_string_object l_Lean_Fmt_fmtGrindAnnotated___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtGrindAnnotated___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__5_value;
static const lean_ctor_object l_Lean_Fmt_fmtGrindAnnotated___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__5_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtGrindAnnotated___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnnotated(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnnotated___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGrindAnnotated"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtGrindAnnotated___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(82, 39, 226, 124, 209, 6, 172, 15)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnnotated(lean_object* v_x_13_, lean_object* v_a_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; uint8_t v___x_17_; 
v___x_16_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAnnotated___closed__4));
lean_inc(v_x_13_);
v___x_17_ = l_Lean_Syntax_isOfKind(v_x_13_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_x_13_);
v___x_18_ = l_Lean_Fmt_Error_partialFormatter;
v___x_19_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
lean_ctor_set(v___x_19_, 1, v_a_15_);
return v___x_19_;
}
else
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_20_ = lean_unsigned_to_nat(1u);
v___x_21_ = l_Lean_Syntax_getArg(v_x_13_, v___x_20_);
v___x_22_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAnnotated___closed__6));
lean_inc(v___x_21_);
v___x_23_ = l_Lean_Syntax_isOfKind(v___x_21_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v___x_21_);
lean_dec(v_x_13_);
v___x_24_ = l_Lean_Fmt_Error_partialFormatter;
v___x_25_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v_a_15_);
return v___x_25_;
}
else
{
lean_object* v___x_26_; lean_object* v_tk_27_; lean_object* v___x_28_; 
v___x_26_ = lean_unsigned_to_nat(0u);
v_tk_27_ = l_Lean_Syntax_getArg(v_x_13_, v___x_26_);
lean_dec(v_x_13_);
v___x_28_ = l_Lean_Fmt_fmt(v_tk_27_, v_a_14_, v_a_15_);
if (lean_obj_tag(v___x_28_) == 0)
{
lean_object* v_a_29_; lean_object* v_a_30_; lean_object* v___x_31_; 
v_a_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc(v_a_29_);
v_a_30_ = lean_ctor_get(v___x_28_, 1);
lean_inc(v_a_30_);
lean_dec_ref_known(v___x_28_, 2);
v___x_31_ = l_Lean_Fmt_fmt(v___x_21_, v_a_14_, v_a_30_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v_a_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_47_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
v_a_33_ = lean_ctor_get(v___x_31_, 1);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_31_);
if (v_isSharedCheck_47_ == 0)
{
v___x_35_ = v___x_31_;
v_isShared_36_ = v_isSharedCheck_47_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_a_33_);
lean_inc(v_a_32_);
lean_dec(v___x_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_47_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; uint8_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_37_ = lean_unsigned_to_nat(2u);
v___x_38_ = lean_mk_empty_array_with_capacity(v___x_37_);
v___x_39_ = lean_array_push(v___x_38_, v_a_29_);
v___x_40_ = lean_array_push(v___x_39_, v_a_32_);
v___x_41_ = 0;
v___x_42_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_42_, 0, v___x_23_);
lean_ctor_set_uint8(v___x_42_, 1, v___x_41_);
lean_ctor_set_uint8(v___x_42_, 2, v___x_41_);
lean_ctor_set_uint8(v___x_42_, 3, v___x_41_);
v___x_43_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_40_, v___x_42_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 0, v___x_43_);
v___x_45_ = v___x_35_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_43_);
lean_ctor_set(v_reuseFailAlloc_46_, 1, v_a_33_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
else
{
lean_dec(v_a_29_);
return v___x_31_;
}
}
else
{
lean_dec(v___x_21_);
return v___x_28_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtGrindAnnotated___boxed(lean_object* v_x_48_, lean_object* v_a_49_, lean_object* v_a_50_){
_start:
{
lean_object* v_res_51_; 
v_res_51_ = l_Lean_Fmt_fmtGrindAnnotated(v_x_48_, v_a_49_, v_a_50_);
lean_dec_ref(v_a_49_);
return v_res_51_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_59_ = l_Lean_Fmt_fmtAttribute;
v___x_60_ = ((lean_object*)(l_Lean_Fmt_fmtGrindAnnotated___closed__4));
v___x_61_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___closed__2));
v___x_62_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtGrindAnnotated___boxed), 3, 0);
v___x_63_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_59_, v___x_60_, v___x_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1___boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1();
return v_res_65_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Grind_Annotated_0__Lean_Fmt_fmtGrindAnnotated___regBuiltin_Lean_Fmt_fmtGrindAnnotated__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Grind_Annotated(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Grind_Annotated(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Grind_Annotated(builtin);
}
#ifdef __cplusplus
}
#endif
