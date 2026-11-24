// Lean compiler output
// Module: Lean.Fmt.Formatters.Lean.Elab.Quotation
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lean.Elab.Quotation import Init.Data
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_pseudoApplication(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtElabStxQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_fmtElabStxQuot___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtElabStxQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Fmt_fmtElabStxQuot___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtElabStxQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Fmt_fmtElabStxQuot___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtElabStxQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Quotation"};
static const lean_object* l_Lean_Fmt_fmtElabStxQuot___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtElabStxQuot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "commandElab_stx_quot_"};
static const lean_object* l_Lean_Fmt_fmtElabStxQuot___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtElabStxQuot___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabStxQuot___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabStxQuot___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 225, 247, 249, 114, 131, 135, 109)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabStxQuot___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(14, 125, 73, 172, 99, 41, 123, 101)}};
static const lean_ctor_object l_Lean_Fmt_fmtElabStxQuot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__4_value),LEAN_SCALAR_PTR_LITERAL(72, 23, 245, 172, 122, 104, 252, 223)}};
static const lean_object* l_Lean_Fmt_fmtElabStxQuot___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__5_value;
static const lean_string_object l_Lean_Fmt_fmtElabStxQuot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Fmt_fmtElabStxQuot___closed__6 = (const lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__6_value;
static const lean_ctor_object l_Lean_Fmt_fmtElabStxQuot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Fmt_fmtElabStxQuot___closed__7 = (const lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabStxQuot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabStxQuot___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtElabStxQuot"};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtElabStxQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(177, 21, 58, 29, 201, 227, 104, 183)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabStxQuot(lean_object* v_x_15_, lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
lean_object* v___x_18_; uint8_t v___x_19_; 
v___x_18_ = ((lean_object*)(l_Lean_Fmt_fmtElabStxQuot___closed__5));
lean_inc(v_x_15_);
v___x_19_ = l_Lean_Syntax_isOfKind(v_x_15_, v___x_18_);
if (v___x_19_ == 0)
{
lean_object* v___x_20_; lean_object* v___x_21_; 
lean_dec(v_x_15_);
v___x_20_ = l_Lean_Fmt_Error_partialFormatter;
v___x_21_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v_a_17_);
return v___x_21_;
}
else
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; uint8_t v___x_25_; 
v___x_22_ = lean_unsigned_to_nat(1u);
v___x_23_ = l_Lean_Syntax_getArg(v_x_15_, v___x_22_);
v___x_24_ = ((lean_object*)(l_Lean_Fmt_fmtElabStxQuot___closed__7));
lean_inc(v___x_23_);
v___x_25_ = l_Lean_Syntax_isOfKind(v___x_23_, v___x_24_);
if (v___x_25_ == 0)
{
lean_object* v___x_26_; lean_object* v___x_27_; 
lean_dec(v___x_23_);
lean_dec(v_x_15_);
v___x_26_ = l_Lean_Fmt_Error_partialFormatter;
v___x_27_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_26_);
lean_ctor_set(v___x_27_, 1, v_a_17_);
return v___x_27_;
}
else
{
lean_object* v___x_28_; lean_object* v_elabStxQuotTk_29_; lean_object* v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(0u);
v_elabStxQuotTk_29_ = l_Lean_Syntax_getArg(v_x_15_, v___x_28_);
lean_dec(v_x_15_);
v___x_30_ = l_Lean_Fmt_fmt(v_elabStxQuotTk_29_, v_a_16_, v_a_17_);
if (lean_obj_tag(v___x_30_) == 0)
{
lean_object* v_a_31_; lean_object* v_a_32_; lean_object* v___x_33_; 
v_a_31_ = lean_ctor_get(v___x_30_, 0);
lean_inc(v_a_31_);
v_a_32_ = lean_ctor_get(v___x_30_, 1);
lean_inc(v_a_32_);
lean_dec_ref_known(v___x_30_, 2);
v___x_33_ = l_Lean_Fmt_fmt(v___x_23_, v_a_16_, v_a_32_);
if (lean_obj_tag(v___x_33_) == 0)
{
lean_object* v_a_34_; lean_object* v_a_35_; lean_object* v___x_37_; uint8_t v_isShared_38_; uint8_t v_isSharedCheck_49_; 
v_a_34_ = lean_ctor_get(v___x_33_, 0);
v_a_35_ = lean_ctor_get(v___x_33_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_33_);
if (v_isSharedCheck_49_ == 0)
{
v___x_37_ = v___x_33_;
v_isShared_38_ = v_isSharedCheck_49_;
goto v_resetjp_36_;
}
else
{
lean_inc(v_a_35_);
lean_inc(v_a_34_);
lean_dec(v___x_33_);
v___x_37_ = lean_box(0);
v_isShared_38_ = v_isSharedCheck_49_;
goto v_resetjp_36_;
}
v_resetjp_36_:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; uint8_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_39_ = lean_unsigned_to_nat(2u);
v___x_40_ = lean_mk_empty_array_with_capacity(v___x_39_);
v___x_41_ = lean_array_push(v___x_40_, v_a_31_);
v___x_42_ = lean_array_push(v___x_41_, v_a_34_);
v___x_43_ = 0;
v___x_44_ = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(v___x_44_, 0, v___x_25_);
lean_ctor_set_uint8(v___x_44_, 1, v___x_43_);
lean_ctor_set_uint8(v___x_44_, 2, v___x_43_);
lean_ctor_set_uint8(v___x_44_, 3, v___x_43_);
v___x_45_ = l_Lean_Fmt_Layouts_pseudoApplication(v___x_42_, v___x_44_);
if (v_isShared_38_ == 0)
{
lean_ctor_set(v___x_37_, 0, v___x_45_);
v___x_47_ = v___x_37_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_a_35_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
else
{
lean_dec(v_a_31_);
return v___x_33_;
}
}
else
{
lean_dec(v___x_23_);
return v___x_30_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtElabStxQuot___boxed(lean_object* v_x_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Fmt_fmtElabStxQuot(v_x_50_, v_a_51_, v_a_52_);
lean_dec_ref(v_a_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_61_ = l_Lean_Fmt_fmtAttribute;
v___x_62_ = ((lean_object*)(l_Lean_Fmt_fmtElabStxQuot___closed__5));
v___x_63_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___closed__2));
v___x_64_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtElabStxQuot___boxed), 3, 0);
v___x_65_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_61_, v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1___boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1();
return v_res_67_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_Quotation(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Lean_Elab_Quotation_0__Lean_Fmt_fmtElabStxQuot___regBuiltin_Lean_Fmt_fmtElabStxQuot__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Elab_Quotation(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Lean_Elab_Quotation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Elab_Quotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Quotation(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Lean_Elab_Quotation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Quotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Lean_Elab_Quotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Lean_Elab_Quotation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Lean_Elab_Quotation(builtin);
}
#ifdef __cplusplus
}
#endif
