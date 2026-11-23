// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Time.Notation.Spec
// Imports: public import Lean.Fmt.FmtM.Basic meta import Std.Time.Notation.Spec import Init.Data
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_metaApplication(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDatespec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtDatespec___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDatespec___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtDatespec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Time"};
static const lean_object* l_Lean_Fmt_fmtDatespec___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDatespec___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtDatespec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "termDatespec(_)"};
static const lean_object* l_Lean_Fmt_fmtDatespec___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtDatespec___closed__2_value;
static const lean_ctor_object l_Lean_Fmt_fmtDatespec___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDatespec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtDatespec___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDatespec___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDatespec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Lean_Fmt_fmtDatespec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDatespec___closed__3_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDatespec___closed__2_value),LEAN_SCALAR_PTR_LITERAL(118, 128, 190, 137, 197, 98, 142, 204)}};
static const lean_object* l_Lean_Fmt_fmtDatespec___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtDatespec___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtDatespec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Fmt_fmtDatespec___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtDatespec___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtDatespec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDatespec___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Fmt_fmtDatespec___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtDatespec___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDatespec(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDatespec___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "fmtDatespec"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(61, 41, 86, 210, 63, 3, 166, 98)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtDatespecWithConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "termDatespec(_,_)"};
static const lean_object* l_Lean_Fmt_fmtDatespecWithConfig___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtDatespecWithConfig___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtDatespecWithConfig___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtDatespec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtDatespecWithConfig___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDatespecWithConfig___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtDatespec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 230, 28, 41, 157, 98, 229, 68)}};
static const lean_ctor_object l_Lean_Fmt_fmtDatespecWithConfig___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtDatespecWithConfig___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtDatespecWithConfig___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 74, 99, 46, 223, 91, 91, 115)}};
static const lean_object* l_Lean_Fmt_fmtDatespecWithConfig___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtDatespecWithConfig___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDatespecWithConfig(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDatespecWithConfig___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtDatespecWithConfig"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 170, 205, 151, 220, 130, 63, 40)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDatespec(lean_object* v_x_11_, lean_object* v_a_12_, lean_object* v_a_13_){
_start:
{
lean_object* v___x_14_; uint8_t v___x_15_; 
v___x_14_ = ((lean_object*)(l_Lean_Fmt_fmtDatespec___closed__3));
lean_inc(v_x_11_);
v___x_15_ = l_Lean_Syntax_isOfKind(v_x_11_, v___x_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_x_11_);
v___x_16_ = l_Lean_Fmt_Error_partialFormatter;
v___x_17_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v_a_13_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; uint8_t v___x_21_; 
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = l_Lean_Syntax_getArg(v_x_11_, v___x_18_);
v___x_20_ = ((lean_object*)(l_Lean_Fmt_fmtDatespec___closed__5));
lean_inc(v___x_19_);
v___x_21_ = l_Lean_Syntax_isOfKind(v___x_19_, v___x_20_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v___x_19_);
lean_dec(v_x_11_);
v___x_22_ = l_Lean_Fmt_Error_partialFormatter;
v___x_23_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
lean_ctor_set(v___x_23_, 1, v_a_13_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v_lbTk_25_; lean_object* v___x_26_; 
v___x_24_ = lean_unsigned_to_nat(0u);
v_lbTk_25_ = l_Lean_Syntax_getArg(v_x_11_, v___x_24_);
v___x_26_ = l_Lean_Fmt_fmt(v_lbTk_25_, v_a_12_, v_a_13_);
if (lean_obj_tag(v___x_26_) == 0)
{
lean_object* v_a_27_; lean_object* v_a_28_; lean_object* v___x_29_; 
v_a_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_a_27_);
v_a_28_ = lean_ctor_get(v___x_26_, 1);
lean_inc(v_a_28_);
lean_dec_ref_known(v___x_26_, 2);
v___x_29_ = l_Lean_Fmt_fmt(v___x_19_, v_a_12_, v_a_28_);
if (lean_obj_tag(v___x_29_) == 0)
{
lean_object* v_a_30_; lean_object* v_a_31_; lean_object* v___x_32_; lean_object* v_rbTk_33_; lean_object* v___x_34_; 
v_a_30_ = lean_ctor_get(v___x_29_, 0);
lean_inc(v_a_30_);
v_a_31_ = lean_ctor_get(v___x_29_, 1);
lean_inc(v_a_31_);
lean_dec_ref_known(v___x_29_, 2);
v___x_32_ = lean_unsigned_to_nat(2u);
v_rbTk_33_ = l_Lean_Syntax_getArg(v_x_11_, v___x_32_);
lean_dec(v_x_11_);
v___x_34_ = l_Lean_Fmt_fmt(v_rbTk_33_, v_a_12_, v_a_31_);
if (lean_obj_tag(v___x_34_) == 0)
{
lean_object* v_a_35_; lean_object* v_a_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_48_; 
v_a_35_ = lean_ctor_get(v___x_34_, 0);
v_a_36_ = lean_ctor_get(v___x_34_, 1);
v_isSharedCheck_48_ = !lean_is_exclusive(v___x_34_);
if (v_isSharedCheck_48_ == 0)
{
v___x_38_ = v___x_34_;
v_isShared_39_ = v_isSharedCheck_48_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_a_36_);
lean_inc(v_a_35_);
lean_dec(v___x_34_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_48_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_40_ = lean_mk_empty_array_with_capacity(v___x_18_);
lean_inc_ref(v___x_40_);
v___x_41_ = lean_array_push(v___x_40_, v_a_30_);
v___x_42_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
v___x_43_ = lean_array_push(v___x_40_, v___x_42_);
v___x_44_ = l_Lean_Fmt_Layouts_metaApplication(v_a_27_, v___x_43_, v_a_35_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v___x_44_);
v___x_46_ = v___x_38_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v___x_44_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_a_36_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
else
{
lean_dec(v_a_30_);
lean_dec(v_a_27_);
return v___x_34_;
}
}
else
{
lean_dec(v_a_27_);
lean_dec(v_x_11_);
return v___x_29_;
}
}
else
{
lean_dec(v___x_19_);
lean_dec(v_x_11_);
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDatespec___boxed(lean_object* v_x_49_, lean_object* v_a_50_, lean_object* v_a_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Fmt_fmtDatespec(v_x_49_, v_a_50_, v_a_51_);
lean_dec_ref(v_a_50_);
return v_res_52_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_61_ = l_Lean_Fmt_fmtAttribute;
v___x_62_ = ((lean_object*)(l_Lean_Fmt_fmtDatespec___closed__3));
v___x_63_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___closed__3));
v___x_64_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDatespec___boxed), 3, 0);
v___x_65_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_61_, v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1___boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDatespecWithConfig(lean_object* v_x_73_, lean_object* v_a_74_, lean_object* v_a_75_){
_start:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
v___x_76_ = ((lean_object*)(l_Lean_Fmt_fmtDatespecWithConfig___closed__1));
lean_inc(v_x_73_);
v___x_77_ = l_Lean_Syntax_isOfKind(v_x_73_, v___x_76_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_dec(v_x_73_);
v___x_78_ = l_Lean_Fmt_Error_partialFormatter;
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v_a_75_);
return v___x_79_;
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_73_, v___x_80_);
v___x_82_ = ((lean_object*)(l_Lean_Fmt_fmtDatespec___closed__5));
lean_inc(v___x_81_);
v___x_83_ = l_Lean_Syntax_isOfKind(v___x_81_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; lean_object* v___x_85_; 
lean_dec(v___x_81_);
lean_dec(v_x_73_);
v___x_84_ = l_Lean_Fmt_Error_partialFormatter;
v___x_85_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v_a_75_);
return v___x_85_;
}
else
{
lean_object* v___x_86_; lean_object* v_lbTk_87_; lean_object* v___x_88_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v_lbTk_87_ = l_Lean_Syntax_getArg(v_x_73_, v___x_86_);
v___x_88_ = l_Lean_Fmt_fmt(v_lbTk_87_, v_a_74_, v_a_75_);
if (lean_obj_tag(v___x_88_) == 0)
{
lean_object* v_a_89_; lean_object* v_a_90_; lean_object* v___x_91_; 
v_a_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc(v_a_89_);
v_a_90_ = lean_ctor_get(v___x_88_, 1);
lean_inc(v_a_90_);
lean_dec_ref_known(v___x_88_, 2);
v___x_91_ = l_Lean_Fmt_fmt(v___x_81_, v_a_74_, v_a_90_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_94_; lean_object* v_commaTk_95_; lean_object* v___x_96_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
v_a_93_ = lean_ctor_get(v___x_91_, 1);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_91_, 2);
v___x_94_ = lean_unsigned_to_nat(2u);
v_commaTk_95_ = l_Lean_Syntax_getArg(v_x_73_, v___x_94_);
v___x_96_ = l_Lean_Fmt_fmt(v_commaTk_95_, v_a_74_, v_a_93_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_96_, 2);
v___x_99_ = lean_unsigned_to_nat(3u);
v___x_100_ = l_Lean_Syntax_getArg(v_x_73_, v___x_99_);
v___x_101_ = l_Lean_Fmt_fmt(v___x_100_, v_a_74_, v_a_98_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v_rbTk_105_; lean_object* v___x_106_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
v_a_103_ = lean_ctor_get(v___x_101_, 1);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_101_, 2);
v___x_104_ = lean_unsigned_to_nat(4u);
v_rbTk_105_ = l_Lean_Syntax_getArg(v_x_73_, v___x_104_);
lean_dec(v_x_73_);
v___x_106_ = l_Lean_Fmt_fmt(v_rbTk_105_, v_a_74_, v_a_103_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_126_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
v_a_108_ = lean_ctor_get(v___x_106_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_126_ == 0)
{
v___x_110_ = v___x_106_;
v_isShared_111_ = v_isSharedCheck_126_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_inc(v_a_107_);
lean_dec(v___x_106_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_126_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_112_ = lean_mk_empty_array_with_capacity(v___x_80_);
lean_inc_ref(v___x_112_);
v___x_113_ = lean_array_push(v___x_112_, v_a_92_);
v___x_114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
v___x_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_115_, 0, v_a_97_);
v___x_116_ = lean_array_push(v___x_112_, v_a_102_);
v___x_117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
v___x_118_ = lean_mk_empty_array_with_capacity(v___x_99_);
v___x_119_ = lean_array_push(v___x_118_, v___x_114_);
v___x_120_ = lean_array_push(v___x_119_, v___x_115_);
v___x_121_ = lean_array_push(v___x_120_, v___x_117_);
v___x_122_ = l_Lean_Fmt_Layouts_metaApplication(v_a_89_, v___x_121_, v_a_107_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_122_);
v___x_124_ = v___x_110_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v_a_108_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
else
{
lean_dec(v_a_102_);
lean_dec(v_a_97_);
lean_dec(v_a_92_);
lean_dec(v_a_89_);
return v___x_106_;
}
}
else
{
lean_dec(v_a_97_);
lean_dec(v_a_92_);
lean_dec(v_a_89_);
lean_dec(v_x_73_);
return v___x_101_;
}
}
else
{
lean_dec(v_a_92_);
lean_dec(v_a_89_);
lean_dec(v_x_73_);
return v___x_96_;
}
}
else
{
lean_dec(v_a_89_);
lean_dec(v_x_73_);
return v___x_91_;
}
}
else
{
lean_dec(v___x_81_);
lean_dec(v_x_73_);
return v___x_88_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtDatespecWithConfig___boxed(lean_object* v_x_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Fmt_fmtDatespecWithConfig(v_x_127_, v_a_128_, v_a_129_);
lean_dec_ref(v_a_128_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1(){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_137_ = l_Lean_Fmt_fmtAttribute;
v___x_138_ = ((lean_object*)(l_Lean_Fmt_fmtDatespecWithConfig___closed__1));
v___x_139_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___closed__1));
v___x_140_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtDatespecWithConfig___boxed), 3, 0);
v___x_141_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_137_, v___x_138_, v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1___boxed(lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1();
return v_res_143_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespec___regBuiltin_Lean_Fmt_fmtDatespec__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Time_Notation_Spec_0__Lean_Fmt_fmtDatespecWithConfig___regBuiltin_Lean_Fmt_fmtDatespecWithConfig__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Time_Notation_Spec(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Time_Notation_Spec(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Time_Notation_Spec(builtin);
}
#ifdef __cplusplus
}
#endif
