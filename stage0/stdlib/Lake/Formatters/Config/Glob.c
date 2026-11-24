// Lean compiler output
// Module: Lake.Formatters.Config.Glob
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lake.Config.Glob import Init.Data
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_atomic(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Formatters_fmtGlobAndSubmodules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_Formatters_fmtGlobAndSubmodules___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__0_value;
static const lean_string_object l_Lake_Formatters_fmtGlobAndSubmodules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term__.*"};
static const lean_object* l_Lake_Formatters_fmtGlobAndSubmodules___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__1_value;
static const lean_ctor_object l_Lake_Formatters_fmtGlobAndSubmodules___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtGlobAndSubmodules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__2_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(61, 124, 105, 77, 27, 110, 223, 140)}};
static const lean_object* l_Lake_Formatters_fmtGlobAndSubmodules___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__2_value;
static const lean_string_object l_Lake_Formatters_fmtGlobAndSubmodules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* l_Lake_Formatters_fmtGlobAndSubmodules___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__3_value;
static const lean_ctor_object l_Lake_Formatters_fmtGlobAndSubmodules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__3_value),LEAN_SCALAR_PTR_LITERAL(84, 246, 234, 130, 97, 205, 144, 82)}};
static const lean_object* l_Lake_Formatters_fmtGlobAndSubmodules___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__4_value;
static const lean_string_object l_Lake_Formatters_fmtGlobAndSubmodules___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Lake_Formatters_fmtGlobAndSubmodules___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__5_value;
static const lean_ctor_object l_Lake_Formatters_fmtGlobAndSubmodules___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Lake_Formatters_fmtGlobAndSubmodules___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__6_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGlobAndSubmodules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGlobAndSubmodules___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Formatters"};
static const lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__0_value;
static const lean_string_object l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "fmtGlobAndSubmodules"};
static const lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__1_value;
static const lean_ctor_object l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 50, 7, 207, 235, 241, 222, 105)}};
static const lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__2 = (const lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___boxed(lean_object*);
static const lean_string_object l_Lake_Formatters_fmtGlobSubmodules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term__.+"};
static const lean_object* l_Lake_Formatters_fmtGlobSubmodules___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtGlobSubmodules___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtGlobSubmodules___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtGlobSubmodules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtGlobSubmodules___closed__1_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtGlobSubmodules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(20, 74, 46, 183, 128, 87, 172, 156)}};
static const lean_object* l_Lake_Formatters_fmtGlobSubmodules___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtGlobSubmodules___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGlobSubmodules(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGlobSubmodules___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "fmtGlobSubmodules"};
static const lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__0_value;
static const lean_ctor_object l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtGlobAndSubmodules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 190, 204, 151, 143, 75, 17, 222)}};
static const lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGlobAndSubmodules(lean_object* v_x_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = ((lean_object*)(l_Lake_Formatters_fmtGlobAndSubmodules___closed__2));
lean_inc(v_x_12_);
v___x_16_ = l_Lean_Syntax_isOfKind(v_x_12_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; 
lean_dec(v_x_12_);
v___x_17_ = l_Lean_Fmt_Error_partialFormatter;
v___x_18_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_17_);
lean_ctor_set(v___x_18_, 1, v_a_14_);
return v___x_18_;
}
else
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; uint8_t v___x_22_; 
v___x_19_ = lean_unsigned_to_nat(0u);
v___x_20_ = l_Lean_Syntax_getArg(v_x_12_, v___x_19_);
v___x_21_ = ((lean_object*)(l_Lake_Formatters_fmtGlobAndSubmodules___closed__4));
lean_inc(v___x_20_);
v___x_22_ = l_Lean_Syntax_isOfKind(v___x_20_, v___x_21_);
if (v___x_22_ == 0)
{
lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v___x_20_);
lean_dec(v_x_12_);
v___x_23_ = l_Lean_Fmt_Error_partialFormatter;
v___x_24_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_23_);
lean_ctor_set(v___x_24_, 1, v_a_14_);
return v___x_24_;
}
else
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; uint8_t v___x_28_; 
v___x_25_ = lean_unsigned_to_nat(1u);
v___x_26_ = l_Lean_Syntax_getArg(v_x_12_, v___x_25_);
v___x_27_ = ((lean_object*)(l_Lake_Formatters_fmtGlobAndSubmodules___closed__6));
v___x_28_ = l_Lean_Syntax_isOfKind(v___x_26_, v___x_27_);
if (v___x_28_ == 0)
{
lean_object* v___x_29_; lean_object* v___x_30_; 
lean_dec(v___x_20_);
lean_dec(v_x_12_);
v___x_29_ = l_Lean_Fmt_Error_partialFormatter;
v___x_30_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v_a_14_);
return v___x_30_;
}
else
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Fmt_fmt(v___x_20_, v_a_13_, v_a_14_);
if (lean_obj_tag(v___x_31_) == 0)
{
lean_object* v_a_32_; lean_object* v_a_33_; lean_object* v___x_34_; lean_object* v_globTk_35_; lean_object* v___x_36_; 
v_a_32_ = lean_ctor_get(v___x_31_, 0);
lean_inc(v_a_32_);
v_a_33_ = lean_ctor_get(v___x_31_, 1);
lean_inc(v_a_33_);
lean_dec_ref_known(v___x_31_, 2);
v___x_34_ = lean_unsigned_to_nat(2u);
v_globTk_35_ = l_Lean_Syntax_getArg(v_x_12_, v___x_34_);
lean_dec(v_x_12_);
v___x_36_ = l_Lean_Fmt_fmt(v_globTk_35_, v_a_13_, v_a_33_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v_a_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_49_; 
v_a_37_ = lean_ctor_get(v___x_36_, 0);
v_a_38_ = lean_ctor_get(v___x_36_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_49_ == 0)
{
v___x_40_ = v___x_36_;
v_isShared_41_ = v_isSharedCheck_49_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_a_38_);
lean_inc(v_a_37_);
lean_dec(v___x_36_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_49_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_47_; 
v___x_42_ = lean_mk_empty_array_with_capacity(v___x_34_);
v___x_43_ = lean_array_push(v___x_42_, v_a_32_);
v___x_44_ = lean_array_push(v___x_43_, v_a_37_);
v___x_45_ = l_Lean_Fmt_Layouts_atomic(v___x_44_);
lean_dec_ref(v___x_44_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 0, v___x_45_);
v___x_47_ = v___x_40_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_a_38_);
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
lean_dec(v_a_32_);
return v___x_36_;
}
}
else
{
lean_dec(v_x_12_);
return v___x_31_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGlobAndSubmodules___boxed(lean_object* v_x_50_, lean_object* v_a_51_, lean_object* v_a_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lake_Formatters_fmtGlobAndSubmodules(v_x_50_, v_a_51_, v_a_52_);
lean_dec_ref(v_a_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1(){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_61_ = l_Lean_Fmt_fmtAttribute;
v___x_62_ = ((lean_object*)(l_Lake_Formatters_fmtGlobAndSubmodules___closed__2));
v___x_63_ = ((lean_object*)(l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___closed__2));
v___x_64_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtGlobAndSubmodules___boxed), 3, 0);
v___x_65_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_61_, v___x_62_, v___x_63_, v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1___boxed(lean_object* v_a_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1();
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGlobSubmodules(lean_object* v_x_72_, lean_object* v_a_73_, lean_object* v_a_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = ((lean_object*)(l_Lake_Formatters_fmtGlobSubmodules___closed__1));
lean_inc(v_x_72_);
v___x_76_ = l_Lean_Syntax_isOfKind(v_x_72_, v___x_75_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v___x_78_; 
lean_dec(v_x_72_);
v___x_77_ = l_Lean_Fmt_Error_partialFormatter;
v___x_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v_a_74_);
return v___x_78_;
}
else
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; uint8_t v___x_82_; 
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = l_Lean_Syntax_getArg(v_x_72_, v___x_79_);
v___x_81_ = ((lean_object*)(l_Lake_Formatters_fmtGlobAndSubmodules___closed__4));
lean_inc(v___x_80_);
v___x_82_ = l_Lean_Syntax_isOfKind(v___x_80_, v___x_81_);
if (v___x_82_ == 0)
{
lean_object* v___x_83_; lean_object* v___x_84_; 
lean_dec(v___x_80_);
lean_dec(v_x_72_);
v___x_83_ = l_Lean_Fmt_Error_partialFormatter;
v___x_84_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v_a_74_);
return v___x_84_;
}
else
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = l_Lean_Syntax_getArg(v_x_72_, v___x_85_);
v___x_87_ = ((lean_object*)(l_Lake_Formatters_fmtGlobAndSubmodules___closed__6));
v___x_88_ = l_Lean_Syntax_isOfKind(v___x_86_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; lean_object* v___x_90_; 
lean_dec(v___x_80_);
lean_dec(v_x_72_);
v___x_89_ = l_Lean_Fmt_Error_partialFormatter;
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v_a_74_);
return v___x_90_;
}
else
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_Fmt_fmt(v___x_80_, v_a_73_, v_a_74_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v_a_92_; lean_object* v_a_93_; lean_object* v___x_94_; lean_object* v_globTk_95_; lean_object* v___x_96_; 
v_a_92_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_a_92_);
v_a_93_ = lean_ctor_get(v___x_91_, 1);
lean_inc(v_a_93_);
lean_dec_ref_known(v___x_91_, 2);
v___x_94_ = lean_unsigned_to_nat(2u);
v_globTk_95_ = l_Lean_Syntax_getArg(v_x_72_, v___x_94_);
lean_dec(v_x_72_);
v___x_96_ = l_Lean_Fmt_fmt(v_globTk_95_, v_a_73_, v_a_93_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v_a_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_109_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
v_a_98_ = lean_ctor_get(v___x_96_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_109_ == 0)
{
v___x_100_ = v___x_96_;
v_isShared_101_ = v_isSharedCheck_109_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_a_98_);
lean_inc(v_a_97_);
lean_dec(v___x_96_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_109_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_107_; 
v___x_102_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_103_ = lean_array_push(v___x_102_, v_a_92_);
v___x_104_ = lean_array_push(v___x_103_, v_a_97_);
v___x_105_ = l_Lean_Fmt_Layouts_atomic(v___x_104_);
lean_dec_ref(v___x_104_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 0, v___x_105_);
v___x_107_ = v___x_100_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_105_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v_a_98_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
else
{
lean_dec(v_a_92_);
return v___x_96_;
}
}
else
{
lean_dec(v_x_72_);
return v___x_91_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtGlobSubmodules___boxed(lean_object* v_x_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lake_Formatters_fmtGlobSubmodules(v_x_110_, v_a_111_, v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1(){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_120_ = l_Lean_Fmt_fmtAttribute;
v___x_121_ = ((lean_object*)(l_Lake_Formatters_fmtGlobSubmodules___closed__1));
v___x_122_ = ((lean_object*)(l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___closed__1));
v___x_123_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtGlobSubmodules___boxed), 3, 0);
v___x_124_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_120_, v___x_121_, v___x_122_, v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1___boxed(lean_object* v_a_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1();
return v_res_126_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Formatters_Config_Glob(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobAndSubmodules___regBuiltin_Lake_Formatters_fmtGlobAndSubmodules__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Config_Glob_0__Lake_Formatters_fmtGlobSubmodules___regBuiltin_Lake_Formatters_fmtGlobSubmodules__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Config_Glob(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Formatters_Config_Glob(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Config_Glob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lake_Config_Glob(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Formatters_Config_Glob(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Glob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Formatters_Config_Glob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Formatters_Config_Glob(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Formatters_Config_Glob(builtin);
}
#ifdef __cplusplus
}
#endif
