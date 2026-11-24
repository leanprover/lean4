// Lean compiler output
// Module: Lake.Formatters.Util.Family
// Imports: public import Lean.Fmt.FmtM.Basic meta import Lake.Util.Family import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Fmt_fmt(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtAppLike(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_globalSignature(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Fmt_Layouts_assignmentDeclaration(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Fmt_fmtDeclWithModifiers(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Formatters_fmtFamilyDef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__0 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__0_value;
static const lean_ctor_object l_Lake_Formatters_fmtFamilyDef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__1 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__1_value;
static const lean_array_object l_Lake_Formatters_fmtFamilyDef___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__2 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__2_value;
static const lean_string_object l_Lake_Formatters_fmtFamilyDef___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__3 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__3_value;
static const lean_string_object l_Lake_Formatters_fmtFamilyDef___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "familyDef"};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__4 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__4_value;
static const lean_ctor_object l_Lake_Formatters_fmtFamilyDef___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Formatters_fmtFamilyDef___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__5_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__4_value),LEAN_SCALAR_PTR_LITERAL(59, 240, 138, 11, 51, 35, 78, 153)}};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__5 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__5_value;
static const lean_string_object l_Lake_Formatters_fmtFamilyDef___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__6 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__6_value;
static const lean_string_object l_Lake_Formatters_fmtFamilyDef___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__7 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__7_value;
static const lean_string_object l_Lake_Formatters_fmtFamilyDef___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__8 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__8_value;
static const lean_string_object l_Lake_Formatters_fmtFamilyDef___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "docComment"};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__9 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__9_value;
static const lean_ctor_object l_Lake_Formatters_fmtFamilyDef___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lake_Formatters_fmtFamilyDef___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__10_value_aux_0),((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__7_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lake_Formatters_fmtFamilyDef___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__10_value_aux_1),((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__8_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l_Lake_Formatters_fmtFamilyDef___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__10_value_aux_2),((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__9_value),LEAN_SCALAR_PTR_LITERAL(44, 76, 179, 33, 27, 4, 201, 125)}};
static const lean_object* l_Lake_Formatters_fmtFamilyDef___closed__10 = (const lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__10_value;
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFamilyDef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFamilyDef___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Formatters"};
static const lean_object* l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__0 = (const lean_object*)&l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__0_value;
static const lean_string_object l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "fmtFamilyDef"};
static const lean_object* l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__1 = (const lean_object*)&l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__1_value;
static const lean_ctor_object l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_Formatters_fmtFamilyDef___closed__3_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__2_value_aux_0),((lean_object*)&l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 221, 165, 186, 116, 133, 231, 135)}};
static const lean_ctor_object l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__2_value_aux_1),((lean_object*)&l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(184, 243, 73, 77, 63, 67, 75, 10)}};
static const lean_object* l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__2 = (const lean_object*)&l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1();
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFamilyDef(lean_object* v_x_20_, lean_object* v_a_21_, lean_object* v_a_22_){
_start:
{
lean_object* v_docComment_x3f_24_; lean_object* v___y_25_; lean_object* v___y_26_; lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = ((lean_object*)(l_Lake_Formatters_fmtFamilyDef___closed__5));
lean_inc(v_x_20_);
v___x_78_ = l_Lean_Syntax_isOfKind(v_x_20_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec(v_x_20_);
v___x_79_ = l_Lean_Fmt_Error_partialFormatter;
v___x_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v_a_22_);
return v___x_80_;
}
else
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = lean_unsigned_to_nat(0u);
v___x_82_ = l_Lean_Syntax_getArg(v_x_20_, v___x_81_);
v___x_83_ = l_Lean_Syntax_isNone(v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(1u);
lean_inc(v___x_82_);
v___x_85_ = l_Lean_Syntax_matchesNull(v___x_82_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_dec(v___x_82_);
lean_dec(v_x_20_);
v___x_86_ = l_Lean_Fmt_Error_partialFormatter;
v___x_87_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_a_22_);
return v___x_87_;
}
else
{
lean_object* v_docComment_x3f_88_; lean_object* v___x_89_; uint8_t v___x_90_; 
v_docComment_x3f_88_ = l_Lean_Syntax_getArg(v___x_82_, v___x_81_);
lean_dec(v___x_82_);
v___x_89_ = ((lean_object*)(l_Lake_Formatters_fmtFamilyDef___closed__10));
lean_inc(v_docComment_x3f_88_);
v___x_90_ = l_Lean_Syntax_isOfKind(v_docComment_x3f_88_, v___x_89_);
if (v___x_90_ == 0)
{
lean_object* v___x_91_; lean_object* v___x_92_; 
lean_dec(v_docComment_x3f_88_);
lean_dec(v_x_20_);
v___x_91_ = l_Lean_Fmt_Error_partialFormatter;
v___x_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v_a_22_);
return v___x_92_;
}
else
{
lean_object* v___x_93_; 
v___x_93_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_93_, 0, v_docComment_x3f_88_);
v_docComment_x3f_24_ = v___x_93_;
v___y_25_ = v_a_21_;
v___y_26_ = v_a_22_;
goto v___jp_23_;
}
}
}
else
{
lean_object* v___x_94_; 
lean_dec(v___x_82_);
v___x_94_ = lean_box(0);
v_docComment_x3f_24_ = v___x_94_;
v___y_25_ = v_a_21_;
v___y_26_ = v_a_22_;
goto v___jp_23_;
}
}
v___jp_23_:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_27_ = lean_unsigned_to_nat(2u);
v___x_28_ = l_Lean_Syntax_getArg(v_x_20_, v___x_27_);
v___x_29_ = ((lean_object*)(l_Lake_Formatters_fmtFamilyDef___closed__1));
lean_inc(v___x_28_);
v___x_30_ = l_Lean_Syntax_isOfKind(v___x_28_, v___x_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
lean_dec(v___x_28_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
v___x_31_ = l_Lean_Fmt_Error_partialFormatter;
v___x_32_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___y_26_);
return v___x_32_;
}
else
{
lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
v___x_33_ = lean_unsigned_to_nat(4u);
v___x_34_ = l_Lean_Syntax_getArg(v_x_20_, v___x_33_);
lean_inc(v___x_34_);
v___x_35_ = l_Lean_Syntax_isOfKind(v___x_34_, v___x_29_);
if (v___x_35_ == 0)
{
lean_object* v___x_36_; lean_object* v___x_37_; 
lean_dec(v___x_34_);
lean_dec(v___x_28_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
v___x_36_ = l_Lean_Fmt_Error_partialFormatter;
v___x_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
lean_ctor_set(v___x_37_, 1, v___y_26_);
return v___x_37_;
}
else
{
lean_object* v___x_38_; lean_object* v_familyDefTk_39_; lean_object* v___x_40_; 
v___x_38_ = lean_unsigned_to_nat(1u);
v_familyDefTk_39_ = l_Lean_Syntax_getArg(v_x_20_, v___x_38_);
v___x_40_ = l_Lean_Fmt_fmt(v_familyDefTk_39_, v___y_25_, v___y_26_);
if (lean_obj_tag(v___x_40_) == 0)
{
lean_object* v_a_41_; lean_object* v_a_42_; lean_object* v___x_43_; 
v_a_41_ = lean_ctor_get(v___x_40_, 0);
lean_inc(v_a_41_);
v_a_42_ = lean_ctor_get(v___x_40_, 1);
lean_inc(v_a_42_);
lean_dec_ref_known(v___x_40_, 2);
v___x_43_ = l_Lean_Fmt_fmt(v___x_28_, v___y_25_, v_a_42_);
if (lean_obj_tag(v___x_43_) == 0)
{
lean_object* v_a_44_; lean_object* v_a_45_; lean_object* v___x_46_; lean_object* v_typeAscriptionTk_47_; lean_object* v___x_48_; 
v_a_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc(v_a_44_);
v_a_45_ = lean_ctor_get(v___x_43_, 1);
lean_inc(v_a_45_);
lean_dec_ref_known(v___x_43_, 2);
v___x_46_ = lean_unsigned_to_nat(3u);
v_typeAscriptionTk_47_ = l_Lean_Syntax_getArg(v_x_20_, v___x_46_);
v___x_48_ = l_Lean_Fmt_fmt(v_typeAscriptionTk_47_, v___y_25_, v_a_45_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v_a_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_a_49_);
v_a_50_ = lean_ctor_get(v___x_48_, 1);
lean_inc(v_a_50_);
lean_dec_ref_known(v___x_48_, 2);
v___x_51_ = lean_unsigned_to_nat(5u);
v___x_52_ = l_Lean_Syntax_getArg(v_x_20_, v___x_51_);
v___x_53_ = lean_mk_empty_array_with_capacity(v___x_27_);
lean_inc_ref(v___x_53_);
v___x_54_ = lean_array_push(v___x_53_, v___x_34_);
v___x_55_ = lean_array_push(v___x_54_, v___x_52_);
v___x_56_ = l_Lean_Fmt_fmtAppLike(v___x_55_, v___y_25_, v_a_50_);
if (lean_obj_tag(v___x_56_) == 0)
{
lean_object* v_a_57_; lean_object* v_a_58_; lean_object* v___x_59_; lean_object* v_colonEqTk_60_; lean_object* v___x_61_; 
v_a_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc(v_a_57_);
v_a_58_ = lean_ctor_get(v___x_56_, 1);
lean_inc(v_a_58_);
lean_dec_ref_known(v___x_56_, 2);
v___x_59_ = lean_unsigned_to_nat(6u);
v_colonEqTk_60_ = l_Lean_Syntax_getArg(v_x_20_, v___x_59_);
v___x_61_ = l_Lean_Fmt_fmt(v_colonEqTk_60_, v___y_25_, v_a_58_);
if (lean_obj_tag(v___x_61_) == 0)
{
lean_object* v_a_62_; lean_object* v_a_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_a_62_ = lean_ctor_get(v___x_61_, 0);
lean_inc(v_a_62_);
v_a_63_ = lean_ctor_get(v___x_61_, 1);
lean_inc(v_a_63_);
lean_dec_ref_known(v___x_61_, 2);
v___x_64_ = lean_unsigned_to_nat(7u);
v___x_65_ = l_Lean_Syntax_getArg(v_x_20_, v___x_64_);
lean_dec(v_x_20_);
v___x_66_ = l_Lean_Fmt_fmt(v___x_65_, v___y_25_, v_a_63_);
if (lean_obj_tag(v___x_66_) == 0)
{
lean_object* v_a_67_; lean_object* v_a_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_a_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_a_67_);
v_a_68_ = lean_ctor_get(v___x_66_, 1);
lean_inc(v_a_68_);
lean_dec_ref_known(v___x_66_, 2);
v___x_69_ = lean_array_push(v___x_53_, v_a_41_);
v___x_70_ = lean_array_push(v___x_69_, v_a_44_);
v___x_71_ = ((lean_object*)(l_Lake_Formatters_fmtFamilyDef___closed__2));
v___x_72_ = l_Lean_Fmt_Layouts_globalSignature(v___x_70_, v___x_71_, v_a_49_, v_a_57_);
lean_dec_ref(v___x_70_);
v___x_73_ = 0;
v___x_74_ = l_Lean_Fmt_Layouts_assignmentDeclaration(v___x_72_, v_a_62_, v_a_67_, v___x_73_);
v___x_75_ = lean_box(0);
v___x_76_ = l_Lean_Fmt_fmtDeclWithModifiers(v_docComment_x3f_24_, v___x_75_, v___x_71_, v___x_74_, v___y_25_, v_a_68_);
return v___x_76_;
}
else
{
lean_dec(v_a_62_);
lean_dec(v_a_57_);
lean_dec_ref(v___x_53_);
lean_dec(v_a_49_);
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec(v_docComment_x3f_24_);
return v___x_66_;
}
}
else
{
lean_dec(v_a_57_);
lean_dec_ref(v___x_53_);
lean_dec(v_a_49_);
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
return v___x_61_;
}
}
else
{
lean_dec_ref(v___x_53_);
lean_dec(v_a_49_);
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
return v___x_56_;
}
}
else
{
lean_dec(v_a_44_);
lean_dec(v_a_41_);
lean_dec(v___x_34_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
return v___x_48_;
}
}
else
{
lean_dec(v_a_41_);
lean_dec(v___x_34_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
return v___x_43_;
}
}
else
{
lean_dec(v___x_34_);
lean_dec(v___x_28_);
lean_dec(v_docComment_x3f_24_);
lean_dec(v_x_20_);
return v___x_40_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Formatters_fmtFamilyDef___boxed(lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lake_Formatters_fmtFamilyDef(v_x_95_, v_a_96_, v_a_97_);
lean_dec_ref(v_a_96_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1(){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_106_ = l_Lean_Fmt_fmtAttribute;
v___x_107_ = ((lean_object*)(l_Lake_Formatters_fmtFamilyDef___closed__5));
v___x_108_ = ((lean_object*)(l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___closed__2));
v___x_109_ = lean_alloc_closure((void*)(l_Lake_Formatters_fmtFamilyDef___boxed), 3, 0);
v___x_110_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_106_, v___x_107_, v___x_108_, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1___boxed(lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1();
return v_res_112_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Formatters_Util_Family(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lake_Formatters_Util_Family_0__Lake_Formatters_fmtFamilyDef___regBuiltin_Lake_Formatters_fmtFamilyDef__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lake_Util_Family(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Formatters_Util_Family(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lake_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Lake_Util_Family(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Formatters_Util_Family(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Formatters_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Formatters_Util_Family(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Formatters_Util_Family(builtin);
}
#ifdef __cplusplus
}
#endif
