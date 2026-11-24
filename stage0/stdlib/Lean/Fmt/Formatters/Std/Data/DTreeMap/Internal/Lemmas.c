// Lean compiler output
// Module: Lean.Fmt.Formatters.Std.Data.DTreeMap.Internal.Lemmas
// Imports: public import Lean.Fmt.Formatters.Std.Data.DHashMap.Internal.RawLemmas public import Lean.Fmt.FmtM.Basic meta import Std.Data.DTreeMap.Internal.Lemmas import Init.Data
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Fmt_fmtSimpToModelLike(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__0_value;
static const lean_string_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DTreeMap"};
static const lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__1_value;
static const lean_string_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel___closed__2 = (const lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__2_value;
static const lean_string_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Impl"};
static const lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel___closed__3 = (const lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__3_value;
static const lean_string_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "tacticSimp_to_model[_]Using_"};
static const lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel___closed__4 = (const lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__4_value;
static const lean_ctor_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value_aux_0),((lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 1, 106, 2, 110, 100, 218, 30)}};
static const lean_ctor_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value_aux_1),((lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__2_value),LEAN_SCALAR_PTR_LITERAL(27, 108, 102, 221, 169, 83, 94, 148)}};
static const lean_ctor_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value_aux_2),((lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 90, 101, 118, 142, 120, 198, 229)}};
static const lean_ctor_object l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value_aux_3),((lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__4_value),LEAN_SCALAR_PTR_LITERAL(108, 149, 115, 22, 73, 250, 140, 17)}};
static const lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5 = (const lean_object*)&l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "fmtTreeMapSimpToModel"};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 13, 216, 5, 20, 224, 255, 184)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel(lean_object* v_x_12_, lean_object* v_a_13_, lean_object* v_a_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = ((lean_object*)(l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5));
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
lean_object* v___x_19_; lean_object* v_simpToModelTk_20_; lean_object* v___x_21_; lean_object* v_lbTk_x3f_23_; lean_object* v_names_x3f_24_; lean_object* v_rbTk_x3f_25_; lean_object* v___y_26_; lean_object* v___y_27_; lean_object* v___x_41_; uint8_t v___x_42_; 
v___x_19_ = lean_unsigned_to_nat(0u);
v_simpToModelTk_20_ = l_Lean_Syntax_getArg(v_x_12_, v___x_19_);
v___x_21_ = lean_unsigned_to_nat(1u);
v___x_41_ = l_Lean_Syntax_getArg(v_x_12_, v___x_21_);
v___x_42_ = l_Lean_Syntax_isNone(v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; uint8_t v___x_44_; 
v___x_43_ = lean_unsigned_to_nat(3u);
lean_inc(v___x_41_);
v___x_44_ = l_Lean_Syntax_matchesNull(v___x_41_, v___x_43_);
if (v___x_44_ == 0)
{
lean_object* v___x_45_; lean_object* v___x_46_; 
lean_dec(v___x_41_);
lean_dec(v_simpToModelTk_20_);
lean_dec(v_x_12_);
v___x_45_ = l_Lean_Fmt_Error_partialFormatter;
v___x_46_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v_a_14_);
return v___x_46_;
}
else
{
lean_object* v_lbTk_x3f_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v_rbTk_x3f_50_; lean_object* v_names_x3f_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v_lbTk_x3f_47_ = l_Lean_Syntax_getArg(v___x_41_, v___x_19_);
v___x_48_ = l_Lean_Syntax_getArg(v___x_41_, v___x_21_);
v___x_49_ = lean_unsigned_to_nat(2u);
v_rbTk_x3f_50_ = l_Lean_Syntax_getArg(v___x_41_, v___x_49_);
lean_dec(v___x_41_);
v_names_x3f_51_ = l_Lean_Syntax_getArgs(v___x_48_);
lean_dec(v___x_48_);
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v_lbTk_x3f_47_);
v___x_53_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_53_, 0, v_names_x3f_51_);
v___x_54_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_54_, 0, v_rbTk_x3f_50_);
v_lbTk_x3f_23_ = v___x_52_;
v_names_x3f_24_ = v___x_53_;
v_rbTk_x3f_25_ = v___x_54_;
v___y_26_ = v_a_13_;
v___y_27_ = v_a_14_;
goto v___jp_22_;
}
}
else
{
lean_object* v___x_55_; 
lean_dec(v___x_41_);
v___x_55_ = lean_box(0);
v_lbTk_x3f_23_ = v___x_55_;
v_names_x3f_24_ = v___x_55_;
v_rbTk_x3f_25_ = v___x_55_;
v___y_26_ = v_a_13_;
v___y_27_ = v_a_14_;
goto v___jp_22_;
}
v___jp_22_:
{
lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_28_ = lean_unsigned_to_nat(2u);
v___x_29_ = l_Lean_Syntax_getArg(v_x_12_, v___x_28_);
lean_dec(v_x_12_);
v___x_30_ = l_Lean_Syntax_isNone(v___x_29_);
if (v___x_30_ == 0)
{
uint8_t v___x_31_; 
lean_inc(v___x_29_);
v___x_31_ = l_Lean_Syntax_matchesNull(v___x_29_, v___x_28_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; 
lean_dec(v___x_29_);
lean_dec(v_rbTk_x3f_25_);
lean_dec(v_names_x3f_24_);
lean_dec(v_lbTk_x3f_23_);
lean_dec(v_simpToModelTk_20_);
v___x_32_ = l_Lean_Fmt_Error_partialFormatter;
v___x_33_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v___y_27_);
return v___x_33_;
}
else
{
lean_object* v_usingTk_x3f_34_; lean_object* v_usingArg_x3f_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_usingTk_x3f_34_ = l_Lean_Syntax_getArg(v___x_29_, v___x_19_);
v_usingArg_x3f_35_ = l_Lean_Syntax_getArg(v___x_29_, v___x_21_);
lean_dec(v___x_29_);
v___x_36_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_36_, 0, v_usingTk_x3f_34_);
v___x_37_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_37_, 0, v_usingArg_x3f_35_);
v___x_38_ = l_Lean_Fmt_fmtSimpToModelLike(v_simpToModelTk_20_, v_lbTk_x3f_23_, v_names_x3f_24_, v_rbTk_x3f_25_, v___x_36_, v___x_37_, v___y_26_, v___y_27_);
return v___x_38_;
}
}
else
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_dec(v___x_29_);
v___x_39_ = lean_box(0);
v___x_40_ = l_Lean_Fmt_fmtSimpToModelLike(v_simpToModelTk_20_, v_lbTk_x3f_23_, v_names_x3f_24_, v_rbTk_x3f_25_, v___x_39_, v___x_39_, v___y_26_, v___y_27_);
return v___x_40_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtTreeMapSimpToModel___boxed(lean_object* v_x_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Fmt_fmtTreeMapSimpToModel(v_x_56_, v_a_57_, v_a_58_);
lean_dec_ref(v_a_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1(){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_68_ = l_Lean_Fmt_fmtAttribute;
v___x_69_ = ((lean_object*)(l_Lean_Fmt_fmtTreeMapSimpToModel___closed__5));
v___x_70_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___closed__3));
v___x_71_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtTreeMapSimpToModel___boxed), 3, 0);
v___x_72_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_68_, v___x_69_, v___x_70_, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1___boxed(lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1();
return v_res_74_;
}
}
lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas_0__Lean_Fmt_fmtTreeMapSimpToModel___regBuiltin_Lean_Fmt_fmtTreeMapSimpToModel__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_Formatters_Std_Data_DHashMap_Internal_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Std_Data_DTreeMap_Internal_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
