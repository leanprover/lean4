// Lean compiler output
// Module: Lean.Fmt.Formatters.Init.Data.List.Notation
// Imports: public import Lean.Fmt.FmtM.Basic meta import Init.Data.List.Notation import Lean.Fmt.FmtM.CommonFormatters import Init.Data
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
extern lean_object* l_Lean_Fmt_fmtAttribute;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Fmt_Error_partialFormatter;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Fmt_fmtArrayLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_fmtListLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term[_]"};
static const lean_object* l_Lean_Fmt_fmtListLit___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtListLit___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtListLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtListLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 147, 168, 74, 195, 98, 232, 161)}};
static const lean_object* l_Lean_Fmt_fmtListLit___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtListLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtListLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtListLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__0_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fmt"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__1_value;
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "fmtListLit"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__2 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(217, 243, 196, 116, 221, 171, 148, 153)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__3 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_fmtListTreeLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "listTreeLit"};
static const lean_object* l_Lean_Fmt_fmtListTreeLit___closed__0 = (const lean_object*)&l_Lean_Fmt_fmtListTreeLit___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_fmtListTreeLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_fmtListTreeLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 194, 89, 43, 254, 92, 144, 135)}};
static const lean_object* l_Lean_Fmt_fmtListTreeLit___closed__1 = (const lean_object*)&l_Lean_Fmt_fmtListTreeLit___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtListTreeLit(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtListTreeLit___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "fmtListTreeLit"};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__0 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(76, 82, 26, 235, 141, 57, 128, 249)}};
static const lean_ctor_object l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(208, 138, 166, 193, 152, 249, 225, 143)}};
static const lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__1 = (const lean_object*)&l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1();
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtListLit(lean_object* v_x_4_, lean_object* v_a_5_, lean_object* v_a_6_){
_start:
{
lean_object* v___x_7_; uint8_t v___x_8_; 
v___x_7_ = ((lean_object*)(l_Lean_Fmt_fmtListLit___closed__1));
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
lean_object* v___x_11_; lean_object* v_lbTk_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v_rbTk_16_; lean_object* v_elems_17_; lean_object* v___x_18_; 
v___x_11_ = lean_unsigned_to_nat(0u);
v_lbTk_12_ = l_Lean_Syntax_getArg(v_x_4_, v___x_11_);
v___x_13_ = lean_unsigned_to_nat(1u);
v___x_14_ = l_Lean_Syntax_getArg(v_x_4_, v___x_13_);
v___x_15_ = lean_unsigned_to_nat(2u);
v_rbTk_16_ = l_Lean_Syntax_getArg(v_x_4_, v___x_15_);
lean_dec(v_x_4_);
v_elems_17_ = l_Lean_Syntax_getArgs(v___x_14_);
lean_dec(v___x_14_);
v___x_18_ = l_Lean_Fmt_fmtArrayLit___redArg(v_lbTk_12_, v_elems_17_, v_rbTk_16_, v_a_5_, v_a_6_);
lean_dec_ref(v_elems_17_);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtListLit___boxed(lean_object* v_x_19_, lean_object* v_a_20_, lean_object* v_a_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Fmt_fmtListLit(v_x_19_, v_a_20_, v_a_21_);
lean_dec_ref(v_a_20_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1(){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_31_ = l_Lean_Fmt_fmtAttribute;
v___x_32_ = ((lean_object*)(l_Lean_Fmt_fmtListLit___closed__1));
v___x_33_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___closed__3));
v___x_34_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtListLit___boxed), 3, 0);
v___x_35_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_31_, v___x_32_, v___x_33_, v___x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1___boxed(lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1();
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtListTreeLit(lean_object* v_x_41_, lean_object* v_a_42_, lean_object* v_a_43_){
_start:
{
lean_object* v___x_44_; uint8_t v___x_45_; 
v___x_44_ = ((lean_object*)(l_Lean_Fmt_fmtListTreeLit___closed__1));
lean_inc(v_x_41_);
v___x_45_ = l_Lean_Syntax_isOfKind(v_x_41_, v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; 
lean_dec(v_x_41_);
v___x_46_ = l_Lean_Fmt_Error_partialFormatter;
v___x_47_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v_a_43_);
return v___x_47_;
}
else
{
lean_object* v___x_48_; lean_object* v_lbTk_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v_rbTk_53_; lean_object* v_elems_54_; lean_object* v___x_55_; 
v___x_48_ = lean_unsigned_to_nat(0u);
v_lbTk_49_ = l_Lean_Syntax_getArg(v_x_41_, v___x_48_);
v___x_50_ = lean_unsigned_to_nat(1u);
v___x_51_ = l_Lean_Syntax_getArg(v_x_41_, v___x_50_);
v___x_52_ = lean_unsigned_to_nat(2u);
v_rbTk_53_ = l_Lean_Syntax_getArg(v_x_41_, v___x_52_);
lean_dec(v_x_41_);
v_elems_54_ = l_Lean_Syntax_getArgs(v___x_51_);
lean_dec(v___x_51_);
v___x_55_ = l_Lean_Fmt_fmtArrayLit___redArg(v_lbTk_49_, v_elems_54_, v_rbTk_53_, v_a_42_, v_a_43_);
lean_dec_ref(v_elems_54_);
return v___x_55_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_fmtListTreeLit___boxed(lean_object* v_x_56_, lean_object* v_a_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_Fmt_fmtListTreeLit(v_x_56_, v_a_57_, v_a_58_);
lean_dec_ref(v_a_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1(){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_66_ = l_Lean_Fmt_fmtAttribute;
v___x_67_ = ((lean_object*)(l_Lean_Fmt_fmtListTreeLit___closed__1));
v___x_68_ = ((lean_object*)(l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___closed__1));
v___x_69_ = lean_alloc_closure((void*)(l_Lean_Fmt_fmtListTreeLit___boxed), 3, 0);
v___x_70_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_66_, v___x_67_, v___x_68_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1___boxed(lean_object* v_a_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1();
return v_res_72_;
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* runtime_initialize_Init_Data(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Formatters_Init_Data_List_Notation(uint8_t builtin) {
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
res = l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListLit___regBuiltin_Lean_Fmt_fmtListLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Fmt_Formatters_Init_Data_List_Notation_0__Lean_Fmt_fmtListTreeLit___regBuiltin_Lean_Fmt_fmtListTreeLit__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Data_List_Notation(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Formatters_Init_Data_List_Notation(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Notation(uint8_t builtin);
lean_object* initialize_Lean_Fmt_FmtM_CommonFormatters(uint8_t builtin);
lean_object* initialize_Init_Data(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Formatters_Init_Data_List_Notation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Fmt_FmtM_CommonFormatters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Formatters_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Formatters_Init_Data_List_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Formatters_Init_Data_List_Notation(builtin);
}
#ifdef __cplusplus
}
#endif
