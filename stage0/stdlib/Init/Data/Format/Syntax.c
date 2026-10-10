// Lean compiler output
// Module: Init.Data.Format.Syntax
// Imports: import Init.Data.ToString.Name public import Init.Data.ToString.Basic import Init.Data.Format.Instances import Init.Data.Format.Macro
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
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Function_comp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0 = (const lean_object*)&l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__0_value)}};
static const lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1 = (const lean_object*)&l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1_value;
static const lean_string_object l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!:"};
static const lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2 = (const lean_object*)&l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__2_value)}};
static const lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3 = (const lean_object*)&l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Syntax_formatStxAux_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__0 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__0_value;
static lean_once_cell_t l_Lean_Syntax_formatStxAux___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_formatStxAux___closed__2;
static lean_once_cell_t l_Lean_Syntax_formatStxAux___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_formatStxAux___closed__3;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_formatStxAux___closed__0_value)}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__4 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__4_value;
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__1 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__1_value;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_formatStxAux___closed__1_value)}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__5 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__5_value;
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "<missing>"};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__6 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__6_value;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_formatStxAux___closed__6_value)}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__7 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__7_value;
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ".."};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__8 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__8_value;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_formatStxAux___closed__8_value)}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__9 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__9_value;
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__10 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__10_value;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_formatStxAux___closed__10_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__11 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__11_value;
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__13 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__13_value;
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__12 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__12_value;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_formatStxAux___closed__12_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_formatStxAux___closed__14_value_aux_0),((lean_object*)&l_Lean_Syntax_formatStxAux___closed__13_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__14 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__14_value;
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__15 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__15_value;
static lean_once_cell_t l_Lean_Syntax_formatStxAux___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_formatStxAux___closed__17;
static lean_once_cell_t l_Lean_Syntax_formatStxAux___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Syntax_formatStxAux___closed__18;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_formatStxAux___closed__15_value)}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__19 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__19_value;
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__16 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__16_value;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_formatStxAux___closed__16_value)}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__20 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__20_value;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Syntax_formatStxAux___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__21 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__21_value;
static const lean_string_object l_Lean_Syntax_formatStxAux___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__22 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__22_value;
static const lean_ctor_object l_Lean_Syntax_formatStxAux___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Syntax_formatStxAux___closed__22_value)}};
static const lean_object* l_Lean_Syntax_formatStxAux___closed__23 = (const lean_object*)&l_Lean_Syntax_formatStxAux___closed__23_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormat___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instToFormat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instToFormat___closed__0 = (const lean_object*)&l_Lean_Syntax_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instToFormat = (const lean_object*)&l_Lean_Syntax_instToFormat___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instToString___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instToString___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instToString___closed__0 = (const lean_object*)&l_Lean_Syntax_instToString___closed__0_value;
static const lean_closure_object l_Lean_Syntax_instToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Function_comp, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Syntax_instToString___closed__0_value),((lean_object*)&l_Lean_Syntax_instToFormat___closed__0_value)} };
static const lean_object* l_Lean_Syntax_instToString___closed__1 = (const lean_object*)&l_Lean_Syntax_instToString___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Syntax_instToString = (const lean_object*)&l_Lean_Syntax_instToString___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_instToFormatTSyntax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instToFormatTSyntax___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instToFormatTSyntax___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instToFormatTSyntax___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___redArg___lam__0(lean_object*);
static const lean_closure_object l_Lean_Syntax_instToStringTSyntax___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Syntax_instToStringTSyntax___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Syntax_instToStringTSyntax___redArg___closed__0 = (const lean_object*)&l_Lean_Syntax_instToStringTSyntax___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___redArg();
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___boxed(lean_object*);
lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(uint8_t v_showInfo_7_, lean_object* v_info_8_, lean_object* v_f_9_){
_start:
{
if (v_showInfo_7_ == 1)
{
switch(lean_obj_tag(v_info_8_))
{
case 0:
{
lean_object* v_leading_10_; lean_object* v_pos_11_; lean_object* v_trailing_12_; lean_object* v_endPos_13_; lean_object* v_str_14_; lean_object* v_startPos_15_; lean_object* v_stopPos_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v_str_22_; lean_object* v_startPos_23_; lean_object* v_stopPos_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v_leading_10_ = lean_ctor_get(v_info_8_, 0);
lean_inc_ref(v_leading_10_);
v_pos_11_ = lean_ctor_get(v_info_8_, 1);
lean_inc(v_pos_11_);
v_trailing_12_ = lean_ctor_get(v_info_8_, 2);
lean_inc_ref(v_trailing_12_);
v_endPos_13_ = lean_ctor_get(v_info_8_, 3);
lean_inc(v_endPos_13_);
lean_dec_ref_known(v_info_8_, 4);
v_str_14_ = lean_ctor_get(v_leading_10_, 0);
lean_inc_ref(v_str_14_);
v_startPos_15_ = lean_ctor_get(v_leading_10_, 1);
lean_inc(v_startPos_15_);
v_stopPos_16_ = lean_ctor_get(v_leading_10_, 2);
lean_inc(v_stopPos_16_);
lean_dec_ref(v_leading_10_);
v___x_17_ = lean_string_utf8_extract(v_str_14_, v_startPos_15_, v_stopPos_16_);
lean_dec(v_stopPos_16_);
lean_dec(v_startPos_15_);
lean_dec_ref(v_str_14_);
v___x_18_ = l_String_quote(v___x_17_);
v___x_19_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
v___x_20_ = ((lean_object*)(l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1));
v___x_21_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_19_);
lean_ctor_set(v___x_21_, 1, v___x_20_);
v_str_22_ = lean_ctor_get(v_trailing_12_, 0);
lean_inc_ref(v_str_22_);
v_startPos_23_ = lean_ctor_get(v_trailing_12_, 1);
lean_inc(v_startPos_23_);
v_stopPos_24_ = lean_ctor_get(v_trailing_12_, 2);
lean_inc(v_stopPos_24_);
lean_dec_ref(v_trailing_12_);
v___x_25_ = l_Nat_reprFast(v_pos_11_);
v___x_26_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
v___x_27_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_27_, 0, v___x_21_);
lean_ctor_set(v___x_27_, 1, v___x_26_);
v___x_28_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
lean_ctor_set(v___x_28_, 1, v___x_20_);
v___x_29_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v_f_9_);
v___x_30_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_30_, 0, v___x_29_);
lean_ctor_set(v___x_30_, 1, v___x_20_);
v___x_31_ = l_Nat_reprFast(v_endPos_13_);
v___x_32_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
v___x_33_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_30_);
lean_ctor_set(v___x_33_, 1, v___x_32_);
v___x_34_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_20_);
v___x_35_ = lean_string_utf8_extract(v_str_22_, v_startPos_23_, v_stopPos_24_);
lean_dec(v_stopPos_24_);
lean_dec(v_startPos_23_);
lean_dec_ref(v_str_22_);
v___x_36_ = l_String_quote(v___x_35_);
v___x_37_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_37_, 0, v___x_36_);
v___x_38_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_34_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
return v___x_38_;
}
case 1:
{
uint8_t v_canonical_39_; 
v_canonical_39_ = lean_ctor_get_uint8(v_info_8_, sizeof(void*)*2);
if (v_canonical_39_ == 0)
{
lean_object* v_pos_40_; lean_object* v_endPos_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v_pos_40_ = lean_ctor_get(v_info_8_, 0);
lean_inc(v_pos_40_);
v_endPos_41_ = lean_ctor_get(v_info_8_, 1);
lean_inc(v_endPos_41_);
lean_dec_ref_known(v_info_8_, 2);
v___x_42_ = l_Nat_reprFast(v_pos_40_);
v___x_43_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
v___x_44_ = ((lean_object*)(l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1));
v___x_45_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_45_, 0, v___x_43_);
lean_ctor_set(v___x_45_, 1, v___x_44_);
v___x_46_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_45_);
lean_ctor_set(v___x_46_, 1, v_f_9_);
v___x_47_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_44_);
v___x_48_ = l_Nat_reprFast(v_endPos_41_);
v___x_49_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
v___x_50_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_50_, 0, v___x_47_);
lean_ctor_set(v___x_50_, 1, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_pos_51_; lean_object* v_endPos_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_pos_51_ = lean_ctor_get(v_info_8_, 0);
lean_inc(v_pos_51_);
v_endPos_52_ = lean_ctor_get(v_info_8_, 1);
lean_inc(v_endPos_52_);
lean_dec_ref_known(v_info_8_, 2);
v___x_53_ = l_Nat_reprFast(v_pos_51_);
v___x_54_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
v___x_55_ = ((lean_object*)(l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__3));
v___x_56_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_56_, 0, v___x_54_);
lean_ctor_set(v___x_56_, 1, v___x_55_);
v___x_57_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v_f_9_);
v___x_58_ = ((lean_object*)(l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___closed__1));
v___x_59_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_57_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = l_Nat_reprFast(v_endPos_52_);
v___x_61_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_59_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
return v___x_62_;
}
}
default: 
{
lean_dec(v_info_8_);
return v_f_9_;
}
}
}
else
{
lean_dec(v_info_8_);
return v_f_9_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo_0interp(lean_interpreter_value* stack)
{
uint8_t v_showInfo_7_ = stack[0].m_num;
lean_object* v_info_8_ = stack[1].m_obj;
lean_object* v_f_9_ = stack[2].m_obj;
lean_object* v_res_63_;
v_res_63_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(v_showInfo_7_, v_info_8_, v_f_9_);
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo___boxed(lean_object* v_showInfo_64_, lean_object* v_info_65_, lean_object* v_f_66_){
_start:
{
uint8_t v_showInfo_boxed_67_; lean_object* v_res_68_; 
v_showInfo_boxed_67_ = lean_unbox(v_showInfo_64_);
v_res_68_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(v_showInfo_boxed_67_, v_info_65_, v_f_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Syntax_formatStxAux_spec__0(lean_object* v_a_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_nat_to_int(v_a_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2_spec__2(lean_object* v_x_71_, lean_object* v_x_72_, lean_object* v_x_73_){
_start:
{
if (lean_obj_tag(v_x_73_) == 0)
{
lean_dec(v_x_71_);
return v_x_72_;
}
else
{
lean_object* v_head_74_; lean_object* v_tail_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_84_; 
v_head_74_ = lean_ctor_get(v_x_73_, 0);
v_tail_75_ = lean_ctor_get(v_x_73_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_x_73_);
if (v_isSharedCheck_84_ == 0)
{
v___x_77_ = v_x_73_;
v_isShared_78_ = v_isSharedCheck_84_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_tail_75_);
lean_inc(v_head_74_);
lean_dec(v_x_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_84_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_80_; 
lean_inc(v_x_71_);
if (v_isShared_78_ == 0)
{
lean_ctor_set_tag(v___x_77_, 5);
lean_ctor_set(v___x_77_, 1, v_x_71_);
lean_ctor_set(v___x_77_, 0, v_x_72_);
v___x_80_ = v___x_77_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_x_72_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_x_71_);
v___x_80_ = v_reuseFailAlloc_83_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; 
v___x_81_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_head_74_);
v_x_72_ = v___x_81_;
v_x_73_ = v_tail_75_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
lean_object* v___x_87_; 
lean_dec(v_x_86_);
v___x_87_ = lean_box(0);
return v___x_87_;
}
else
{
lean_object* v_tail_88_; 
v_tail_88_ = lean_ctor_get(v_x_85_, 1);
if (lean_obj_tag(v_tail_88_) == 0)
{
lean_object* v_head_89_; 
lean_dec(v_x_86_);
v_head_89_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_head_89_);
lean_dec_ref_known(v_x_85_, 2);
return v_head_89_;
}
else
{
lean_object* v_head_90_; lean_object* v___x_91_; 
lean_inc(v_tail_88_);
v_head_90_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_head_90_);
lean_dec_ref_known(v_x_85_, 2);
v___x_91_ = l_List_foldl___at___00Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2_spec__2(v_x_86_, v_head_90_, v_tail_88_);
return v___x_91_;
}
}
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__2(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__0));
v___x_94_ = lean_string_length(v___x_93_);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__3(void){
_start:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = lean_obj_once(&l_Lean_Syntax_formatStxAux___closed__2, &l_Lean_Syntax_formatStxAux___closed__2_once, _init_l_Lean_Syntax_formatStxAux___closed__2);
v___x_96_ = lean_nat_to_int(v___x_95_);
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__17(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__15));
v___x_118_ = lean_string_length(v___x_117_);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Syntax_formatStxAux___closed__18(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = lean_obj_once(&l_Lean_Syntax_formatStxAux___closed__17, &l_Lean_Syntax_formatStxAux___closed__17_once, _init_l_Lean_Syntax_formatStxAux___closed__17);
v___x_120_ = lean_nat_to_int(v___x_119_);
return v___x_120_;
}
}
lean_object* l_Lean_Syntax_formatStxAux(lean_object* v_maxDepth_132_, uint8_t v_showInfo_133_, lean_object* v_depth_134_, lean_object* v_x_135_){
_start:
{
lean_object* v___y_137_; 
switch(lean_obj_tag(v_x_135_))
{
case 0:
{
lean_object* v___x_146_; 
lean_dec(v_maxDepth_132_);
v___x_146_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__7));
return v___x_146_;
}
case 1:
{
lean_object* v_info_147_; lean_object* v_kind_148_; lean_object* v_args_149_; lean_object* v___x_150_; lean_object* v_depth_151_; lean_object* v___y_159_; lean_object* v___x_162_; uint8_t v___x_163_; 
v_info_147_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_info_147_);
v_kind_148_ = lean_ctor_get(v_x_135_, 1);
lean_inc(v_kind_148_);
v_args_149_ = lean_ctor_get(v_x_135_, 2);
lean_inc_ref(v_args_149_);
lean_dec_ref_known(v_x_135_, 3);
v___x_150_ = lean_unsigned_to_nat(1u);
v_depth_151_ = lean_nat_add(v_depth_134_, v___x_150_);
v___x_162_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__11));
v___x_163_ = lean_name_eq(v_kind_148_, v___x_162_);
if (v___x_163_ == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_shorterName_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_header_170_; lean_object* v___y_172_; uint8_t v___y_185_; lean_object* v___y_191_; lean_object* v___x_193_; lean_object* v___x_194_; uint8_t v___x_195_; 
v___x_164_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__14));
v___x_165_ = lean_box(0);
v_shorterName_166_ = l_Lean_Name_replacePrefix(v_kind_148_, v___x_164_, v___x_165_);
v___x_167_ = 1;
v___x_168_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_shorterName_166_, v___x_167_);
v___x_169_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
v_header_170_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(v_showInfo_133_, v_info_147_, v___x_169_);
v___x_193_ = lean_unsigned_to_nat(0u);
v___x_194_ = lean_array_get_size(v_args_149_);
v___x_195_ = lean_nat_dec_lt(v___x_193_, v___x_194_);
if (v___x_195_ == 0)
{
v___y_185_ = v___x_163_;
goto v___jp_184_;
}
else
{
if (lean_obj_tag(v_maxDepth_132_) == 0)
{
lean_inc(v_depth_151_);
v___y_191_ = v_depth_151_;
goto v___jp_190_;
}
else
{
lean_object* v_val_196_; 
v_val_196_ = lean_ctor_get(v_maxDepth_132_, 0);
lean_inc(v_val_196_);
v___y_191_ = v_val_196_;
goto v___jp_190_;
}
}
v___jp_171_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; uint8_t v___x_182_; lean_object* v___x_183_; 
v___x_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_173_, 0, v_header_170_);
lean_ctor_set(v___x_173_, 1, v___y_172_);
v___x_174_ = lean_box(1);
v___x_175_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(v___x_173_, v___x_174_);
v___x_176_ = lean_obj_once(&l_Lean_Syntax_formatStxAux___closed__18, &l_Lean_Syntax_formatStxAux___closed__18_once, _init_l_Lean_Syntax_formatStxAux___closed__18);
v___x_177_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__19));
v___x_178_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_175_);
v___x_179_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__20));
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_178_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
v___x_181_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_176_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = 0;
v___x_183_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set_uint8(v___x_183_, sizeof(void*)*1, v___x_182_);
return v___x_183_;
}
v___jp_184_:
{
if (v___y_185_ == 0)
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_186_ = lean_array_to_list(v_args_149_);
v___x_187_ = lean_box(0);
v___x_188_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(v_maxDepth_132_, v_showInfo_133_, v_depth_151_, v___x_186_, v___x_187_);
lean_dec(v_depth_151_);
v___y_172_ = v___x_188_;
goto v___jp_171_;
}
else
{
lean_object* v___x_189_; 
lean_dec(v_depth_151_);
lean_dec_ref(v_args_149_);
lean_dec(v_maxDepth_132_);
v___x_189_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__21));
v___y_172_ = v___x_189_;
goto v___jp_171_;
}
}
v___jp_190_:
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_lt(v___y_191_, v_depth_151_);
lean_dec(v___y_191_);
v___y_185_ = v___x_192_;
goto v___jp_184_;
}
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
lean_dec(v_kind_148_);
lean_dec(v_info_147_);
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = lean_array_get_size(v_args_149_);
v___x_199_ = lean_nat_dec_lt(v___x_197_, v___x_198_);
if (v___x_199_ == 0)
{
goto v___jp_152_;
}
else
{
if (lean_obj_tag(v_maxDepth_132_) == 0)
{
lean_inc(v_depth_151_);
v___y_159_ = v_depth_151_;
goto v___jp_158_;
}
else
{
lean_object* v_val_200_; 
v_val_200_ = lean_ctor_get(v_maxDepth_132_, 0);
lean_inc(v_val_200_);
v___y_159_ = v_val_200_;
goto v___jp_158_;
}
}
}
v___jp_152_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = lean_array_to_list(v_args_149_);
v___x_154_ = lean_box(0);
v___x_155_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(v_maxDepth_132_, v_showInfo_133_, v_depth_151_, v___x_153_, v___x_154_);
lean_dec(v_depth_151_);
v___x_156_ = lean_box(1);
v___x_157_ = l_Std_Format_joinSep___at___00Lean_Syntax_formatStxAux_spec__2(v___x_155_, v___x_156_);
v___y_137_ = v___x_157_;
goto v___jp_136_;
}
v___jp_158_:
{
uint8_t v___x_160_; 
v___x_160_ = lean_nat_dec_lt(v___y_159_, v_depth_151_);
lean_dec(v___y_159_);
if (v___x_160_ == 0)
{
goto v___jp_152_;
}
else
{
lean_object* v___x_161_; 
lean_dec(v_depth_151_);
lean_dec_ref(v_args_149_);
lean_dec(v_maxDepth_132_);
v___x_161_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__9));
v___y_137_ = v___x_161_;
goto v___jp_136_;
}
}
}
case 2:
{
lean_object* v_info_201_; lean_object* v_val_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v_maxDepth_132_);
v_info_201_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_info_201_);
v_val_202_ = lean_ctor_get(v_x_135_, 1);
lean_inc_ref(v_val_202_);
lean_dec_ref_known(v_x_135_, 2);
v___x_203_ = l_String_quote(v_val_202_);
v___x_204_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
v___x_205_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(v_showInfo_133_, v_info_201_, v___x_204_);
return v___x_205_;
}
default: 
{
lean_object* v_info_206_; lean_object* v_val_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_maxDepth_132_);
v_info_206_ = lean_ctor_get(v_x_135_, 0);
lean_inc(v_info_206_);
v_val_207_ = lean_ctor_get(v_x_135_, 2);
lean_inc(v_val_207_);
lean_dec_ref_known(v_x_135_, 4);
v___x_208_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__23));
v___x_209_ = 1;
v___x_210_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_val_207_, v___x_209_);
v___x_211_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
v___x_212_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_208_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = l___private_Init_Data_Format_Syntax_0__Lean_Syntax_formatInfo(v_showInfo_133_, v_info_206_, v___x_212_);
return v___x_213_;
}
}
v___jp_136_:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; 
v___x_138_ = lean_obj_once(&l_Lean_Syntax_formatStxAux___closed__3, &l_Lean_Syntax_formatStxAux___closed__3_once, _init_l_Lean_Syntax_formatStxAux___closed__3);
v___x_139_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__4));
v___x_140_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___y_137_);
v___x_141_ = ((lean_object*)(l_Lean_Syntax_formatStxAux___closed__5));
v___x_142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_140_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_138_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = 0;
v___x_145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set_uint8(v___x_145_, sizeof(void*)*1, v___x_144_);
return v___x_145_;
}
}
}
LEAN_EXPORT void l_Lean_Syntax_formatStxAux_0interp(lean_interpreter_value* stack)
{
lean_object* v_maxDepth_132_ = stack[0].m_obj;
uint8_t v_showInfo_133_ = stack[1].m_num;
lean_object* v_depth_134_ = stack[2].m_obj;
lean_object* v_x_135_ = stack[3].m_obj;
lean_object* v_res_214_;
v_res_214_ = l_Lean_Syntax_formatStxAux(v_maxDepth_132_, v_showInfo_133_, v_depth_134_, v_x_135_);
stack->m_obj
 = v_res_214_;
}
lean_object* l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(lean_object* v_maxDepth_215_, uint8_t v_showInfo_216_, lean_object* v_depth_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
if (lean_obj_tag(v_a_218_) == 0)
{
lean_object* v___x_220_; 
lean_dec(v_maxDepth_215_);
v___x_220_ = l_List_reverse___redArg(v_a_219_);
return v___x_220_;
}
else
{
lean_object* v_head_221_; lean_object* v_tail_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_231_; 
v_head_221_ = lean_ctor_get(v_a_218_, 0);
v_tail_222_ = lean_ctor_get(v_a_218_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v_a_218_);
if (v_isSharedCheck_231_ == 0)
{
v___x_224_ = v_a_218_;
v_isShared_225_ = v_isSharedCheck_231_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_tail_222_);
lean_inc(v_head_221_);
lean_dec(v_a_218_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_231_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; lean_object* v___x_228_; 
lean_inc(v_maxDepth_215_);
v___x_226_ = l_Lean_Syntax_formatStxAux(v_maxDepth_215_, v_showInfo_216_, v_depth_217_, v_head_221_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_a_219_);
lean_ctor_set(v___x_224_, 0, v___x_226_);
v___x_228_ = v___x_224_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_a_219_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
v_a_218_ = v_tail_222_;
v_a_219_ = v___x_228_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_maxDepth_215_ = stack[0].m_obj;
uint8_t v_showInfo_216_ = stack[1].m_num;
lean_object* v_depth_217_ = stack[2].m_obj;
lean_object* v_a_218_ = stack[3].m_obj;
lean_object* v_a_219_ = stack[4].m_obj;
lean_object* v_res_232_;
v_res_232_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(v_maxDepth_215_, v_showInfo_216_, v_depth_217_, v_a_218_, v_a_219_);
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1___boxed(lean_object* v_maxDepth_233_, lean_object* v_showInfo_234_, lean_object* v_depth_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
uint8_t v_showInfo_boxed_238_; lean_object* v_res_239_; 
v_showInfo_boxed_238_ = lean_unbox(v_showInfo_234_);
v_res_239_ = l_List_mapTR_loop___at___00Lean_Syntax_formatStxAux_spec__1(v_maxDepth_233_, v_showInfo_boxed_238_, v_depth_235_, v_a_236_, v_a_237_);
lean_dec(v_depth_235_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStxAux___boxed(lean_object* v_maxDepth_240_, lean_object* v_showInfo_241_, lean_object* v_depth_242_, lean_object* v_x_243_){
_start:
{
uint8_t v_showInfo_boxed_244_; lean_object* v_res_245_; 
v_showInfo_boxed_244_ = lean_unbox(v_showInfo_241_);
v_res_245_ = l_Lean_Syntax_formatStxAux(v_maxDepth_240_, v_showInfo_boxed_244_, v_depth_242_, v_x_243_);
lean_dec(v_depth_242_);
return v_res_245_;
}
}
lean_object* l_Lean_Syntax_formatStx(lean_object* v_stx_246_, lean_object* v_maxDepth_247_, uint8_t v_showInfo_248_){
_start:
{
lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_249_ = lean_unsigned_to_nat(0u);
v___x_250_ = l_Lean_Syntax_formatStxAux(v_maxDepth_247_, v_showInfo_248_, v___x_249_, v_stx_246_);
return v___x_250_;
}
}
LEAN_EXPORT void l_Lean_Syntax_formatStx_0interp(lean_interpreter_value* stack)
{
lean_object* v_stx_246_ = stack[0].m_obj;
lean_object* v_maxDepth_247_ = stack[1].m_obj;
uint8_t v_showInfo_248_ = stack[2].m_num;
lean_object* v_res_251_;
v_res_251_ = l_Lean_Syntax_formatStx(v_stx_246_, v_maxDepth_247_, v_showInfo_248_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_formatStx___boxed(lean_object* v_stx_252_, lean_object* v_maxDepth_253_, lean_object* v_showInfo_254_){
_start:
{
uint8_t v_showInfo_boxed_255_; lean_object* v_res_256_; 
v_showInfo_boxed_255_ = lean_unbox(v_showInfo_254_);
v_res_256_ = l_Lean_Syntax_formatStx(v_stx_252_, v_maxDepth_253_, v_showInfo_boxed_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormat___lam__0(lean_object* v_stx_257_){
_start:
{
lean_object* v___x_258_; uint8_t v___x_259_; lean_object* v___x_260_; 
v___x_258_ = lean_box(0);
v___x_259_ = 0;
v___x_260_ = l_Lean_Syntax_formatStx(v_stx_257_, v___x_258_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToString___lam__0(lean_object* v_f_263_){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = l_Std_Format_defWidth;
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = l_Std_Format_pretty(v_f_263_, v___x_264_, v___x_265_, v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___redArg___lam__0(lean_object* v_x_272_){
_start:
{
lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; 
v___x_273_ = lean_box(0);
v___x_274_ = 0;
v___x_275_ = l_Lean_Syntax_formatStx(v_x_272_, v___x_273_, v___x_274_);
return v___x_275_;
}
}
lean_object* l_Lean_Syntax_instToFormatTSyntax___redArg(){
_start:
{
lean_object* v___f_278_; 
v___f_278_ = ((lean_object*)(l_Lean_Syntax_instToFormatTSyntax___redArg___closed__0));
return v___f_278_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instToFormatTSyntax___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_279_;
v_res_279_ = l_Lean_Syntax_instToFormatTSyntax___redArg();
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___redArg___boxed(lean_object* v___dummy_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Syntax_instToFormatTSyntax___redArg();
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax(lean_object* v_k_282_){
_start:
{
lean_object* v___f_283_; 
v___f_283_ = ((lean_object*)(l_Lean_Syntax_instToFormatTSyntax___redArg___closed__0));
return v___f_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToFormatTSyntax___boxed(lean_object* v_k_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_Syntax_instToFormatTSyntax(v_k_284_);
lean_dec(v_k_284_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___redArg___lam__0(lean_object* v_x_286_){
_start:
{
lean_object* v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_287_ = lean_box(0);
v___x_288_ = 0;
v___x_289_ = l_Lean_Syntax_formatStx(v_x_286_, v___x_287_, v___x_288_);
v___x_290_ = l_Std_Format_defWidth;
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = l_Std_Format_pretty(v___x_289_, v___x_290_, v___x_291_, v___x_291_);
return v___x_292_;
}
}
lean_object* l_Lean_Syntax_instToStringTSyntax___redArg(){
_start:
{
lean_object* v___f_295_; 
v___f_295_ = ((lean_object*)(l_Lean_Syntax_instToStringTSyntax___redArg___closed__0));
return v___f_295_;
}
}
LEAN_EXPORT void l_Lean_Syntax_instToStringTSyntax___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_296_;
v_res_296_ = l_Lean_Syntax_instToStringTSyntax___redArg();
stack->m_obj
 = v_res_296_;
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___redArg___boxed(lean_object* v___dummy_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Lean_Syntax_instToStringTSyntax___redArg();
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax(lean_object* v_k_299_){
_start:
{
lean_object* v___f_300_; 
v___f_300_ = ((lean_object*)(l_Lean_Syntax_instToStringTSyntax___redArg___closed__0));
return v___f_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Syntax_instToStringTSyntax___boxed(lean_object* v_k_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Syntax_instToStringTSyntax(v_k_301_);
lean_dec(v_k_301_);
return v_res_302_;
}
}
lean_object* runtime_initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Instances(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Format_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Format_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_ToString_Name(uint8_t builtin);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Instances(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Format_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Name(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Instances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Format_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Format_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
