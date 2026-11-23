// Lean compiler output
// Module: Lean.Fmt.Util.Module
// Imports: public import Lean.Fmt.FmtM.Error public import Lean.Parser.Module.Syntax import Lean.Parser.Module
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
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Parser_isTerminalCommand(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static const lean_string_object l_Lean_Fmt_headerKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Fmt_headerKind___closed__0 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__0_value;
static const lean_string_object l_Lean_Fmt_headerKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Fmt_headerKind___closed__1 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__1_value;
static const lean_string_object l_Lean_Fmt_headerKind___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Module"};
static const lean_object* l_Lean_Fmt_headerKind___closed__2 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__2_value;
static const lean_string_object l_Lean_Fmt_headerKind___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Fmt_headerKind___closed__3 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__3_value;
static const lean_ctor_object l_Lean_Fmt_headerKind___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_headerKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_headerKind___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_headerKind___closed__4_value_aux_0),((lean_object*)&l_Lean_Fmt_headerKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_headerKind___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_headerKind___closed__4_value_aux_1),((lean_object*)&l_Lean_Fmt_headerKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Fmt_headerKind___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_headerKind___closed__4_value_aux_2),((lean_object*)&l_Lean_Fmt_headerKind___closed__3_value),LEAN_SCALAR_PTR_LITERAL(40, 173, 92, 3, 94, 219, 131, 202)}};
static const lean_object* l_Lean_Fmt_headerKind___closed__4 = (const lean_object*)&l_Lean_Fmt_headerKind___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_headerKind = (const lean_object*)&l_Lean_Fmt_headerKind___closed__4_value;
static const lean_string_object l_Lean_Fmt_moduleKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l_Lean_Fmt_moduleKind___closed__0 = (const lean_object*)&l_Lean_Fmt_moduleKind___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_moduleKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_headerKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_moduleKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_headerKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_moduleKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_headerKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Fmt_moduleKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_moduleKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 203, 142, 146, 93, 76, 229, 9)}};
static const lean_object* l_Lean_Fmt_moduleKind___closed__1 = (const lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_moduleKind = (const lean_object*)&l_Lean_Fmt_moduleKind___closed__1_value;
static const lean_string_object l_Lean_Fmt_cmdsKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cmds"};
static const lean_object* l_Lean_Fmt_cmdsKind___closed__0 = (const lean_object*)&l_Lean_Fmt_cmdsKind___closed__0_value;
static const lean_ctor_object l_Lean_Fmt_cmdsKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_headerKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Fmt_cmdsKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Fmt_headerKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Fmt_cmdsKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Fmt_headerKind___closed__2_value),LEAN_SCALAR_PTR_LITERAL(239, 68, 245, 129, 233, 83, 45, 77)}};
static const lean_ctor_object l_Lean_Fmt_cmdsKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Fmt_cmdsKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 195, 254, 203, 161, 113, 38, 248)}};
static const lean_object* l_Lean_Fmt_cmdsKind___closed__1 = (const lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Fmt_cmdsKind = (const lean_object*)&l_Lean_Fmt_cmdsKind___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "eoi"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Fmt_headerKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Fmt_headerKind___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(26, 206, 8, 118, 9, 188, 233, 7)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_findAbnormalTerminalCommand_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Fmt_findAbnormalTerminalCommand_x3f___boxed(lean_object*);
static const lean_string_object l_Lean_Fmt_mkModuleSyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "Cannot format file with early termination commands (e.g. `#exit`)."};
static const lean_object* l_Lean_Fmt_mkModuleSyntax___closed__0 = (const lean_object*)&l_Lean_Fmt_mkModuleSyntax___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Fmt_mkModuleSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0(lean_object* v_as_35_, size_t v_sz_36_, size_t v_i_37_, lean_object* v_b_38_){
_start:
{
lean_object* v_a_40_; uint8_t v___x_44_; 
v___x_44_ = lean_usize_dec_lt(v_i_37_, v_sz_36_);
if (v___x_44_ == 0)
{
lean_inc_ref(v_b_38_);
return v_b_38_;
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v_a_47_; uint8_t v___x_48_; 
v___x_45_ = lean_box(0);
v___x_46_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__0));
v_a_47_ = lean_array_uget_borrowed(v_as_35_, v_i_37_);
lean_inc(v_a_47_);
v___x_48_ = l_Lean_Parser_isTerminalCommand(v_a_47_);
if (v___x_48_ == 0)
{
v_a_40_ = v___x_46_;
goto v___jp_39_;
}
else
{
lean_object* v___x_49_; uint8_t v___x_50_; 
v___x_49_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__3));
lean_inc(v_a_47_);
v___x_50_ = l_Lean_Syntax_isOfKind(v_a_47_, v___x_49_);
if (v___x_50_ == 0)
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
lean_inc(v_a_47_);
v___x_51_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_51_, 0, v_a_47_);
v___x_52_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
v___x_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_45_);
return v___x_53_;
}
else
{
v_a_40_ = v___x_46_;
goto v___jp_39_;
}
}
}
v___jp_39_:
{
size_t v___x_41_; size_t v___x_42_; 
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_add(v_i_37_, v___x_41_);
v_i_37_ = v___x_42_;
v_b_38_ = v_a_40_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___boxed(lean_object* v_as_54_, lean_object* v_sz_55_, lean_object* v_i_56_, lean_object* v_b_57_){
_start:
{
size_t v_sz_boxed_58_; size_t v_i_boxed_59_; lean_object* v_res_60_; 
v_sz_boxed_58_ = lean_unbox_usize(v_sz_55_);
lean_dec(v_sz_55_);
v_i_boxed_59_ = lean_unbox_usize(v_i_56_);
lean_dec(v_i_56_);
v_res_60_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0(v_as_54_, v_sz_boxed_58_, v_i_boxed_59_, v_b_57_);
lean_dec_ref(v_b_57_);
lean_dec_ref(v_as_54_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_findAbnormalTerminalCommand_x3f(lean_object* v_stxs_61_){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; size_t v_sz_64_; size_t v___x_65_; lean_object* v___x_66_; lean_object* v_fst_67_; 
v___x_62_ = lean_box(0);
v___x_63_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0___closed__0));
v_sz_64_ = lean_array_size(v_stxs_61_);
v___x_65_ = ((size_t)0ULL);
v___x_66_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Fmt_findAbnormalTerminalCommand_x3f_spec__0(v_stxs_61_, v_sz_64_, v___x_65_, v___x_63_);
v_fst_67_ = lean_ctor_get(v___x_66_, 0);
lean_inc(v_fst_67_);
lean_dec_ref(v___x_66_);
if (lean_obj_tag(v_fst_67_) == 0)
{
return v___x_62_;
}
else
{
lean_object* v_val_68_; 
v_val_68_ = lean_ctor_get(v_fst_67_, 0);
lean_inc(v_val_68_);
lean_dec_ref_known(v_fst_67_, 1);
return v_val_68_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_findAbnormalTerminalCommand_x3f___boxed(lean_object* v_stxs_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Lean_Fmt_findAbnormalTerminalCommand_x3f(v_stxs_69_);
lean_dec_ref(v_stxs_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Fmt_mkModuleSyntax(lean_object* v_headerStx_72_, lean_object* v_cmdStxs_73_){
_start:
{
lean_object* v___x_74_; 
v___x_74_ = l_Lean_Fmt_findAbnormalTerminalCommand_x3f(v_cmdStxs_73_);
if (lean_obj_tag(v___x_74_) == 1)
{
lean_object* v_val_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_85_; 
lean_dec_ref(v_cmdStxs_73_);
lean_dec(v_headerStx_72_);
v_val_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_85_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_85_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_val_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_85_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_79_ = ((lean_object*)(l_Lean_Fmt_mkModuleSyntax___closed__0));
v___x_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_80_, 0, v_val_75_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_80_);
v___x_82_ = v___x_77_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_84_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; 
v___x_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
return v___x_83_;
}
}
}
else
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
lean_dec(v___x_74_);
v___x_86_ = ((lean_object*)(l_Lean_Fmt_moduleKind));
v___x_87_ = ((lean_object*)(l_Lean_Fmt_cmdsKind));
v___x_88_ = lean_box(2);
v___x_89_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
lean_ctor_set(v___x_89_, 1, v___x_87_);
lean_ctor_set(v___x_89_, 2, v_cmdStxs_73_);
v___x_90_ = lean_unsigned_to_nat(2u);
v___x_91_ = lean_mk_empty_array_with_capacity(v___x_90_);
v___x_92_ = lean_array_push(v___x_91_, v_headerStx_72_);
v___x_93_ = lean_array_push(v___x_92_, v___x_89_);
v___x_94_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_94_, 0, v___x_88_);
lean_ctor_set(v___x_94_, 1, v___x_86_);
lean_ctor_set(v___x_94_, 2, v___x_93_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
}
lean_object* runtime_initialize_Lean_Fmt_FmtM_Error(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser_Module(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Fmt_Util_Module(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Fmt_Util_Module(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Fmt_FmtM_Error(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module_Syntax(uint8_t builtin);
lean_object* initialize_Lean_Parser_Module(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Fmt_Util_Module(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Fmt_FmtM_Error(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Fmt_Util_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Fmt_Util_Module(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Fmt_Util_Module(builtin);
}
#ifdef __cplusplus
}
#endif
