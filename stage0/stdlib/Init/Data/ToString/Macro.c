// Lean compiler output
// Module: Init.Data.ToString.Macro
// Imports: public meta import Init.Meta public import Init.Notation
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_expandInterpolatedStr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_termS_x21___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "termS!_"};
static const lean_object* l_termS_x21___00__closed__0 = (const lean_object*)&l_termS_x21___00__closed__0_value;
static const lean_ctor_object l_termS_x21___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termS_x21___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 130, 93, 49, 63, 146, 201, 153)}};
static const lean_object* l_termS_x21___00__closed__1 = (const lean_object*)&l_termS_x21___00__closed__1_value;
static const lean_string_object l_termS_x21___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_termS_x21___00__closed__2 = (const lean_object*)&l_termS_x21___00__closed__2_value;
static const lean_ctor_object l_termS_x21___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termS_x21___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_termS_x21___00__closed__3 = (const lean_object*)&l_termS_x21___00__closed__3_value;
static const lean_string_object l_termS_x21___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "s!"};
static const lean_object* l_termS_x21___00__closed__4 = (const lean_object*)&l_termS_x21___00__closed__4_value;
static const lean_ctor_object l_termS_x21___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_termS_x21___00__closed__4_value)}};
static const lean_object* l_termS_x21___00__closed__5 = (const lean_object*)&l_termS_x21___00__closed__5_value;
static const lean_string_object l_termS_x21___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "interpolatedStr"};
static const lean_object* l_termS_x21___00__closed__6 = (const lean_object*)&l_termS_x21___00__closed__6_value;
static const lean_ctor_object l_termS_x21___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termS_x21___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(156, 58, 177, 246, 99, 11, 16, 252)}};
static const lean_object* l_termS_x21___00__closed__7 = (const lean_object*)&l_termS_x21___00__closed__7_value;
static const lean_string_object l_termS_x21___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_termS_x21___00__closed__8 = (const lean_object*)&l_termS_x21___00__closed__8_value;
static const lean_ctor_object l_termS_x21___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_termS_x21___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_termS_x21___00__closed__9 = (const lean_object*)&l_termS_x21___00__closed__9_value;
static const lean_ctor_object l_termS_x21___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_termS_x21___00__closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_termS_x21___00__closed__10 = (const lean_object*)&l_termS_x21___00__closed__10_value;
static const lean_ctor_object l_termS_x21___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_termS_x21___00__closed__7_value),((lean_object*)&l_termS_x21___00__closed__10_value)}};
static const lean_object* l_termS_x21___00__closed__11 = (const lean_object*)&l_termS_x21___00__closed__11_value;
static const lean_ctor_object l_termS_x21___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_termS_x21___00__closed__3_value),((lean_object*)&l_termS_x21___00__closed__5_value),((lean_object*)&l_termS_x21___00__closed__11_value)}};
static const lean_object* l_termS_x21___00__closed__12 = (const lean_object*)&l_termS_x21___00__closed__12_value;
static const lean_ctor_object l_termS_x21___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_termS_x21___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_termS_x21___00__closed__12_value)}};
static const lean_object* l_termS_x21___00__closed__13 = (const lean_object*)&l_termS_x21___00__closed__13_value;
LEAN_EXPORT const lean_object* l_termS_x21__ = (const lean_object*)&l_termS_x21___00__closed__13_value;
static const lean_string_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1;
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__3 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2_value)}};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__4 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__5 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__3_value),((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__5_value)}};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__6 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__6_value;
static const lean_string_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toString"};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7_value;
static lean_once_cell_t l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8;
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 79, 177, 134, 210, 33, 7, 227)}};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__9 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__9_value;
static const lean_string_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ToString"};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__10 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__10_value;
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(30, 202, 174, 203, 16, 186, 159, 168)}};
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value_aux_0),((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(206, 210, 39, 124, 69, 192, 37, 107)}};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value;
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__12 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__12_value;
static const lean_ctor_object l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__13 = (const lean_object*)&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__13_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_32_ = ((lean_object*)(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__0));
v___x_33_ = l_String_toRawSubstring_x27(v___x_32_);
return v___x_33_;
}
}
static lean_object* _init_l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = ((lean_object*)(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__7));
v___x_49_ = l_String_toRawSubstring_x27(v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1(lean_object* v_x_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = ((lean_object*)(l_termS_x21___00__closed__1));
lean_inc(v_x_62_);
v___x_66_ = l_Lean_Syntax_isOfKind(v_x_62_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec_ref(v_a_63_);
lean_dec(v_x_62_);
v___x_67_ = lean_box(1);
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_a_64_);
return v___x_68_;
}
else
{
lean_object* v_quotContext_69_; lean_object* v_currMacroScope_70_; lean_object* v_ref_71_; lean_object* v___x_72_; lean_object* v_interpStr_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_quotContext_69_ = lean_ctor_get(v_a_63_, 1);
v_currMacroScope_70_ = lean_ctor_get(v_a_63_, 2);
v_ref_71_ = lean_ctor_get(v_a_63_, 5);
v___x_72_ = lean_unsigned_to_nat(1u);
v_interpStr_73_ = l_Lean_Syntax_getArg(v_x_62_, v___x_72_);
lean_dec(v_x_62_);
v___x_74_ = 0;
v___x_75_ = l_Lean_SourceInfo_fromRef(v_ref_71_, v___x_74_);
v___x_76_ = lean_obj_once(&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1, &l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1_once, _init_l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__1);
v___x_77_ = ((lean_object*)(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__2));
lean_inc(v_currMacroScope_70_);
lean_inc(v_quotContext_69_);
v___x_78_ = l_Lean_addMacroScope(v_quotContext_69_, v___x_77_, v_currMacroScope_70_);
v___x_79_ = ((lean_object*)(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__6));
lean_inc(v___x_75_);
v___x_80_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_80_, 0, v___x_75_);
lean_ctor_set(v___x_80_, 1, v___x_76_);
lean_ctor_set(v___x_80_, 2, v___x_78_);
lean_ctor_set(v___x_80_, 3, v___x_79_);
v___x_81_ = lean_obj_once(&l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8, &l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8_once, _init_l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__8);
v___x_82_ = ((lean_object*)(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__9));
lean_inc(v_currMacroScope_70_);
lean_inc(v_quotContext_69_);
v___x_83_ = l_Lean_addMacroScope(v_quotContext_69_, v___x_82_, v_currMacroScope_70_);
v___x_84_ = ((lean_object*)(l___aux__Init__Data__ToString__Macro______macroRules__termS_x21____1___closed__13));
v___x_85_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_85_, 0, v___x_75_);
lean_ctor_set(v___x_85_, 1, v___x_81_);
lean_ctor_set(v___x_85_, 2, v___x_83_);
lean_ctor_set(v___x_85_, 3, v___x_84_);
lean_inc_ref(v___x_85_);
v___x_86_ = l_Lean_TSyntax_expandInterpolatedStr(v_interpStr_73_, v___x_80_, v___x_85_, v___x_85_, v_a_63_, v_a_64_);
lean_dec(v_interpStr_73_);
if (lean_obj_tag(v___x_86_) == 0)
{
lean_object* v_a_87_; lean_object* v_a_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_95_; 
v_a_87_ = lean_ctor_get(v___x_86_, 0);
v_a_88_ = lean_ctor_get(v___x_86_, 1);
v_isSharedCheck_95_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_95_ == 0)
{
v___x_90_ = v___x_86_;
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_a_88_);
lean_inc(v_a_87_);
lean_dec(v___x_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_95_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_93_; 
if (v_isShared_91_ == 0)
{
v___x_93_ = v___x_90_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v_a_87_);
lean_ctor_set(v_reuseFailAlloc_94_, 1, v_a_88_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v_a_96_; lean_object* v_a_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_a_96_ = lean_ctor_get(v___x_86_, 0);
v_a_97_ = lean_ctor_get(v___x_86_, 1);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_86_);
if (v_isSharedCheck_104_ == 0)
{
v___x_99_ = v___x_86_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_a_97_);
lean_inc(v_a_96_);
lean_dec(v___x_86_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_a_96_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_a_97_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
}
}
lean_object* runtime_initialize_Init_Notation(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_ToString_Macro(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Init_Meta(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_ToString_Macro(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Meta(uint8_t builtin);
lean_object* initialize_Init_Notation(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Meta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Notation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_ToString_Macro(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_ToString_Macro(builtin);
}
#ifdef __cplusplus
}
#endif
