// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util
// Imports: public import Lean.Meta.Tactic.Simp.Simproc
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
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__3;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__4_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__5 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__6;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_false_of_decide"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__7_value),LEAN_SCALAR_PTR_LITERAL(171, 157, 112, 124, 91, 52, 64, 56)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__9;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__10 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__10_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__11 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__12;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "True"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__13 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__13_value),LEAN_SCALAR_PTR_LITERAL(78, 21, 103, 131, 118, 13, 187, 164)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__14 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__15;
static const lean_string_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "eq_true_of_decide"};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__16 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalPropStep___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__16_value),LEAN_SCALAR_PTR_LITERAL(10, 132, 193, 70, 136, 209, 66, 149)}};
static const lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__17 = (const lean_object*)&l_Lean_Meta_Simp_evalPropStep___redArg___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalPropStep___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Simp_evalEqPropStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "eq_false"};
static const lean_object* l_Lean_Meta_Simp_evalEqPropStep___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalEqPropStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 127, 91, 199, 130, 171, 29, 27)}};
static const lean_object* l_Lean_Meta_Simp_evalEqPropStep___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalEqPropStep___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalEqPropStep___closed__2;
static const lean_string_object l_Lean_Meta_Simp_evalEqPropStep___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "eq_true"};
static const lean_object* l_Lean_Meta_Simp_evalEqPropStep___closed__3 = (const lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalEqPropStep___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__3_value),LEAN_SCALAR_PTR_LITERAL(50, 213, 255, 45, 151, 209, 83, 175)}};
static const lean_object* l_Lean_Meta_Simp_evalEqPropStep___closed__4 = (const lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalEqPropStep___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalEqPropStep___closed__5;
static const lean_string_object l_Lean_Meta_Simp_evalEqPropStep___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Simp_evalEqPropStep___closed__6 = (const lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__6_value;
static const lean_string_object l_Lean_Meta_Simp_evalEqPropStep___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "refl"};
static const lean_object* l_Lean_Meta_Simp_evalEqPropStep___closed__7 = (const lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalEqPropStep___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__6_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_Simp_evalEqPropStep___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__7_value),LEAN_SCALAR_PTR_LITERAL(72, 6, 107, 181, 0, 125, 21, 187)}};
static const lean_object* l_Lean_Meta_Simp_evalEqPropStep___closed__8 = (const lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__8_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalEqPropStep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalEqPropStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Simp_evalNePropStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalEqPropStep___closed__6_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Simp_evalNePropStep___closed__0 = (const lean_object*)&l_Lean_Meta_Simp_evalNePropStep___closed__0_value;
static const lean_string_object l_Lean_Meta_Simp_evalNePropStep___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "not_not_intro"};
static const lean_object* l_Lean_Meta_Simp_evalNePropStep___closed__1 = (const lean_object*)&l_Lean_Meta_Simp_evalNePropStep___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Simp_evalNePropStep___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Simp_evalNePropStep___closed__1_value),LEAN_SCALAR_PTR_LITERAL(141, 174, 41, 152, 198, 172, 7, 80)}};
static const lean_object* l_Lean_Meta_Simp_evalNePropStep___closed__2 = (const lean_object*)&l_Lean_Meta_Simp_evalNePropStep___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Simp_evalNePropStep___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Simp_evalNePropStep___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalNePropStep(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalNePropStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__3(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = lean_box(0);
v___x_7_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__2));
v___x_8_ = l_Lean_mkConst(v___x_7_, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6(void){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_12_ = lean_box(0);
v___x_13_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__5));
v___x_14_ = l_Lean_mkConst(v___x_13_, v___x_12_);
return v___x_14_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__9(void){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_18_ = lean_box(0);
v___x_19_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__8));
v___x_20_ = l_Lean_mkConst(v___x_19_, v___x_18_);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__12(void){
_start:
{
lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_25_ = lean_box(0);
v___x_26_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__11));
v___x_27_ = l_Lean_mkConst(v___x_26_, v___x_25_);
return v___x_27_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__14));
v___x_33_ = l_Lean_mkConst(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__18(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_box(0);
v___x_38_ = ((lean_object*)(l_Lean_Meta_Simp_evalPropStep___redArg___closed__17));
v___x_39_ = l_Lean_mkConst(v___x_38_, v___x_37_);
return v___x_39_;
}
}
lean_object* l_Lean_Meta_Simp_evalPropStep___redArg(lean_object* v_p_40_, uint8_t v_result_41_, lean_object* v_a_42_, lean_object* v_a_43_, lean_object* v_a_44_, lean_object* v_a_45_){
_start:
{
lean_object* v___x_47_; 
lean_inc_ref(v_p_40_);
v___x_47_ = l_Lean_Meta_mkDecide(v_p_40_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_47_) == 0)
{
lean_object* v_a_48_; uint8_t v___x_49_; 
v_a_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc(v_a_48_);
lean_dec_ref_known(v___x_47_, 1);
v___x_49_ = 1;
if (v_result_41_ == 0)
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__3, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__3_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__3);
v___x_51_ = l_Lean_Meta_mkEqRefl(v___x_50_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_51_) == 0)
{
lean_object* v_a_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_71_; 
v_a_52_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_71_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_71_ == 0)
{
v___x_54_ = v___x_51_;
v_isShared_55_ = v_isSharedCheck_71_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_a_52_);
lean_dec(v___x_51_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_71_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_69_; 
v___x_56_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__6, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6);
v___x_57_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__9, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__9_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__9);
v___x_58_ = l_Lean_Expr_appArg_x21(v_a_48_);
lean_dec(v_a_48_);
v___x_59_ = lean_unsigned_to_nat(3u);
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_61_ = lean_array_push(v___x_60_, v_p_40_);
v___x_62_ = lean_array_push(v___x_61_, v___x_58_);
v___x_63_ = lean_array_push(v___x_62_, v_a_52_);
v___x_64_ = l_Lean_mkAppN(v___x_57_, v___x_63_);
lean_dec_ref(v___x_63_);
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
v___x_66_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_66_, 0, v___x_56_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
lean_ctor_set_uint8(v___x_66_, sizeof(void*)*2, v___x_49_);
v___x_67_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_67_);
v___x_69_ = v___x_54_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
}
}
}
else
{
lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_79_; 
lean_dec(v_a_48_);
lean_dec_ref(v_p_40_);
v_a_72_ = lean_ctor_get(v___x_51_, 0);
v_isSharedCheck_79_ = !lean_is_exclusive(v___x_51_);
if (v_isSharedCheck_79_ == 0)
{
v___x_74_ = v___x_51_;
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_51_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_79_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_77_; 
if (v_isShared_75_ == 0)
{
v___x_77_ = v___x_74_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_a_72_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__12, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__12_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__12);
v___x_81_ = l_Lean_Meta_mkEqRefl(v___x_80_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
if (lean_obj_tag(v___x_81_) == 0)
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_101_; 
v_a_82_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_101_ == 0)
{
v___x_84_ = v___x_81_;
v_isShared_85_ = v_isSharedCheck_101_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_101_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_99_; 
v___x_86_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__15, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15);
v___x_87_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__18, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__18_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__18);
v___x_88_ = l_Lean_Expr_appArg_x21(v_a_48_);
lean_dec(v_a_48_);
v___x_89_ = lean_unsigned_to_nat(3u);
v___x_90_ = lean_mk_empty_array_with_capacity(v___x_89_);
v___x_91_ = lean_array_push(v___x_90_, v_p_40_);
v___x_92_ = lean_array_push(v___x_91_, v___x_88_);
v___x_93_ = lean_array_push(v___x_92_, v_a_82_);
v___x_94_ = l_Lean_mkAppN(v___x_87_, v___x_93_);
lean_dec_ref(v___x_93_);
v___x_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
v___x_96_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_96_, 0, v___x_86_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
lean_ctor_set_uint8(v___x_96_, sizeof(void*)*2, v___x_49_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_97_);
v___x_99_ = v___x_84_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_97_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
else
{
lean_object* v_a_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_109_; 
lean_dec(v_a_48_);
lean_dec_ref(v_p_40_);
v_a_102_ = lean_ctor_get(v___x_81_, 0);
v_isSharedCheck_109_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_109_ == 0)
{
v___x_104_ = v___x_81_;
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_a_102_);
lean_dec(v___x_81_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_109_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_107_; 
if (v_isShared_105_ == 0)
{
v___x_107_ = v___x_104_;
goto v_reusejp_106_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v_a_102_);
v___x_107_ = v_reuseFailAlloc_108_;
goto v_reusejp_106_;
}
v_reusejp_106_:
{
return v___x_107_;
}
}
}
}
}
else
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_117_; 
lean_dec_ref(v_p_40_);
v_a_110_ = lean_ctor_get(v___x_47_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_47_);
if (v_isSharedCheck_117_ == 0)
{
v___x_112_ = v___x_47_;
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_47_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_117_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_a_110_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_evalPropStep___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_40_ = stack[0].m_obj;
uint8_t v_result_41_ = stack[1].m_num;
lean_object* v_a_42_ = stack[2].m_obj;
lean_object* v_a_43_ = stack[3].m_obj;
lean_object* v_a_44_ = stack[4].m_obj;
lean_object* v_a_45_ = stack[5].m_obj;
lean_object* v_res_118_;
v_res_118_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_p_40_, v_result_41_, v_a_42_, v_a_43_, v_a_44_, v_a_45_);
stack->m_obj
 = v_res_118_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___redArg___boxed(lean_object* v_p_119_, lean_object* v_result_120_, lean_object* v_a_121_, lean_object* v_a_122_, lean_object* v_a_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
uint8_t v_result_boxed_126_; lean_object* v_res_127_; 
v_result_boxed_126_ = lean_unbox(v_result_120_);
v_res_127_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_p_119_, v_result_boxed_126_, v_a_121_, v_a_122_, v_a_123_, v_a_124_);
lean_dec(v_a_124_);
lean_dec_ref(v_a_123_);
lean_dec(v_a_122_);
lean_dec_ref(v_a_121_);
return v_res_127_;
}
}
lean_object* l_Lean_Meta_Simp_evalPropStep(lean_object* v_p_128_, uint8_t v_result_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_Lean_Meta_Simp_evalPropStep___redArg(v_p_128_, v_result_129_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
return v___x_138_;
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_evalPropStep_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_128_ = stack[0].m_obj;
uint8_t v_result_129_ = stack[1].m_num;
lean_object* v_a_130_ = stack[2].m_obj;
lean_object* v_a_131_ = stack[3].m_obj;
lean_object* v_a_132_ = stack[4].m_obj;
lean_object* v_a_133_ = stack[5].m_obj;
lean_object* v_a_134_ = stack[6].m_obj;
lean_object* v_a_135_ = stack[7].m_obj;
lean_object* v_a_136_ = stack[8].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_Lean_Meta_Simp_evalPropStep(v_p_128_, v_result_129_, v_a_130_, v_a_131_, v_a_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalPropStep___boxed(lean_object* v_p_140_, lean_object* v_result_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_){
_start:
{
uint8_t v_result_boxed_150_; lean_object* v_res_151_; 
v_result_boxed_150_ = lean_unbox(v_result_141_);
v_res_151_ = l_Lean_Meta_Simp_evalPropStep(v_p_140_, v_result_boxed_150_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_, v_a_147_, v_a_148_);
lean_dec(v_a_148_);
lean_dec_ref(v_a_147_);
lean_dec(v_a_146_);
lean_dec_ref(v_a_145_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
return v_res_151_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalEqPropStep___closed__2(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_155_ = lean_box(0);
v___x_156_ = ((lean_object*)(l_Lean_Meta_Simp_evalEqPropStep___closed__1));
v___x_157_ = l_Lean_mkConst(v___x_156_, v___x_155_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalEqPropStep___closed__5(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_161_ = lean_box(0);
v___x_162_ = ((lean_object*)(l_Lean_Meta_Simp_evalEqPropStep___closed__4));
v___x_163_ = l_Lean_mkConst(v___x_162_, v___x_161_);
return v___x_163_;
}
}
lean_object* l_Lean_Meta_Simp_evalEqPropStep(lean_object* v_e_169_, uint8_t v_eq_170_, lean_object* v_mkNeProof_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
uint8_t v___x_180_; 
v___x_180_ = 1;
if (v_eq_170_ == 0)
{
lean_object* v___x_181_; 
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc(v_a_174_);
lean_inc_ref(v_a_173_);
lean_inc(v_a_172_);
v___x_181_ = lean_apply_8(v_mkNeProof_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_, lean_box(0));
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_195_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_195_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_195_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_186_ = lean_obj_once(&l_Lean_Meta_Simp_evalEqPropStep___closed__2, &l_Lean_Meta_Simp_evalEqPropStep___closed__2_once, _init_l_Lean_Meta_Simp_evalEqPropStep___closed__2);
v___x_187_ = l_Lean_mkAppB(v___x_186_, v_e_169_, v_a_182_);
v___x_188_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__6, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6);
v___x_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
v___x_190_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*2, v___x_180_);
v___x_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_191_);
v___x_193_ = v___x_184_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v_e_169_);
v_a_196_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_181_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_181_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
else
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v_00_u03b1_207_; lean_object* v_a_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v_u_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v_proof_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
lean_dec_ref(v_mkNeProof_171_);
v___x_204_ = lean_box(0);
v___x_205_ = l_Lean_Expr_appFn_x21(v_e_169_);
v___x_206_ = l_Lean_Expr_appFn_x21(v___x_205_);
v_00_u03b1_207_ = l_Lean_Expr_appArg_x21(v___x_206_);
v_a_208_ = l_Lean_Expr_appArg_x21(v___x_205_);
lean_dec_ref(v___x_205_);
v___x_209_ = l_Lean_Expr_appFn_x21(v___x_206_);
lean_dec_ref(v___x_206_);
v___x_210_ = l_Lean_Expr_constLevels_x21(v___x_209_);
lean_dec_ref(v___x_209_);
v_u_211_ = l_List_head_x21___redArg(v___x_204_, v___x_210_);
lean_dec(v___x_210_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_obj_once(&l_Lean_Meta_Simp_evalEqPropStep___closed__5, &l_Lean_Meta_Simp_evalEqPropStep___closed__5_once, _init_l_Lean_Meta_Simp_evalEqPropStep___closed__5);
v___x_214_ = ((lean_object*)(l_Lean_Meta_Simp_evalEqPropStep___closed__8));
v___x_215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_215_, 0, v_u_211_);
lean_ctor_set(v___x_215_, 1, v___x_212_);
v___x_216_ = l_Lean_mkConst(v___x_214_, v___x_215_);
v___x_217_ = l_Lean_mkAppB(v___x_216_, v_00_u03b1_207_, v_a_208_);
v_proof_218_ = l_Lean_mkAppB(v___x_213_, v_e_169_, v___x_217_);
v___x_219_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__15, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_proof_218_);
v___x_221_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*2, v___x_180_);
v___x_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
v___x_223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_223_, 0, v___x_222_);
return v___x_223_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_evalEqPropStep_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_169_ = stack[0].m_obj;
uint8_t v_eq_170_ = stack[1].m_num;
lean_object* v_mkNeProof_171_ = stack[2].m_obj;
lean_object* v_a_172_ = stack[3].m_obj;
lean_object* v_a_173_ = stack[4].m_obj;
lean_object* v_a_174_ = stack[5].m_obj;
lean_object* v_a_175_ = stack[6].m_obj;
lean_object* v_a_176_ = stack[7].m_obj;
lean_object* v_a_177_ = stack[8].m_obj;
lean_object* v_a_178_ = stack[9].m_obj;
lean_object* v_res_224_;
v_res_224_ = l_Lean_Meta_Simp_evalEqPropStep(v_e_169_, v_eq_170_, v_mkNeProof_171_, v_a_172_, v_a_173_, v_a_174_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalEqPropStep___boxed(lean_object* v_e_225_, lean_object* v_eq_226_, lean_object* v_mkNeProof_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
uint8_t v_eq_boxed_236_; lean_object* v_res_237_; 
v_eq_boxed_236_ = lean_unbox(v_eq_226_);
v_res_237_ = l_Lean_Meta_Simp_evalEqPropStep(v_e_225_, v_eq_boxed_236_, v_mkNeProof_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
return v_res_237_;
}
}
static lean_object* _init_l_Lean_Meta_Simp_evalNePropStep___closed__3(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_box(0);
v___x_244_ = ((lean_object*)(l_Lean_Meta_Simp_evalNePropStep___closed__2));
v___x_245_ = l_Lean_mkConst(v___x_244_, v___x_243_);
return v___x_245_;
}
}
lean_object* l_Lean_Meta_Simp_evalNePropStep(lean_object* v_e_246_, uint8_t v_ne_247_, lean_object* v_mkNeProof_248_, lean_object* v_a_249_, lean_object* v_a_250_, lean_object* v_a_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_, lean_object* v_a_255_){
_start:
{
uint8_t v___x_257_; 
v___x_257_ = 1;
if (v_ne_247_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v_00_u03b1_261_; lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_u_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v_eqProp_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v_rflExpr_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v_proof_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec_ref(v_mkNeProof_248_);
v___x_258_ = lean_box(0);
v___x_259_ = l_Lean_Expr_appFn_x21(v_e_246_);
v___x_260_ = l_Lean_Expr_appFn_x21(v___x_259_);
v_00_u03b1_261_ = l_Lean_Expr_appArg_x21(v___x_260_);
v_a_262_ = l_Lean_Expr_appArg_x21(v___x_259_);
lean_dec_ref(v___x_259_);
v___x_263_ = l_Lean_Expr_appFn_x21(v___x_260_);
lean_dec_ref(v___x_260_);
v___x_264_ = l_Lean_Expr_constLevels_x21(v___x_263_);
lean_dec_ref(v___x_263_);
v_u_265_ = l_List_head_x21___redArg(v___x_258_, v___x_264_);
lean_dec(v___x_264_);
v___x_266_ = ((lean_object*)(l_Lean_Meta_Simp_evalNePropStep___closed__0));
v___x_267_ = lean_box(0);
v___x_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_268_, 0, v_u_265_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
lean_inc_ref(v___x_268_);
v___x_269_ = l_Lean_mkConst(v___x_266_, v___x_268_);
lean_inc_ref_n(v_a_262_, 2);
lean_inc_ref(v_00_u03b1_261_);
v_eqProp_270_ = l_Lean_mkApp3(v___x_269_, v_00_u03b1_261_, v_a_262_, v_a_262_);
v___x_271_ = ((lean_object*)(l_Lean_Meta_Simp_evalEqPropStep___closed__8));
v___x_272_ = l_Lean_mkConst(v___x_271_, v___x_268_);
v_rflExpr_273_ = l_Lean_mkAppB(v___x_272_, v_00_u03b1_261_, v_a_262_);
v___x_274_ = lean_obj_once(&l_Lean_Meta_Simp_evalEqPropStep___closed__2, &l_Lean_Meta_Simp_evalEqPropStep___closed__2_once, _init_l_Lean_Meta_Simp_evalEqPropStep___closed__2);
v___x_275_ = lean_obj_once(&l_Lean_Meta_Simp_evalNePropStep___closed__3, &l_Lean_Meta_Simp_evalNePropStep___closed__3_once, _init_l_Lean_Meta_Simp_evalNePropStep___closed__3);
v___x_276_ = l_Lean_mkAppB(v___x_275_, v_eqProp_270_, v_rflExpr_273_);
v_proof_277_ = l_Lean_mkAppB(v___x_274_, v_e_246_, v___x_276_);
v___x_278_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__6, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__6_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__6);
v___x_279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_279_, 0, v_proof_277_);
v___x_280_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
lean_ctor_set_uint8(v___x_280_, sizeof(void*)*2, v___x_257_);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
v___x_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
else
{
lean_object* v___x_283_; 
lean_inc(v_a_255_);
lean_inc_ref(v_a_254_);
lean_inc(v_a_253_);
lean_inc_ref(v_a_252_);
lean_inc(v_a_251_);
lean_inc_ref(v_a_250_);
lean_inc(v_a_249_);
v___x_283_ = lean_apply_8(v_mkNeProof_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_, lean_box(0));
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_a_284_; lean_object* v___x_286_; uint8_t v_isShared_287_; uint8_t v_isSharedCheck_297_; 
v_a_284_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_297_ == 0)
{
v___x_286_ = v___x_283_;
v_isShared_287_ = v_isSharedCheck_297_;
goto v_resetjp_285_;
}
else
{
lean_inc(v_a_284_);
lean_dec(v___x_283_);
v___x_286_ = lean_box(0);
v_isShared_287_ = v_isSharedCheck_297_;
goto v_resetjp_285_;
}
v_resetjp_285_:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_288_ = lean_obj_once(&l_Lean_Meta_Simp_evalEqPropStep___closed__5, &l_Lean_Meta_Simp_evalEqPropStep___closed__5_once, _init_l_Lean_Meta_Simp_evalEqPropStep___closed__5);
v___x_289_ = l_Lean_mkAppB(v___x_288_, v_e_246_, v_a_284_);
v___x_290_ = lean_obj_once(&l_Lean_Meta_Simp_evalPropStep___redArg___closed__15, &l_Lean_Meta_Simp_evalPropStep___redArg___closed__15_once, _init_l_Lean_Meta_Simp_evalPropStep___redArg___closed__15);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_289_);
v___x_292_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
lean_ctor_set_uint8(v___x_292_, sizeof(void*)*2, v___x_257_);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
if (v_isShared_287_ == 0)
{
lean_ctor_set(v___x_286_, 0, v___x_293_);
v___x_295_ = v___x_286_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_293_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec_ref(v_e_246_);
v_a_298_ = lean_ctor_get(v___x_283_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_283_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_283_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_283_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Simp_evalNePropStep_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_246_ = stack[0].m_obj;
uint8_t v_ne_247_ = stack[1].m_num;
lean_object* v_mkNeProof_248_ = stack[2].m_obj;
lean_object* v_a_249_ = stack[3].m_obj;
lean_object* v_a_250_ = stack[4].m_obj;
lean_object* v_a_251_ = stack[5].m_obj;
lean_object* v_a_252_ = stack[6].m_obj;
lean_object* v_a_253_ = stack[7].m_obj;
lean_object* v_a_254_ = stack[8].m_obj;
lean_object* v_a_255_ = stack[9].m_obj;
lean_object* v_res_306_;
v_res_306_ = l_Lean_Meta_Simp_evalNePropStep(v_e_246_, v_ne_247_, v_mkNeProof_248_, v_a_249_, v_a_250_, v_a_251_, v_a_252_, v_a_253_, v_a_254_, v_a_255_);
stack->m_obj
 = v_res_306_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_evalNePropStep___boxed(lean_object* v_e_307_, lean_object* v_ne_308_, lean_object* v_mkNeProof_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
uint8_t v_ne_boxed_318_; lean_object* v_res_319_; 
v_ne_boxed_318_ = lean_unbox(v_ne_308_);
v_res_319_ = l_Lean_Meta_Simp_evalNePropStep(v_e_307_, v_ne_boxed_318_, v_mkNeProof_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_);
lean_dec(v_a_316_);
lean_dec_ref(v_a_315_);
lean_dec(v_a_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_a_312_);
lean_dec_ref(v_a_311_);
lean_dec(v_a_310_);
return v_res_319_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Util(builtin);
}
#ifdef __cplusplus
}
#endif
