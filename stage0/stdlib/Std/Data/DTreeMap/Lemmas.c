// Lean compiler output
// Module: Std.Data.DTreeMap.Lemmas
// Imports: import Std.Data.DTreeMap.Internal.Lemmas public import Std.Data.DTreeMap.AdditionalOperations public import Init.Data.Array.Perm public import Std.Internal.ForIn.Basic import Init.Data.List.Pairwise import Init.Data.Prod
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__3___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__3___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__3(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__2 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__3 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_0),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_1),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__4 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__4_value;
static const lean_array_object l_Std_DTreeMap_isSetoid___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__5 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__5_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__6 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_0),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_1),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__7_value_aux_2),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__7 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__7_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__8 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__9 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__9_value;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__10 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__10_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_0),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_1),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__11_value_aux_2),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__11 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__11_value;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__12;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__13;
static const lean_string_object l_Std_DTreeMap_isSetoid___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "compare"};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__14 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__14_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(7) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__15 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__15_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(109, 41, 149, 169, 79, 76, 232, 231)}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__16 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__16_value;
static const lean_ctor_object l_Std_DTreeMap_isSetoid___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__15_value),((lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__17 = (const lean_object*)&l_Std_DTreeMap_isSetoid___auto__1___closed__17_value;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__18;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__19;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__20;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__21;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__22;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__23;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__24;
static lean_once_cell_t l_Std_DTreeMap_isSetoid___auto__1___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_isSetoid___auto__1___closed__25;
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid___auto__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_instCoeTypeForall__3___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_instCoeTypeForall__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Std_DTreeMap_instCoeTypeForall__3___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__3___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_DTreeMap_instCoeTypeForall__3___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_instCoeTypeForall__3(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
lean_object* l_Std_DTreeMap_Equiv_instTrans___redArg(){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Equiv_instTrans___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_10_;
v_res_10_ = l_Std_DTreeMap_Equiv_instTrans___redArg();
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans___redArg___boxed(lean_object* v___dummy_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_DTreeMap_Equiv_instTrans___redArg();
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_cmp_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(0);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Equiv_instTrans___boxed(lean_object* v_00_u03b1_17_, lean_object* v_00_u03b2_18_, lean_object* v_cmp_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_DTreeMap_Equiv_instTrans(v_00_u03b1_17_, v_00_u03b2_18_, v_cmp_19_);
lean_dec_ref(v_cmp_19_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter___redArg(lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; 
lean_dec(v_h__1_22_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_apply_1(v_h__2_23_, v___x_24_);
return v___x_25_;
}
else
{
lean_object* v_val_26_; lean_object* v___x_27_; 
lean_dec(v_h__2_23_);
v_val_26_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_val_26_);
lean_dec_ref_known(v_x_21_, 1);
v___x_27_ = lean_apply_1(v_h__1_22_, v_val_26_);
return v___x_27_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Lemmas_0__Break_runK_match__1_splitter(lean_object* v_00_u03b1_28_, lean_object* v_motive_29_, lean_object* v_x_30_, lean_object* v_h__1_31_, lean_object* v_h__2_32_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; 
lean_dec(v_h__1_31_);
v___x_33_ = lean_box(0);
v___x_34_ = lean_apply_1(v_h__2_32_, v___x_33_);
return v___x_34_;
}
else
{
lean_object* v_val_35_; lean_object* v___x_36_; 
lean_dec(v_h__2_32_);
v_val_35_ = lean_ctor_get(v_x_30_, 0);
lean_inc(v_val_35_);
lean_dec_ref_known(v_x_30_, 1);
v___x_36_ = lean_apply_1(v_h__1_31_, v_val_35_);
return v___x_36_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__12(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; 
v___x_63_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__10));
v___x_64_ = l_Lean_mkAtom(v___x_63_);
return v___x_64_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__13(void){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__12, &l_Std_DTreeMap_isSetoid___auto__1___closed__12_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__12);
v___x_66_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__5));
v___x_67_ = lean_array_push(v___x_66_, v___x_65_);
return v___x_67_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__18(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_80_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__17));
v___x_81_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__13, &l_Std_DTreeMap_isSetoid___auto__1___closed__13_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__13);
v___x_82_ = lean_array_push(v___x_81_, v___x_80_);
return v___x_82_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__19(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_83_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__18, &l_Std_DTreeMap_isSetoid___auto__1___closed__18_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__18);
v___x_84_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__11));
v___x_85_ = lean_box(2);
v___x_86_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_83_);
return v___x_86_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__20(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__19, &l_Std_DTreeMap_isSetoid___auto__1___closed__19_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__19);
v___x_88_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__5));
v___x_89_ = lean_array_push(v___x_88_, v___x_87_);
return v___x_89_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__21(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_90_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__20, &l_Std_DTreeMap_isSetoid___auto__1___closed__20_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__20);
v___x_91_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__9));
v___x_92_ = lean_box(2);
v___x_93_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_90_);
return v___x_93_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__22(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_94_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__21, &l_Std_DTreeMap_isSetoid___auto__1___closed__21_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__21);
v___x_95_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__5));
v___x_96_ = lean_array_push(v___x_95_, v___x_94_);
return v___x_96_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__23(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__22, &l_Std_DTreeMap_isSetoid___auto__1___closed__22_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__22);
v___x_98_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__7));
v___x_99_ = lean_box(2);
v___x_100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v___x_98_);
lean_ctor_set(v___x_100_, 2, v___x_97_);
return v___x_100_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__24(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_101_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__23, &l_Std_DTreeMap_isSetoid___auto__1___closed__23_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__23);
v___x_102_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__5));
v___x_103_ = lean_array_push(v___x_102_, v___x_101_);
return v___x_103_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1___closed__25(void){
_start:
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__24, &l_Std_DTreeMap_isSetoid___auto__1___closed__24_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__24);
v___x_105_ = ((lean_object*)(l_Std_DTreeMap_isSetoid___auto__1___closed__4));
v___x_106_ = lean_box(2);
v___x_107_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
lean_ctor_set(v___x_107_, 2, v___x_104_);
return v___x_107_;
}
}
static lean_object* _init_l_Std_DTreeMap_isSetoid___auto__1(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Std_DTreeMap_isSetoid___auto__1___closed__25, &l_Std_DTreeMap_isSetoid___auto__1___closed__25_once, _init_l_Std_DTreeMap_isSetoid___auto__1___closed__25);
return v___x_108_;
}
}
lean_object* l_Std_DTreeMap_isSetoid___redArg(){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = lean_box(0);
return v___x_110_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_isSetoid___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_111_;
v_res_111_ = l_Std_DTreeMap_isSetoid___redArg();
stack->m_obj
 = v_res_111_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid___redArg___boxed(lean_object* v___dummy_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Std_DTreeMap_isSetoid___redArg();
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid(lean_object* v_00_u03b1_114_, lean_object* v_00_u03b2_115_, lean_object* v_cmp_116_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = lean_box(0);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_isSetoid___boxed(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_cmp_120_){
_start:
{
lean_object* v_res_121_; 
v_res_121_ = l_Std_DTreeMap_isSetoid(v_00_u03b1_118_, v_00_u03b2_119_, v_cmp_120_);
lean_dec_ref(v_cmp_120_);
return v_res_121_;
}
}
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Perm(uint8_t builtin);
lean_object* runtime_initialize_Std_Internal_ForIn_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Prod(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Internal_ForIn_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Std_DTreeMap_isSetoid___auto__1 = _init_l_Std_DTreeMap_isSetoid___auto__1();
lean_mark_persistent(l_Std_DTreeMap_isSetoid___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DTreeMap_Internal_Lemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_AdditionalOperations(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Perm(uint8_t builtin);
lean_object* initialize_Std_Internal_ForIn_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin);
lean_object* initialize_Init_Data_Prod(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DTreeMap_Internal_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_AdditionalOperations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Perm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_ForIn_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
