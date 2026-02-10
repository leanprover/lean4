// Lean compiler output
// Module: Init.Data.Nat.Bitwise.Lemmas
// Imports: import all Init.Data.Nat.Bitwise.Basic public import Init.BinderPredicates public import Init.Data.Bool public import Init.Data.Nat.Log2 import Init.ByCases import Init.Data.Int.Pow import Init.Data.Nat.Lemmas import Init.Omega import Init.RCases import Init.TacticsExtra
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
static const lean_string_object l_Nat_bitwise__div__two__pow___auto__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__0 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__0_value;
static const lean_string_object l_Nat_bitwise__div__two__pow___auto__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__1 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__1_value;
static const lean_string_object l_Nat_bitwise__div__two__pow___auto__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__2 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__2_value;
static const lean_string_object l_Nat_bitwise__div__two__pow___auto__9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__3 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_0),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_1),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__4_value_aux_2),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__4 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__4_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__5;
static const lean_string_object l_Nat_bitwise__div__two__pow___auto__9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__6 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__6_value;
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_0),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_1),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__7_value_aux_2),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__7 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__7_value;
static const lean_string_object l_Nat_bitwise__div__two__pow___auto__9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__8 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__8_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__9 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__9_value;
static const lean_string_object l_Nat_bitwise__div__two__pow___auto__9___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__10 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__10_value;
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_0),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_1),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Nat_bitwise__div__two__pow___auto__9___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__11_value_aux_2),((lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__10_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__11 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__11_value;
static const lean_string_object l_Nat_bitwise__div__two__pow___auto__9___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__12 = (const lean_object*)&l_Nat_bitwise__div__two__pow___auto__9___closed__12_value;
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__13;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__14;
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__15;
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__16;
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__17;
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__18;
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__19;
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__20;
static lean_object* l_Nat_bitwise__div__two__pow___auto__9___closed__21;
LEAN_EXPORT lean_object* l_Nat_bitwise__div__two__pow___auto__9;
LEAN_EXPORT lean_object* l_Nat_bitwise__mod__two__pow___auto__9;
LEAN_EXPORT lean_object* l_Nat_bitwise__mul__two__pow___auto__9;
LEAN_EXPORT lean_object* l_Nat_shiftLeft__bitwise__distrib___auto__5;
LEAN_EXPORT lean_object* l_Nat_shiftRight__bitwise__distrib___auto__5;
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Nat_bitwise__div__two__pow___auto__9___closed__12));
x_2 = l_Lean_mkAtom(x_1);
return x_2;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__13;
x_2 = l_Nat_bitwise__div__two__pow___auto__9___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__14;
x_2 = ((lean_object*)(l_Nat_bitwise__div__two__pow___auto__9___closed__11));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__15;
x_2 = l_Nat_bitwise__div__two__pow___auto__9___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__16;
x_2 = ((lean_object*)(l_Nat_bitwise__div__two__pow___auto__9___closed__9));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__17;
x_2 = l_Nat_bitwise__div__two__pow___auto__9___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__18;
x_2 = ((lean_object*)(l_Nat_bitwise__div__two__pow___auto__9___closed__7));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__19;
x_2 = l_Nat_bitwise__div__two__pow___auto__9___closed__5;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__20;
x_2 = ((lean_object*)(l_Nat_bitwise__div__two__pow___auto__9___closed__4));
x_3 = lean_box(2);
x_4 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Nat_bitwise__div__two__pow___auto__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__21;
return x_1;
}
}
static lean_object* _init_l_Nat_bitwise__mod__two__pow___auto__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__21;
return x_1;
}
}
static lean_object* _init_l_Nat_bitwise__mul__two__pow___auto__9() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__21;
return x_1;
}
}
static lean_object* _init_l_Nat_shiftLeft__bitwise__distrib___auto__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__21;
return x_1;
}
}
static lean_object* _init_l_Nat_shiftRight__bitwise__distrib___auto__5() {
_start:
{
lean_object* x_1; 
x_1 = l_Nat_bitwise__div__two__pow___auto__9___closed__21;
return x_1;
}
}
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Nat_Bitwise_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Log2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Nat_bitwise__div__two__pow___auto__9___closed__5 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__5();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__5);
l_Nat_bitwise__div__two__pow___auto__9___closed__13 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__13();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__13);
l_Nat_bitwise__div__two__pow___auto__9___closed__14 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__14();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__14);
l_Nat_bitwise__div__two__pow___auto__9___closed__15 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__15();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__15);
l_Nat_bitwise__div__two__pow___auto__9___closed__16 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__16();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__16);
l_Nat_bitwise__div__two__pow___auto__9___closed__17 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__17();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__17);
l_Nat_bitwise__div__two__pow___auto__9___closed__18 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__18();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__18);
l_Nat_bitwise__div__two__pow___auto__9___closed__19 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__19();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__19);
l_Nat_bitwise__div__two__pow___auto__9___closed__20 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__20();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__20);
l_Nat_bitwise__div__two__pow___auto__9___closed__21 = _init_l_Nat_bitwise__div__two__pow___auto__9___closed__21();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9___closed__21);
l_Nat_bitwise__div__two__pow___auto__9 = _init_l_Nat_bitwise__div__two__pow___auto__9();
lean_mark_persistent(l_Nat_bitwise__div__two__pow___auto__9);
l_Nat_bitwise__mod__two__pow___auto__9 = _init_l_Nat_bitwise__mod__two__pow___auto__9();
lean_mark_persistent(l_Nat_bitwise__mod__two__pow___auto__9);
l_Nat_bitwise__mul__two__pow___auto__9 = _init_l_Nat_bitwise__mul__two__pow___auto__9();
lean_mark_persistent(l_Nat_bitwise__mul__two__pow___auto__9);
l_Nat_shiftLeft__bitwise__distrib___auto__5 = _init_l_Nat_shiftLeft__bitwise__distrib___auto__5();
lean_mark_persistent(l_Nat_shiftLeft__bitwise__distrib___auto__5);
l_Nat_shiftRight__bitwise__distrib___auto__5 = _init_l_Nat_shiftRight__bitwise__distrib___auto__5();
lean_mark_persistent(l_Nat_shiftRight__bitwise__distrib___auto__5);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
