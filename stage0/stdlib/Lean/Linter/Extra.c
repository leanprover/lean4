// Lean compiler output
// Module: Lean.Linter.Extra
// Imports: public import Lean.Linter.Extra.DupNamespace public import Lean.Linter.Extra.UnnecessarySeqFocus public import Lean.Linter.Extra.UnreachableTactic public import Lean.Linter.Extra.UnusedDecidableInType
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Linter_addBuiltinLinterSet(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "extra"};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "dupNamespace"};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(100, 70, 92, 151, 235, 189, 126, 126)}};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "unnecessarySeqFocus"};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(117, 28, 30, 68, 103, 193, 126, 138)}};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "unreachableTactic"};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__9_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(136, 56, 214, 109, 29, 26, 244, 93)}};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "unusedDecidableInType"};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(33, 183, 205, 183, 92, 15, 88, 116)}};
static const lean_ctor_object l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__12_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(126, 106, 196, 225, 81, 30, 137, 135)}};
static const lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2____boxed(lean_object*);
static lean_object* _init_l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = ((lean_object*)(l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_));
v___x_12_ = l_Lean_NameSet_empty;
v___x_13_ = l_Lean_NameSet_insert(v___x_12_, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = ((lean_object*)(l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_));
v___x_20_ = lean_obj_once(&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_);
v___x_21_ = l_Lean_NameSet_insert(v___x_20_, v___x_19_);
return v___x_21_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = ((lean_object*)(l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__10_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_));
v___x_28_ = lean_obj_once(&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_);
v___x_29_ = l_Lean_NameSet_insert(v___x_28_, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_35_ = ((lean_object*)(l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__13_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_));
v___x_36_ = lean_obj_once(&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__11_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_);
v___x_37_ = l_Lean_NameSet_insert(v___x_36_, v___x_35_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = ((lean_object*)(l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_));
v___x_40_ = lean_obj_once(&l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_, &l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2__once, _init_l___private_Lean_Linter_Extra_0__Lean_Linter_initFn___closed__14_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_);
v___x_41_ = l_Lean_Linter_addBuiltinLinterSet(v___x_39_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_Extra_0__Lean_Linter_initFn_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2____boxed(lean_object* v_a_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___private_Lean_Linter_Extra_0__Lean_Linter_initFn_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_();
return v_res_43_;
}
}
lean_object* runtime_initialize_Lean_Linter_Extra_DupNamespace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Extra_UnreachableTactic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Extra_UnusedDecidableInType(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Extra(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Linter_Extra_DupNamespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_Extra_0__Lean_Linter_initFn_00___x40_Lean_Linter_Extra_4111276407____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Extra(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Linter_Extra_DupNamespace(uint8_t builtin);
lean_object* initialize_Lean_Linter_Extra_UnnecessarySeqFocus(uint8_t builtin);
lean_object* initialize_Lean_Linter_Extra_UnreachableTactic(uint8_t builtin);
lean_object* initialize_Lean_Linter_Extra_UnusedDecidableInType(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Extra(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Linter_Extra_DupNamespace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Extra_UnnecessarySeqFocus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Extra_UnreachableTactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Extra_UnusedDecidableInType(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Extra(builtin);
}
#ifdef __cplusplus
}
#endif
